-- |This module contains our SmallCheck-esque counter example finder.
-- Ours however is based on our critical-term technique,
-- i.e. through the analysis of symbolic execution and strictness.
-- Seemed like a good idea but in practice is pretty terrible.
module Zeno.Checker ( 
  contradictory, 
  falsify, falsifiable,
  purifyConditions
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Evaluation
import Zeno.Reduction

import qualified Data.Map as Map

local2 :: MonadReader r m => (r -> r) -> ReaderT r2 m a -> ReaderT r2 m a
local2 f r = do
  m <- asks (runReaderT r)
  lift (local f m)
  
deepCritical :: ZExpr -> Maybe CriticalTerm
deepCritical = runWriterT . critical . evaluateToCase
  where
  critical :: ZExpr -> WriterT [Id] Maybe ZTerm
  critical (Cse id strict_term _) = do
    tell [id]
    critical (evaluateToCase strict_term)
  critical term
    | destructibleTerm term && isUniversalVar var = 
      lift (Just term)
    where Just var = termFunction term
  critical _ = lift Nothing
  
usableCritical :: CriticalTerm -> Bool
usableCritical (term, src) =
  not . any invalidPath . allSources $ term
  where
  invalidPath check = 
    orderedSupersetOf src check 
    && all (`elem` check) src
    
falsifiable :: (IdCounter c, MonadReader c m) => ZClause -> m Bool
falsifiable = liftM isJust . falsify

showCounterexample :: Maybe ZExprSubstitution -> String
showCounterexample Nothing = "None"

-- |Attempts to find a counter-example to a given property.
falsify :: (IdCounter c, MonadReader c m) => ZClause -> m (Maybe ZExprSubstitution)
falsify cls = do
  id <- asks largestId
  return 
    . getFirst
    . flip runReader []
    . flip runReaderT id
    . falsifyR 
    $ cls
    
type Checker a = ReaderT Id (Reader [ZEquality]) a
type Falsifier = Checker (First ZExprSubstitution)

falsifyR :: ZClause -> Falsifier
falsifyR cls = do
  stateful (reduceM cls) 
    $ \reduced_cls ->
      case reduced_cls of
        ReducedToFalse -> return . First . Just $ mempty
        ReducedTo clss -> concatMapM falsifier clss
  where
  falsifyWith :: ZClause -> ZTerm -> ZTerm -> Falsifier
  falsifyWith clause old_term new_term =
    liftM (fmap modifySubs) 
      $ falsifyR (substituteTakingSources sub clause)
    where 
    sub = Map.singleton old_term new_term
    
    modifySubs :: ZExprSubstitution -> ZExprSubstitution
    modifySubs old_sub = 
      old_sub' `Map.union` new_sub
      where
      new_sub = Map.map (substitute old_sub) sub
      old_sub' = Map.filterWithKey (\k _ -> clause `contains` k) old_sub
  
  falsifier :: ZClause -> Falsifier
  falsifier cls@(Clause goal@(lhs :=: rhs) conds)
    | not (null var_crits) = do
      let cterm@(term, _) = head var_crits
      stateful (instantiateConstructors cterm) 
        $ \cons -> concatMapM (falsifyWith cls term) (map fst cons)

    | not (null all_var_crits) = do
      let var_crit = head all_var_crits
      stateful (instantiateConstructors var_crit) $ 
        \cons -> do
          let nonrec = filter (not . recursiveConstructorInstance) cons
          concatMapM (falsifyWith cls (fst var_crit)) (map fst nonrec) 
      
    | otherwise = do
      assigned <- lift $ asks (map equalityLeft)
      let usable_app_crits = id
            . filter (not . flip elem assigned . fst) 
            $ app_crits
      if null usable_app_crits 
        then return mempty
        else do 
          let cterm@(term, _) = head usable_app_crits
          stateful (instantiateConstructors cterm) 
            $ concatMapM 
            $ \(con, _) -> local2 ([term :=: con] ++) (falsifyWith cls term con)  
    where
    all_terms = lhs : rhs : map equalityLeft conds
    usable_crits = filter usableCritical all_crits
    all_crits = mergeCriticalTerms
              $ mapMaybe deepCritical
              $ all_terms
    all_var_crits = filter (isVar . fst) all_crits
    (var_crits, app_crits) = partition (isVar . fst) usable_crits
      
-- |Searches for contradiction within a conjunction of equalities. That is to say
-- whether at least one of them will be false for any possible variable assignment. 
contradictory :: forall c m . (MonadReader c m, IdCounter c) => [ZEquality] -> m Bool
contradictory eqs = do
  id <- asks largestId
  return
    . flip runReader []
    . flip runReaderT id 
    $ contradictoryR eqs

contradictoryR :: [ZEquality] -> Checker Bool
contradictoryR eqs =
  stateful (mconcat `liftM` mapM reduceM eqs) $ \reduced_eqs -> 
    case reduced_eqs of
      ReducedToFalse -> return True
      ReducedTo [] -> return False
      ReducedTo eqs' ->
        let all_crits = id 
              . filter usableCritical
              . mergeCriticalTerms
              . mapMaybe deepCritical
              . map equalityLeft
              $ eqs'
        in case all_crits of
          [] -> return False
          cterm@(term, _) : _ ->
            stateful (instantiateConstructors cterm) 
              $ allM (splitOn eqs' term)
  where
  splitOn :: [ZEquality] -> ZTerm -> 
    (ZTerm, a) -> Checker Bool
  splitOn eqs old_term (new_term, _) 
    = contradictoryR
    $ map (substituteTakingSources sub) eqs
    where sub = Map.singleton old_term new_term

-- |Remove any unnecessary conditions using 'falsify'.
-- Unnecessary conditions are those which do not cause a clause to be 
-- falsifiable if removed.
purifyConditions :: forall c m . (IdCounter c, MonadReader c m) =>
    ZClause -> m ZClause
purifyConditions cls@(Clause eq conds) = do
  conds' <- tryRemove [] conds
  return (Clause eq conds')
  where
  tryRemove :: [ZEquality] -> [ZEquality] -> m [ZEquality]
  tryRemove needed_cs [] = return needed_cs
  tryRemove needed_cs (c:cs) = do
    needed <- falsifiable (Clause eq (needed_cs ++ cs))
    if needed
      then tryRemove (c : needed_cs) cs
      else trace ("dropped " ++ show c ++ " from " ++ show cls) $ tryRemove needed_cs cs

