-- |The Zeno automated theorem prover. 
-- Lemmas go in, proofs come out, never a miscommunication.
{-# LANGUAGE TupleSections #-}
module Zeno.Solver (
  solve, solveM
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Evaluation
import Zeno.Proof
import Zeno.Reduction
import Zeno.Checker

import qualified Zeno.Proof as Proof
import qualified Data.Set as Set
import qualified Data.Map as Map

{- 
STUFF

Convert this all to MaybeT and remove the case-of maybe code

REMEMBER the filterConditions weirdness, 
  needs to be removed, if only to shorten proofs
  
REMEMBER that reducing hypotheses loses proofs

The "==" check for adding a Proof.Sim step in solve_reduce is a bit heavy perhaps
  possibly find a way of optimizing this

Inner let structural equivalence fail?
  Probably won't happen as they will always float in.

Command line option for randomSequence vs sequence

Do things in phases?
  like after induction there is no generalisation?
  after splitting there is no induction?
  
Theory about removal of multiple linked induction hypotheses on application

Theory about only adding a hypothesis one the "first" inductive step of a chain
  that is to say do not add a hypothesis if hypotheses already exist
  
Try merging case-splitting back into induction
  
just remember to apply function definitions whilst finding critical terms
  
Try iding each case-analysis and never use case-analysis to do induction on
  a child of a variable that was created with this analysis
  
Try "hypothesis can be proven from conditions of goal using the solver"
  rather than it can directly be inferred

Should variable sources distinguish between case-split and induction generated ones? i.e. data VariableSource = CaseSplit [Id] | Induction [Id] 
  
sorted (sorted xs) === sorted xs 
  same as: sorted ys === ys :- P(ys) ... what is P??
    discovery of predicates
-}

data SolverState
  = SolverState   { sProgram :: !ZProgram,
                    sGoal :: !ZClause,
                    sHypotheses :: ![ZHypothesis] }

instance IdCounter SolverState where
  newId ss = (id, ss')
    where
    (id, pgm') = newId (sProgram ss)
    ss' = ss { sProgram = pgm' }
    
  largestId = largestId . sProgram

instance WithinTraversable ZExpr SolverState where
  mapWithinM f s = do
    goal' <- mapWithinM f (sGoal s)
    hyps' <- mapM (mapWithinM f) (sHypotheses s)
    return $ s { sGoal = goal', sHypotheses = hyps' }
    
type Solver = Reader SolverState
type StatefulSolver = State SolverState

debugSolver :: Bool
debugSolver = False

-- |Whether any have been proven.
disjoin :: [Maybe a] -> Maybe a
disjoin = listToMaybe . catMaybes

-- |Whether all have been proven.
conjoin :: [Maybe a] -> Maybe [a]
conjoin = sequence

solveM :: MonadReader ZProgram m => ZClause -> m (Maybe ZProof)
solveM cls = asks (flip solve cls)

solve :: ZProgram -> ZClause -> Maybe ZProof
solve pgm lemma =
  flip runReader (SolverState pgm lemma mempty)
    . clearGoalSources
    $ solve_all

solve_all :: Solver (Maybe ZProof)
solve_all = id 
         -- $ solve_apply
          . solve_reduce
          . traceGoal "goal"
          $ combine [ 
                   --   solve_con,
                       
                      solve_fac,
                      solve_gen,
                      solve_hyp,
                      solve_hcn,
                      solve_ind,
                      solve_cse,
                      solve_filter,
                      
                      return Nothing ]

-- |This step applies any variable assignments in the goal conditions
solve_apply :: Solver (Maybe ZProof) -> Solver (Maybe ZProof)
solve_apply next_step = do
  old_goal@(Clause _ conds) <- asks sGoal
  let new_goal = applyVarAssignments conds old_goal
  if new_goal == old_goal
    then next_step
    else do
      maybe_proof <- localGoal new_goal next_step
      mapM (proofstep . Proof.Sim) maybe_proof
  where
  applyVarAssignments :: [ZEquality] -> ZClause -> ZClause
  applyVarAssignments = foldl' apply id 
    where
    apply fun c@(l@(Var var) :=: r) 
      | isUniversalVar var = id
        . substituteTakingSources (Map.singleton l r) 
        . removeCondition c
        . fun
    apply fun c@(l :=: r@(Var var))
      | isUniversalVar var = id
          . substituteTakingSources (Map.singleton r l) 
          . removeCondition c
          . fun
    apply fun _ = fun
  
solve_filter :: Solver (Maybe ZProof)
solve_filter = do
  Clause eq conds <- asks sGoal
  let vars = map freeUniversalVariables (eq : conds)
      singleton var = (<= 1)
                    . length
                    $ filter (elem var) vars
      usable cond = not
                  . any singleton
                  $ freeUniversalVariables cond
      conds' = filter usable conds
  if length conds == length conds'
    then return Nothing
    else do
      proof <- localGoal (Clause eq conds') solve_all 
      mapM (proofstep . Proof.Sim) proof
      
-- Had to essentially reimplement the Reducible ZClause instance here
-- since I had no nice way of detecting which type of proof
-- was used, i.e. Con or Eql.
solve_reduce :: Solver (Maybe ZProof) -> Solver (Maybe ZProof)
solve_reduce next_step = do
  goal@(Clause eq conds) <- asks sGoal
  stateful (reduce conds eq) $ \reduced_eq ->
    stateful (mapM (reduce conds) conds) $ \reduced_conds -> do
      case mconcat reduced_conds of
        ReducedToFalse -> Just <$> proofstep Proof.Con
        ReducedTo new_conds -> do
          let new_goals = case reduced_eq of
                ReducedToFalse -> [Clause eq new_conds]
                ReducedTo new_eqs ->
                  map (flip Clause new_conds) new_eqs
          proofs <- forM new_goals (flip localGoal next_step) 
          forM (conjoin proofs) $ \proofs -> do
            proof <- wrapProof proofs
            if new_goals == [goal] || proofStep proof == Proof.Eql
              then return proof
              else proofstep (Proof.Sim proof)
  where 
  wrapProof :: [ZProof] -> Solver ZProof
  wrapProof [] = proofstep Proof.Eql
  wrapProof [proof] = return proof
  wrapProof proofs = proofstep (Proof.Fac proofs)
                
solve_con :: Solver (Maybe ZProof)
solve_con = do
  conds <- asks (clauseConditions . sGoal)
  contr <- contradictory conds
  if contr 
    then Just <$> proofstep Proof.Con
    else return Nothing

solve_fac :: Solver (Maybe ZProof)
solve_fac = do
  goal <- asks sGoal
  let (l_term :=: r_term) = clauseEquality goal
      (l_func : l_args) = flattenApp l_term
      (r_func : r_args) = flattenApp r_term
  if l_func /= r_func
    then return Nothing
    else do
      let factor_goals = map pairToEquality (l_args `zip` r_args)
      factor_proofs <- forM factor_goals $
            \eq -> localGoalEquality eq 
                      . clearHypotheses
                      . tryToFalsifyGoal
                      $ solve_all
      mapM (proofstep . Proof.Fac) (conjoin factor_proofs)
        
solve_hyp :: Solver (Maybe ZProof)
solve_hyp = do
  hyp_proofs <- concat <$> applyHypotheses maybeApplyHyp
  mapM (proofstep . uncurry Proof.Hyp) (listToMaybe hyp_proofs)
  where
  maybeApplyHyp :: ZHypothesis -> Solver [(ZHypothesis, ZProof)]
  maybeApplyHyp hyp = do
    goal@(l_goal :=: r_goal) <- clauseEquality <$> asks sGoal
    let hyp_cls = hypClause hyp
        flipped_cls = flipQuantifiedClauseEquality hyp_cls
        apply_left = findApplications l_goal hyp_cls
        apply_right = findApplications r_goal flipped_cls
        l_eqs = map (second (\t -> (t :=: r_goal))) apply_left
        r_eqs = map (second (\t -> (l_goal :=: t))) apply_right
        all_eqs = l_eqs ++ r_eqs
    mapMaybeM solveEq all_eqs
    where
    solveEq (_, eq) =
      fmap (hyp, ) <$> localGoalEquality eq solve_all

  findApplications :: ZExpr -> ZQuantified -> [(ZExprSubstitution, ZExpr)]
  findApplications goal_expr
      (Quantified vars (Clause (from_hyp :=: to_hyp) [])) =
    map (id &&& applySubstitution) 
      . nubOrd
      . filter (completeSubstitution vars) 
      $ allUnifiers from_hyp goal_expr
    where
    applySubstitution :: ZExprSubstitution -> ZExpr
    applySubstitution sub = substituteTakingSources hyp_sub goal_expr
      where
      hyp_sub = Map.singleton from_hyp' to_hyp'
      from_hyp' = substituteTakingSources sub from_hyp
      to_hyp' = substituteTakingSources sub to_hyp
   
solve_ind :: Solver (Maybe ZProof)
solve_ind = do
  crits <- id
    <$> mergeCriticalTerms
    <$> filter inductiveCriticalTerm
    <$> criticalTerms True
  case crits of
    [] -> return Nothing
    cterm@(term, id) : rest -> do
      let alts = filter ((==) term . fst) rest
      disjoin <$> mapM goInductive (cterm : alts)
  where
  inductiveCriticalTerm :: CriticalTerm -> Bool
  inductiveCriticalTerm (term, _) =
    isVar term && isUniversalVar (fromVar term)
    
  goInductive :: CriticalTerm -> Solver (Maybe ZProof)
  goInductive cterm@(ind_term@(Var ind_var), _) = do
    goal <- asks sGoal
    hyps <- asks sHypotheses
    let all_inds = ind_var : map hypId hyps
        others = filter (not . flip elem all_inds) (freeUniversalVariables goal)
        forall = filter (not . isFunType . varType) others
    stateful cons_s $ \cons -> do
      maybe_ind_proofs <- mapM (goInductive' ind_var forall) cons
      let cons_terms = map fst cons
      flip mapM (conjoin maybe_ind_proofs) $ \proofs ->
        proofstep $ Proof.Ind ind_var forall (cons_terms `zip` proofs)
    where
    ty_fun = head . flattenAppType . getType $ ind_term
    cons_s = instantiateConstructors cterm
  goInductive cterm = error $ 
    "Invalid critical term for induction " ++ show cterm
    ++ "\nThis is a bug!"

  goInductive' :: ZVar -> [ZVar] -> ConstructorInstance -> Solver (Maybe ZProof) 
  goInductive' ind_var forall (new_term, ind_vars) = do
    goal <- asks sGoal
    hyps <- asks sHypotheses
    let createHyp :: ZVar -> ZHypothesis
        createHyp rec_var = Hypothesis rec_var [(ind_var, Var rec_var)]
                          $ Quantified forall hyp
          where hyp = replace ind_var rec_var goal
          
        groundHypothesis :: ZHypothesis -> [ZHypothesis]
        groundHypothesis hyp@(Hypothesis hyp_id hyp_binds 
                               (Quantified vars cls))
          | not (ind_var `elem` vars) = [hyp]
          | otherwise = map generateHyp (new_term : map Var ind_vars)
          where
          new_vars = filter (/= ind_var) vars
          
          generateHyp :: ZTerm -> ZHypothesis
          generateHyp new_term = Hypothesis hyp_id new_binds 
                               $ Quantified new_vars new_cls
            where
            new_binds = (ind_var, new_term) : hyp_binds
            subst = Map.singleton (Var ind_var) new_term
            new_cls = substituteTakingSources subst cls 

    let subst = Map.singleton (Var ind_var) new_term
        new_goal = substituteTakingSources subst goal
        new_hyps = concatMap groundHypothesis hyps
        created_hyps = map createHyp ind_vars
    
    local (\s -> s { sGoal = new_goal })
      . local (\s -> s { sHypotheses = created_hyps ++ new_hyps })
      $ solve_all

solve_cse :: Solver (Maybe ZProof)
solve_cse = do
  crits <- id
    <$> mergeCriticalTerms
    <$> criticalTerms True
  case find (isApp . fst) crits of
    Nothing -> return Nothing
    Just split -> goSplit split
  where
  provenPath :: ZTerm -> ZTerm -> Solver (Maybe (ZTerm, ZProof)) 
  provenPath term kterm
    | isApp kterm = return Nothing
    | otherwise = do
      conds <- clauseConditions <$> asks sGoal
      let goal = Clause (clearSources (term :=: kterm)) conds
      fmap (fmap (kterm, ))
        . localGoal goal
        . tryToFalsifyGoal
        . clearHypotheses
        $ solve_all

  goSplit :: CriticalTerm -> Solver (Maybe ZProof)
  goSplit cterm@(term, source) = do
    stateful (instantiateConstructors cterm) $ \cons -> do
      let kterms = map fst cons
          sourced_term = addSources [source] term
      proven_paths <- mapMaybeM (provenPath sourced_term) kterms
      case proven_paths of
        [] -> do
          splits <- mapM goSplit' kterms
          forM (conjoin splits) $ \proofs ->
            proofstep (Proof.Csp term (kterms `zip` proofs))
        [(kterm, proof1)] -> do
          maybe_proof2 <- goSplit' kterm
          forM maybe_proof2 $ \proof2 -> 
            proofstep (Proof.Icn (term :=: kterm) proof1 proof2)
        _ ->
          -- TODO This indicates a contradiction,
          -- but needs an Isabelle mapping
          return Nothing
    where
    goSplit' :: ZTerm -> Solver (Maybe ZProof)
    goSplit' kterm = 
      localAddGoalCondition (term :=: kterm) solve_all
    
solve_gen :: Solver (Maybe ZProof)
solve_gen = do
  inds <- id
    <$> filter (\t -> isVar t && isUniversalVar (fromVar t))
    <$> map fst
    <$> criticalTerms False
  goal <- asks sGoal
  let -- cons = map Var (constructors goal)
      subterms = id
        . concatMap strictlyWithinList
        $ exprList goal
      superterms = id
        . nubOrd
        . concatMap (usableSuperterms subterms) 
        $ inds 
        -- (inds ++ cons)
  disjoin <$> mapM generalise superterms
  where  
    usableSuperterms :: [ZTerm] -> ZTerm -> [ZTerm]
    usableSuperterms all_terms sub_term = 
      removeSupersets (filter superterm all_terms)
      --removeSubterms all_duplicates                 
      where
        all_duplicates :: [ZTerm]
        all_duplicates = filter superterm (duplicates all_terms)

        superterm :: ZTerm -> Bool
        superterm t = destructibleTerm t 
                   && isApp t 
                   && t `contains` sub_term 
                   && fromMaybe False (isDefinedVar <$> termFunction t)
  
solve_hcn :: Solver (Maybe ZProof)
solve_hcn = do
  hyp_proofs <- concat <$> applyHypotheses generaliseHyp
  forM (listToMaybe hyp_proofs) (proofstep . uncurry Proof.Hcn)
  where
  generaliseHyp :: ZHypothesis -> Solver [(ZHypothesis, ZProof)]
  generaliseHyp hyp@(Hypothesis hyp_id hyp_binds
                  (Quantified vars (Clause eq@(l_hyp :=: r_hyp) [])))
    | not (isConstructorTerm r_hyp) = return []
    | otherwise = do
        goal_term <- equalityLeft <$> clauseEquality <$> sGoal <$> ask 
        
        let possibleTerm :: ZTerm -> Bool
            possibleTerm term 
               = isApp term 
              && isDefinedVar var 
              && destructibleTerm term 
              && length (universalVariables term) == length vars + 1
              where
              Just var = termFunction term

        fmap catMaybes
          . sequence 
          $ do
            possible <- filter possibleTerm (strictlyWithinList l_hyp)
            uni <- allUnifiers possible goal_term
            guard (completeSubstitution vars uni) 
            let eq' = substitute uni eq
                genr = substitute uni possible
            return 
              . fmap (fmap (hyp, ))
              $ localAddGoalCondition eq' (generalise genr)
{-
randomSequence :: [Solver a] -> Solver [a]
randomSequence solvers = do
  random <- sRandom <$> ask
  let (solvers', random') = shuffle solvers random
  localRandom random' (splitGens solvers')
  where
    localRandom :: StdGen -> Solver a -> Solver a
    localRandom gen = local (\s -> s { sRandom = gen })
        
    splitGens :: [Solver a] -> Solver [a]
    splitGens = foldl' splitGen (return [])
      where 
        splitGen :: Solver [a] -> Solver a -> Solver [a]
        splitGen ss s = do
          random <- sRandom <$> ask
          let (r1, r2) = split random
          ss' <- localRandom r2 ss
          s' <- localRandom r1 s
          return (s' : ss')
-}
purifyGoal :: Solver a -> Solver a 
purifyGoal solver = do
  goal <- asks sGoal
  purified <- purifyConditions goal
  localGoal purified solver

-- |Returns the list of all critical terms in the current goal;
-- see 'criticalTerm'.
criticalTerms :: Bool -> Solver [CriticalTerm]
criticalTerms check_superset = do
  Clause (goal_l :=: goal_r) conds <- asks sGoal
  let all_terms = goal_l : goal_r : concatMap exprList conds
      filterer (term, _) 
        = isVar term 
        || not (any (flip contains term) all_terms)
  return 
    . nubOrd
    . filter filterer
    . mapMaybe (criticalTerm check_superset)
    $ all_terms
  where 
  criticalTerm :: Bool -> ZTerm -> Maybe CriticalTerm
  criticalTerm check_superset expr = do
    cterm@(term, src) <- id
      . runWriterT 
      . critical
      . evaluateToCase
      $ expr
    guard (not $ null src)
    guard (destructibleTerm term)
    guard (not check_superset 
      || all (not . orderedSupersetOf src) (allSources term))
    return cterm
    where
    critical :: ZExpr -> WriterT [Id] Maybe ZTerm
    critical (Cse id strict_term _) = do
      tell [id]
      if expr `contains` strict_term
          then critical (evaluateToCase strict_term)
        else if isTerm strict_term
          then lift $ Just $ strict_term
          else lift Nothing
    critical expr'
      | isTerm expr' = lift $ Just expr'
      | otherwise = lift Nothing

generalise :: ZTerm -> Solver (Maybe ZProof)
generalise term =
  stateful newIdS $ \new_id -> do
    goal <- asks sGoal
    let new_var = ZVar new_id Nothing (getType term) defaultVarClass
    maybe_proof <- id 
      . local (substituteTakingSources (Map.singleton term (Var new_var)))
      . tryToFalsifyGoal
      . clearHypotheses
      $ solve_all
    forM maybe_proof $ \proof -> 
      proofstep (Proof.Gen term new_var proof)

applyHypotheses :: forall a . (ZHypothesis -> Solver a) -> Solver [a]
applyHypotheses apply = do
  hyps <- asks sHypotheses
  stateful (mapM freshenHypothesis hyps)
    $ \fresh_hyps -> concat <$> mapM applyHyp (hyps `zip` fresh_hyps)
  where
  removeHypothesis :: ZHypothesis -> Solver b -> Solver b
  removeHypothesis hyp = local $ \s ->
    s { sHypotheses = delete hyp (sHypotheses s) }

  freshenHypothesis :: ZHypothesis -> StatefulSolver ZHypothesis
  freshenHypothesis hyp = do
    let Quantified vars cls = hypClause hyp
    fresh_vars <- mapM freshVariable vars
    let sub = Map.fromList $ vars `zip` fresh_vars
        fresh_cls = substituteTakingSources sub cls
    return $ hyp { hypClause = Quantified fresh_vars fresh_cls }

  applyHyp :: (ZHypothesis, ZHypothesis) -> Solver [a]
  applyHyp (old_hyp, fresh_hyp) = do
    apps <- applicable fresh_hyp
    removeHypothesis old_hyp (mapM apply apps)

  applicable :: ZHypothesis -> Solver [ZHypothesis]
  applicable hyp@(Hypothesis _ _ (Quantified _ (Clause _ []))) = return [hyp]
  applicable (Hypothesis hyp_id hyp_binds 
                (Quantified c_vars (Clause c_eq c_conds))) = do
    possible_subs <- mapM removeCondition c_conds
    return 
      . map applySub 
      . mergeUnifiers 
      . map (mconcat . map Unifier)
      $ sequence possible_subs
    where
    applySub :: ZExprSubstitution -> ZHypothesis
    applySub sub = Hypothesis hyp_id new_binds 
                 $ Quantified c_vars' (Clause c_eq' [])
      where 
      vars = map fromVar (Map.keys sub)
      c_vars' = filter (not . flip elem vars) c_vars
      c_eq' = substitute sub c_eq
      new_binds = hyp_binds ++ map (first fromVar) (Map.toList sub)
    
    validSubstitution :: ZExprSubstitution -> Bool
    validSubstitution = all (flip elem (map Var c_vars)) . Map.keys

    removeCondition :: ZEquality -> Solver [ZExprSubstitution]
    removeCondition eq@(c_l :=: c_r) = do
      g_conds <- clauseConditions <$> asks sGoal
      return 
        . filter validSubstitution
        . mergeUnifiers 
        . flip map g_conds 
        $ \(g_l :=: g_r) ->
          let uni_l = unify c_l g_l
              uni_r = unify c_r g_r
          in uni_l `mappend` uni_r
          
completeSubstitution :: Ord a => [a] -> ExprSubstitution a -> Bool
completeSubstitution vars sub = 
  Set.fromList (map Var vars) == Map.keysSet sub

localGoal :: ZClause -> Solver a -> Solver a
localGoal goal = local $ \s -> s { sGoal = goal }

localAddGoalCondition :: ZEquality -> Solver a -> Solver a
localAddGoalCondition eq = local $ \s -> s 
  { sGoal = addCondition eq (sGoal s) }
          
localGoalEquality :: ZEquality -> Solver a -> Solver a
localGoalEquality eq = local $ \s -> s 
  { sGoal = (sGoal s) { clauseEquality = eq } }

localGoalConditions :: [ZEquality] -> Solver a -> Solver a
localGoalConditions conds = local $ \s -> s
  { sGoal = (sGoal s) { clauseConditions = conds } }
          
combine :: [Solver (Maybe ZProof)] -> Solver (Maybe ZProof)
combine = fmap disjoin . sequence 

proofstep :: ZProofStep -> Solver ZProof
proofstep step = do
  goal <- asks sGoal
  hyps <- asks sHypotheses
  return (Proof step goal hyps)
  
clearGoalSources :: Solver a -> Solver a
clearGoalSources = local $ \s ->
  s { sGoal = clearSources (sGoal s) }
  
clearHypotheses :: Solver a -> Solver a
clearHypotheses = local $ \s -> s { sHypotheses = mempty }

tryToFalsifyGoal :: Solver (Maybe a) -> Solver (Maybe a)
tryToFalsifyGoal next_step = do
  goal <- asks sGoal
  false <- falsifiable (clearSources goal)
  if false then return Nothing else next_step

traceGoal :: String -> Solver (Maybe a) -> Solver (Maybe a)
traceGoal tag solver 
  | not debugSolver = solver
  | otherwise = do
    goal <- asks sGoal
    hyps <- asks sHypotheses
    let hyps_s = if null hyps 
          then "" 
          else "\nwith\n" ++ (intercalate "\n" $ map show hyps)
    flip local solver $
      trace (tag ++ ":\n" ++ show goal ++ hyps_s)
      
