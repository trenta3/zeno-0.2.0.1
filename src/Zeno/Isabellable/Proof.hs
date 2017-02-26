-- |Here we convert Zeno proofs to Isabelle/HOL ones.
-- Horribly kludged code, you were warned.
module Zeno.Isabellable.Proof (
  namedIsabelleProof
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Proof

import Zeno.Isabellable.Class
import Zeno.Isabellable.Core

import qualified Data.Text as Text

type IsaProof = RWS (Int, Text) [Text] Int 

atpTactic :: Text
atpTactic = " by (metis | simp)"

simpTactic :: Text
simpTactic = " by (metis | simp)"

elimTactic :: [Text] -> Text
elimTactic rules = " by (elim " ++ intercalate " " rules ++ " | metis | simp)"

instance IndentationMonad IsaProof where
  indent = local (first (+ 1))
  resetIndent = local (first (const 0))
  indentation = asks $ \(i, _) -> fromString $ "\n" ++ (concat . replicate i) "  " 
  
runIsaProof :: String -> IsaProof Text -> Text
runIsaProof name rws = concat lemmas
  where
  (_, lemmas) = evalRWS rws (0, fromString name) 1

namedIsabelleProof :: String -> ZProof -> Text
namedIsabelleProof name prf =
  runIsaProof name (makeLemma prf)
  
instance Isabellable ZProof where
  toIsabelle = runIsaProof mempty . makeLemma

tickquote :: Text -> Text
tickquote str = "`" ++ str ++ "`"

makeLemma :: ZProof -> IsaProof Text
makeLemma prf@(Proof _ cls@(Clause _ conds) _) = (resetIndent . indent) $ do
  name <- asks snd
  id <- get
  modify (+ 1)
  prf' <- isaProof True prf
  let fixs = concatMap fixes (freeUniversalVariables cls)
  cond_assms <- concat 
    <$> zipWithM makeAssume (conditionNames conds) conds
  let name_prefix =
        if (not . Text.null) name && id > 1 
          then name ++ "_" 
          else name
      lemma_name = name_prefix ++ 
        if id > 1 || Text.null name
          then "step_" ++ fromString (show id) 
          else ""
      lemma = "\n\nlemma " ++ lemma_name ++ " :" ++ fixs ++
        "\n  shows " ++ (quote . toIsabelle) cls ++ 
        "\nproof -" ++ cond_assms ++ prf' ++ "\nqed"
  tell [lemma]
  return lemma_name
  where   
  fixes :: ZVar -> Text
  fixes var =
    "\n  fixes " ++ toIsabelle var ++
    " :: " ++ (quote . toIsabelle . varType) var
  
hypothesisName :: ZVar -> Text
hypothesisName = fromString . ("hyp_" ++) . show . varId

makeAssume :: Isabellable a => Text -> a -> IsaProof Text
makeAssume n c = do
  i <- indentation
  return $ 
    i ++ "assume " ++ n ++ " : " ++ quote (toIsabelle c)

conditionNames :: [ZEquality] -> [Text]
conditionNames conds = 
  flip map [1..length conds] $ \i -> "c" ++ fromString (show i)

isaProof :: Bool -> ZProof -> IsaProof Text
isaProof end (Proof step cls@(Clause goal conds) hyps) = isaStep step
  where
  goal_s = (quote . toIsabelle) goal
  cls_s = (quote . toIsabelle) cls
  
  fix :: ZVar -> IsaProof Text
  fix var = do
    i <- indentation
    return $ 
      i ++ "fix " ++ toIsabelle var ++ 
      " :: " ++ (quote . toIsabelle . varType) var
  
  have :: Bool -> Bool -> [Text] -> IsaProof Text
  have end withthis fcts = do
    i <- indentation
    let fcts' = intercalate " and " fcts ++ i
        text = 
          if null fcts
            then if withthis 
              then if end
                then "thus"
                else "hence"
              else if end
                then "show"
                else "have"
            else if withthis 
              then if end
                then "with " ++ fcts' ++ "  show"
                else "with " ++ fcts' ++ "  have"
              else if end
                then "from " ++ fcts' ++ "  show"
                else "from " ++ fcts' ++ "  have"
    return $ i ++ text ++ " "
  
  cond_names = conditionNames conds
  hyp_names = map (hypothesisName . hypId) hyps
  
  subProof :: Text -> Text -> IsaProof Text
  subProof prop proof
    | null cond_names = do  
      hve <- have end False []
      i <- indentation
      return $ hve ++ prop ++ proof ++ i ++ "qed"
    | otherwise = do
      i <- indentation
      hve1 <- have False False []
      hve2 <- have end True cond_names
      return $
        hve1 ++ prop ++ proof ++ 
        i ++ "qed" ++
        hve2 ++ goal_s ++ simpTactic
      
  isaCase :: [ZVar] -> (ZTerm, ZProof) -> IsaProof Text
  isaCase forall (term, prf@(Proof _ (Clause goal' conds') hyps')) = indent $ do
    prf' <- isaProof True prf
    fixes <- concat <$> mapM fix (args ++ forall)
    hyp_assms <- concat <$> zipWithM makeAssume hyp_names' new_hyps
    cond_assms <- concat <$> zipWithM makeAssume cond_names' conds'
    return $ fixes ++ cond_assms ++ hyp_assms ++ prf'
    where
    args = (map fromVar . tail . flattenApp) term
    new_hyps = nubAndDifference hyps' hyps
    hyp_names' = map (hypothesisName . hypId) new_hyps
    cond_names' = conditionNames conds'
   
  isaStep :: ZProofStep -> IsaProof Text
  isaStep Eql = do
    hve <- have end False cond_names
    return $ hve ++ goal_s ++ simpTactic
    
  isaStep Con = do
    hve1 <- have False False cond_names
    hve2 <- have end True []
    return $
      hve1 ++ "False" ++ simpTactic ++
      hve2 ++ goal_s ++ simpTactic
    
  isaStep (Sim prf@(Proof _ cls'@(Clause _ conds') _))
    | conds' == conds = do
      prf' <- isaProof False prf
      hve <- have end True cond_names
      return $ prf' ++ 
        hve ++ goal_s ++ simpTactic
    | otherwise = do
      prf' <- indent (isaProof True prf)
      i <- indentation
      cond_assms <- indent 
         $  concat 
        <$> zipWithM makeAssume (conditionNames conds') conds'
      let proof = i ++ "proof -" ++ cond_assms ++ prf'
      subProof ((quote . toIsabelle) cls') proof
      
  isaStep (Fac [prf]) = do
    prf' <- isaProof False prf
    hve <- have end True []
    return $ prf' ++
      hve ++ goal_s ++ simpTactic
      
  isaStep (Fac fcts) = do
    (names, prfs) <- unzip <$> zipWithM isaFactor [1..] fcts
    hve <- have end False names
    return $ concat prfs ++
      hve ++ goal_s ++ simpTactic
    where
    isaFactor :: Int -> ZProof -> IsaProof (Text, Text)
    isaFactor i prf@(Proof _ (Clause goal _) _) = do
      prf' <- isaProof False prf
      hve <- have False True []
      let name = fromString $ "fct_" ++ show i
          proof = prf' ++
            hve ++ name ++ 
            " : " ++ quote (toIsabelle goal) ++ simpTactic
      return (name, proof)
      
  isaStep (Gen term var prf@(Proof _ cls'@(Clause _ conds') _)) = do
    gen_name <- makeLemma prf
    hve <- have end False (gen_name : cond_names)
    return $
      hve ++ goal_s ++ elimTactic (gen_name : cond_names)
      
  isaStep (Hyp hyp prf@(Proof _ (Clause goal' _) _)) = do
    prf' <- isaProof False prf
    hve1 <- have False False (hypothesisName (hypId hyp) : cond_names)
    hve2 <- have end True ("pre_hyp" : cond_names)
    i <- indentation
    return $ prf' ++
      i ++ "note pre_hyp = this" ++
      hve1 ++ (quote . toIsabelle) hyp ++ atpTactic ++ 
      hve2 ++ goal_s ++ atpTactic
    
  isaStep (Hcn hyp prf@(Proof _ (Clause goal' conds') _)) = do
    prf' <- isaProof end prf
    hve1 <- have False False (hypothesisName (hypId hyp) : cond_names)
    return $
      hve1 ++ new_cond_name ++ " : " ++ 
      new_cond ++ simpTactic ++ prf'
    where
    new_cond = (quote . toIsabelle . last) conds'
    new_cond_name = last (conditionNames conds')
    
  isaStep (Icn (term :=: kterm) prf1 
           prf2@(Proof _ cls2@(Clause _ conds') _)) = do
    i <- indentation
    prf1_name <- makeLemma prf1
    prf2' <- indent (isaProof True prf2)
    hve1 <- have False False []
    hve2 <- have end True (prf1_name : cond_names)
    cond_assms <- indent 
         $  concat 
        <$> zipWithM makeAssume (conditionNames conds') conds'
    return $ hve1 ++ cls2_s ++
      i ++ "proof -" ++ cond_assms ++ prf2' ++ 
      i ++ "qed" ++
      hve2 ++ cls_s ++ simpTactic
    where
    cls2_s = (quote . toIsabelle) cls2
    
  isaStep (Csp term cses) = do
    i <- indentation
    cses' <- (foldr1 (++) . intersperse (i ++ "next"))
      <$> mapM (isaCase []) cses
    subProof cls_s (i ++ csp ++ cses')
    where
    csp = "proof (cases " ++ (quote . toIsabelle) term ++ ")"

  isaStep (Ind var forall cses) = do
    i <- indentation
    cses' <- (foldr1 (++) . intersperse (i ++ "next"))
      <$> mapM (isaCase forall) cses
    subProof cls_s (i ++ ind ++ cses')
    where
    arb | null forall = ""
        | otherwise = " arbitrary:" 
            ++ concatMap ((" " ++) . toIsabelle) forall
      
    var_s = if var `elem` cls then toIsabelle var else "_"
    ind = "proof (induct " ++ var_s ++ arb ++ ")"
    

        


