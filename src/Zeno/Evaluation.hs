-- |This module contains functions which will normalise a 'ZExpr'.
module Zeno.Evaluation (
  simplify,
  evaluateR,
  evaluate,
  evaluateBindings,
  evaluateToCase,
  updateDefinitions,
  clausify,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import qualified Data.Map as Map

updateDefinitions :: Functor f => ZBindings -> f ZVar -> f ZVar
updateDefinitions binds = fmap updateVar
  where
  flat = flattenBindings binds
  is_rec = isRec binds
  
  updateVar :: ZVar -> ZVar
  updateVar var =
    case lookup var flat of
      Just expr -> updateDefinedVar (Just is_rec) expr var
      Nothing -> var

updateDefinedVar :: Maybe Bool -> ZExpr -> ZVar -> ZVar
updateDefinedVar rc' expr var = 
  case varClass var of
    DefinedVar _ rc -> 
      var { varClass = DefinedVar (Just expr) (fromMaybe rc rc') }
    
replaceAllVars :: Functor f => [ZVar] -> f ZVar -> f ZVar
replaceAllVars vars = replaceMany (vars `zip` vars)

clausify :: ZBinding -> Maybe (String, ZClause)
clausify (var, expr) = do
  (guard . (isSuffixOf "Prop") . show 
    . returnType . getType) var
  cls <- clausify' expr
  name <- varName var
  return (name, cls)
  where
  tryEval :: (ZExpr -> Maybe a) -> ZExpr -> Maybe a
  tryEval f expr
    | expr' /= expr = f expr'
    | otherwise = Nothing
    where expr' = simplify expr
    
  equalify :: ZExpr -> Maybe ZEquality
  equalify expr@(App (App (Var eq) lhs) rhs)
    | ":=:" `isInfixOf` show eq 
      && "Equals" `isSuffixOf` show (getType expr) = 
      return (lhs :=: rhs)
  equalify expr = 
    tryEval equalify expr
  
  clausify' :: ZExpr -> Maybe ZClause
  clausify' (Lam _ rhs) = clausify' rhs 
  clausify' (App (App (Var given) eq) prop)
    | "Given" `isSuffixOf` show given = do
      guard $ "Prop" `isSuffixOf` show (getType prop)
      new_cond <- equalify eq
      Clause eq conds <- clausify' prop
      return (Clause eq (new_cond : conds))
  clausify' (App (Var prove) eq) 
    | "Prove" `isSuffixOf` show prove = do
      goal <- equalify eq
      return (Clause goal [])
  clausify' expr = 
    tryEval clausify' expr

evaluateBindings :: ZBindings -> ZBindings
evaluateBindings (NonRec (var, expr)) = 
  NonRec (updateDefinedVar (Just False) expr var, expr)
evaluateBindings (Rec binds) = Rec exprs
  where
  exprs = map evaluateBinding binds 
  vars = map fst exprs
  
  evaluateBinding :: ZBinding -> ZBinding
  evaluateBinding (var, expr) = (updateDefinedVar (Just True) expr' var, expr')
    where 
    expr' = replaceAllVars vars expr
    
derivingTerm :: [ZExpr] -> ZTerm
derivingTerm exprs = fromMaybe (last exprs) (find isTerm exprs)

simplify :: ZExpr -> ZExpr
simplify = mapWithin simplifyExpr
  where
  simplifyExpr (Var (varClass -> DefinedVar (Just def) False)) = def
  simplifyExpr (App Err _) = Err
  simplifyExpr (App fun@(Lam var rhs) arg) = 
    case unify (getType var) (getType arg) of
      NoUnifier -> error $
        "Couldn't unify types in term application evaluation." 
        ++ "\n" ++ showTyped arg
        ++ "\napplied to\n" ++ showTyped fun
      Unifier sub -> id
        . simplify
        . updateType sub
        . replaceWithin (Var var) arg
        $ rhs
  simplifyExpr expr@(Cse id lhs alts)
    | isVar fun && isConstructorVar fun_var = simplify new_expr
    where
    fun : args = flattenApp lhs
    fun_var = fromVar fun
    
    matching_alt = fromMaybe (fromMaybe failure find_default) find_match
      where
      find_match = find ((== AltCon fun_var) . altCon) alts
      find_default = find ((== AltDefault) . altCon) alts
      failure = error $ "Incomplete pattern in: " ++ show expr
      
    alt_vars = (map Var . altVars) matching_alt
    subst = Map.fromList (alt_vars `zip` args)
    new_expr = (substitute subst . altExpr) matching_alt
    
  simplifyExpr expr = expr
          
evaluateToCase :: ZExpr -> ZExpr
evaluateToCase 
  = head
  . flip runReader []
  . evaluateExpr

evaluate :: [ZEquality] -> ZExpr -> ZExpr
evaluate facts = flip runReader facts . evaluateR

evaluateR :: MonadReader [ZEquality] m => ZExpr -> m ZExpr
evaluateR = mapExprM (liftM derivingTerm . evaluateExpr)

evaluateExpr :: MonadReader [ZEquality] m => ZExpr -> m [ZExpr]
evaluateExpr expr@(Var var) = return $
  case varClass var of
    DefinedVar (Just def) _ -> [def, expr]
    DefinedVar Nothing _ -> error $ "Undefined function: " ++ show var
    _ -> [expr]
evaluateExpr expr@(App fun arg) = do
  (fun' : funs) <- evaluateExpr fun
  arg' <- liftM derivingTerm . evaluateExpr $ arg
  let hist = map (flip App arg') funs
      expr' = simplify (App fun' arg')
  exprs <-
    if isLam fun'
      then evaluateExpr expr'
      else return [expr']
  return (exprs ++ hist)
evaluateExpr (Let binds rhs) = 
  evaluateExpr $ replaceAllVars vars rhs
  where 
  vars = map fst 
       . flattenBindings
       $ evaluateBindings binds
evaluateExpr expr@(Cse id lhs alts) = do
  lhs' <- liftM derivingTerm $ evaluateExpr lhs
  facts <- asks (map equalityToPair)
  let lhs'' = fromMaybe lhs' (lookup lhs' facts)
      expr' = simplify (Cse id lhs'' alts)
  if isConstructorTerm lhs''
    then evaluateExpr expr'
    else return [expr']
evaluateExpr expr = return [expr]


