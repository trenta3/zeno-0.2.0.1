{-# LANGUAGE DeriveFunctor, DeriveFoldable, 
             DeriveTraversable, TupleSections #-}
-- |This module contains the AST of Zeno's internal functional syntax, 
-- which is essentially GHC core.
module Zeno.Expression (
  Expr (..), Bindings (..), Alt (..),
  AltCon (..), ExprTraversable (..),
  Binding, Term, ExprSubstitution,
  isTerm, isVar, fromVar, isApp, isCse, isErr, isLam,
  flattenBindings, freeVariables, isRec,
  flattenApp, unflattenApp, termFunction,
  flattenLambdas, unflattenLambdas,
  boundVars, boundExprs,
  mapExprMaybe, mapExpr,
  isOperator,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Id
import Zeno.Traversing
import Zeno.Utils
import Zeno.Unification

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |This is an expression for which 'isTerm' should be 'True'.
type Term a = Expr a  
type Binding a = (a, Expr a)
type ExprSubstitution a = Substitution (Expr a) (Expr a)

-- |Expressions in Zeno, essentially GHC core syntax.
data Expr a 
  = Err
  | Var !a
  | App !(Expr a) !(Expr a)
  | Let !(Bindings a) !(Expr a)
  | Lam !a !(Expr a)
  
  -- |Case analysis has an identifier for our 'CriticalTerm' technique
  | Cse !Id !(Expr a) ![Alt a]
  deriving ( Eq, Ord, Functor, Foldable, Traversable )

data Bindings a 
  = NonRec !(Binding a)
  | Rec ![Binding a]
  deriving ( Eq, Ord, Functor, Foldable, Traversable )

data Alt a
  = Alt     { altCon :: !(AltCon a),
              altVars :: ![a],
              altExpr :: !(Expr a) }
  deriving ( Eq, Ord, Functor, Foldable, Traversable )
  
data AltCon a
  = AltCon !a
  | AltDefault
  deriving ( Eq, Ord, Functor, Foldable, Traversable )
  
class ExprTraversable f where
  mapExprM :: Monad m => (Expr a -> m (Expr a)) -> f a -> m (f a)
  
  exprList :: f a -> [Expr a]
  exprList = execWriter . mapExprM (\x -> tell [x] >> return x)
  
mapExpr :: ExprTraversable f => (Expr a -> Expr a) -> f a -> f a
mapExpr = mapM_to_fmap mapExprM

mapExprMaybe :: ExprTraversable f => 
  (Expr a -> Maybe (Expr a)) -> f a -> Maybe (f a)
mapExprMaybe = mapM_to_mapMaybe mapExprM
  
instance ExprTraversable Expr where
  mapExprM = id
  exprList = return
  
instance ExprTraversable Bindings where
  mapExprM f (NonRec (var, expr)) = 
    return (NonRec . (var, )) `ap` f expr
  mapExprM f (Rec binds) = 
    return Rec `ap` mapM mapBind binds
    where
    mapBind (var, expr) = liftM (var, ) (f expr)
  exprList = boundExprs
  
flattenBindings :: Bindings a -> [Binding a]
flattenBindings (NonRec bind) = [bind]
flattenBindings (Rec binds) = binds
  
boundVars :: Bindings a -> [a]
boundVars = map fst . flattenBindings 

boundExprs :: Bindings a -> [Expr a]
boundExprs = map snd . flattenBindings

isRec :: Bindings a -> Bool
isRec (Rec {}) = True
isRec _ = False
  
freeVariables :: (Ord a, WithinTraversable (Expr a) (f a), Foldable f) => 
  f a -> [a]
freeVariables expr = Set.toList freeVars
  where
  allVars = Set.fromList (toList expr)
  boundVars = execWriter (mapWithinM writeBound expr)
  freeVars = allVars `Set.difference` boundVars
  
  writeBound expr@(Cse _ _ alts) = do
    let bound = concatMap altVars alts
    tell (Set.fromList bound)
    return expr
  writeBound expr@(Lam var _) = do
    tell (Set.singleton var)
    return expr
  writeBound expr = 
    return expr
  
-- |Terms are just variables, errors and application.
isTerm :: Expr a -> Bool
isTerm (App lhs rhs) = isTerm lhs
isTerm Err = True
isTerm (Var _) = True
isTerm _ = False

isVar :: Expr a -> Bool
isVar (Var _) = True
isVar _ = False

isErr :: Expr a -> Bool
isErr Err = True
isErr _ = False

isApp :: Expr a -> Bool
isApp (App _ _) = True
isApp _ = False

isCse :: Expr a -> Bool
isCse (Cse {}) = True
isCse _ = False

isLam :: Expr a -> Bool
isLam (Lam {}) = True
isLam _ = False

fromVar :: Expr a -> a
fromVar (Var v) = v

flattenApp :: Expr a -> [Expr a]
flattenApp (App lhs rhs) = flattenApp lhs ++ [rhs]
flattenApp expr = [expr]

unflattenApp :: [Expr a] -> Expr a
unflattenApp [] = Err
unflattenApp xs = foldl1 App xs

flattenLambdas :: Expr a -> ([a], Expr a)
flattenLambdas (Lam v rhs) = 
  let (vs, rhs') = flattenLambdas rhs in (v : vs, rhs')
flattenLambdas expr = ([], expr)

unflattenLambdas :: [a] -> Expr a -> Expr a
unflattenLambdas = flip (foldr Lam)

termFunction :: Term a -> Maybe a
termFunction term = 
  case head (flattenApp term) of
    Var v -> Just v
    _ -> Nothing

instance Ord a => Unifiable (Expr a) where
  type Names (Expr a) = Expr a

  unify Err Err = mempty
  unify (Var v1) (Var v2)
    | v1 == v2 = mempty
  unify var@(Var _) expr =
    Unifier (Map.singleton var expr)
  unify (App f1 a1) (App f2 a2) =
    unify f1 f2 `mappend` unify a1 a2
  unify _ _ = NoUnifier

instance WithinTraversable (Expr a) (Expr a) where
  mapWithinM f (App lhs rhs) =
    f =<< return App `ap` mapWithinM f lhs `ap` mapWithinM f rhs
  mapWithinM f (Cse id lhs alts) =
    f =<< return (Cse id) `ap` mapWithinM f lhs `ap` mapM (mapWithinM f) alts
  mapWithinM f (Let bind rhs) =
    f =<< return Let `ap` mapWithinM f bind `ap` mapWithinM f rhs
  mapWithinM f (Lam var rhs) =
    f =<< return (Lam var) `ap` mapWithinM f rhs
  mapWithinM f expr =
    f =<< return expr
    
mwBindingM :: Monad m => 
  (Expr a -> m (Expr a)) -> Binding a -> m (Binding a)
mwBindingM f (b, x) = return (b,) `ap` mapWithinM f x 
  
instance WithinTraversable (Expr a) (Bindings a) where
  mapWithinM f (NonRec b) = 
    return NonRec `ap` mwBindingM f b
  mapWithinM f (Rec bs) = 
    return Rec `ap` mapM (mwBindingM f) bs

instance WithinTraversable (Expr a) (Alt a) where
  mapWithinM f (Alt con binds rhs) = 
    return (Alt con binds) `ap` mapWithinM f rhs

instance Show a => Show (Expr a) where
  show = flip runReader 0 . showExpr

instance Show a => Show (Bindings a) where
  show = flip runReader 0 . showBindings

showAlt :: Show a => Alt a -> Indented String
showAlt (Alt con binds rhs) = do
  i <- indentation
  rhs_s <- indent $ showExpr rhs
  let con_s = case con of
        AltDefault -> "_"
        AltCon var -> show var ++ concatMap ((" " ++) . show) binds
  return $ i ++ con_s ++ " -> " ++ rhs_s
  
showBinding :: Show a => (a, Expr a) -> Indented String
showBinding (var, rhs) = do
  rhs' <- indent (showExpr rhs)
  return $ show var ++ " = " ++ rhs'
  
showBindings :: Show a => Bindings a -> Indented String
showBindings (Rec []) = return ""
showBindings (NonRec bind) = do
  bind' <- showBinding bind
  i <- indentation
  return $ i ++ "let " ++ bind'
showBindings (Rec binds) = do
  i <- indentation
  binds' <- intercalate (i ++ "and ") <$> mapM showBinding binds
  return $ i ++ "let rec " ++ binds' 
  
isOperator :: String -> Bool
isOperator = any (not . isNormalChar)
  where
  isNormalChar :: Char -> Bool
  isNormalChar '_' = True
 -- isNormalChar '$' = True
  isNormalChar '.' = True
  isNormalChar c = isAlphaNum c
    
showExpr :: Show a => Expr a -> Indented String
showExpr Err = return "undefined"
showExpr (Var var) = (return . stripModuleName . show) var
showExpr (flattenApp -> Var fun : args) 
  | (show fun == "(,)" && length args == 2)
    || (show fun == "(,,)" && length args == 3)
    || (show fun == "(,,,)" && length args == 4) = do
       args' <- mapM showExpr args
       return $
         "(" ++ intercalate ", " args' ++ ")"
showExpr (App (App (Var fun) arg1) arg2) 
  | isOperator fun_s && isTerm arg1 && isTerm arg2 = do
    arg1' <- (indent . showExpr) arg1
    arg2' <- (indent . showExpr) arg2
    let arg1_s = if isTerm arg1 then arg1' else "(" ++ arg1' ++ ")"
        arg2_s = if isTerm arg2 then arg2' else "(" ++ arg2' ++ ")"
    if fun_s == ":" && arg2_s == "[]" 
      then return $ "[" ++ arg1_s ++ "]"
      else return $ "(" ++ arg1_s ++ " " ++ fun_s ++ " " ++ arg2_s ++ ")"
  where
  fun_s = show fun
showExpr (App lhs rhs) = do
  lhs' <- (indent . showExpr) lhs
  rhs' <- (indent . showExpr) rhs
  let lhs_s = if isVar lhs || isApp lhs then lhs' else "(" ++ lhs' ++ ")"
      rhs_s = if isVar rhs then rhs' else "(" ++ rhs' ++ ")"
  return $ lhs_s ++ " " ++ rhs_s 
showExpr expr@(Lam {}) = do
  let (vars, rhs) = flattenLam expr
      vars_s = intercalate " " (map show vars)
  rhs_s <- showExpr rhs
  return $ "\\" ++ vars_s ++ " -> " ++ rhs_s
  where
  flattenLam :: Expr a -> ([a], Expr a)
  flattenLam (Lam var rhs) = (var : vars, real_rhs)
    where (vars, real_rhs) = flattenLam rhs
  flattenLam expr = ([], expr)
showExpr (Cse id lhs alts) = do
  alts' <- indent . concatMapM showAlt $ alts
  lhs' <- indent . showExpr $ lhs
  let lhs'' = if isTerm lhs then lhs' else "(" ++ lhs' ++ ")"
  i <- indentation
  return $ i ++ "case " ++ lhs'' ++ " of" ++ alts'
showExpr (Let binds rhs) = do
  binds' <- showBindings binds
  rhs' <- showExpr rhs
  return $ binds' ++ " in " ++ rhs'
  
