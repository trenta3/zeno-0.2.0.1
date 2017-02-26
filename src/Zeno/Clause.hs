{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Zeno.Clause (
  Equality (..), Clause (..), 
  Quantified (..), Hypothesis (..),
  flipEquality, flipQuantifiedClauseEquality,
  equalityToPair, pairToEquality, 
  addCondition, removeCondition,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Expression
import Zeno.Traversing

data Equality a 
  = (:=:)       { equalityLeft :: !(Expr a),
                  equalityRight :: !(Expr a) }
  deriving ( Eq, Functor, Foldable, Traversable )

data Clause a
  = Clause      { clauseEquality :: !(Equality a),
                  clauseConditions :: ![Equality a] }
  deriving ( Eq, Functor, Foldable, Traversable )
  
data Quantified f a
  = Quantified  { quantifiedVariables :: ![a],
                  quantifiedObject :: !(f a) }
  deriving ( Eq, Functor, Foldable, Traversable )
  
data Hypothesis a 
  = Hypothesis  { hypId :: !a,
                  hypBinds :: ![Binding a], 
                  hypClause :: !(Quantified Clause a) }
  deriving ( Functor, Foldable, Traversable )
  
instance Eq a => Eq (Hypothesis a) where
  (==) = (==) `on` hypId
  
instance Ord a => Ord (Hypothesis a) where
  compare = compare `on` hypId
  
instance ExprTraversable Equality where
  mapExprM f (lhs :=: rhs) =
    return (:=:) `ap` f lhs `ap` f rhs
    
instance ExprTraversable Clause where
  mapExprM f (Clause eq conds) = 
    return Clause `ap` mapExprM f eq `ap` mapM (mapExprM f) conds
    
instance ExprTraversable (Quantified Clause) where
  mapExprM f (Quantified vars cls) =
    return (Quantified vars) `ap` mapExprM f cls
    
instance ExprTraversable Hypothesis where
  mapExprM f (Hypothesis id binds cls) = 
    return (Hypothesis id) `ap` mapM mapBind binds `ap` mapExprM f cls
    where mapBind (b, expr) = do
            expr' <- f expr 
            return (b, expr')
            
instance WithinTraversable (Expr a) (Equality a) where
  mapWithinM f (t1 :=: t2) = do
    t1' <- mapWithinM f t1
    t2' <- mapWithinM f t2
    return (t1' :=: t2')
  
instance WithinTraversable (Expr a) (Clause a) where
  mapWithinM f (Clause eq conds) = do
    eq' <- mapWithinM f eq
    conds' <- mapM (mapWithinM f) conds
    return (Clause eq' conds')
    
instance WithinTraversable c (a b) => 
         WithinTraversable c (Quantified a b) where
  mapWithinM f (Quantified vars obj) = do
    obj' <- mapWithinM f obj
    return (Quantified vars obj')
    
instance WithinTraversable (Expr a) (Hypothesis a) where
  mapWithinM f (Hypothesis id binds cls) =
    Hypothesis id binds `liftM` mapWithinM f cls
    
instance (Show b, Show (a b)) => Show (Quantified a b) where
  show (Quantified vars obj) = 
    case vars of
      [] -> show obj
      _ -> "forall " ++ (intercalate ", " $ map show vars) 
        ++ " . " ++ show obj
  
instance Show a => Show (Hypothesis a) where
  show = show . hypClause
        
instance Show a => Show (Equality a) where
  show (l :=: r) = show l ++ " = " ++ show r

instance Show a => Show (Clause a) where
  show (Clause t cs) = 
    let cs_s = case cs of
          [] -> ""
          cs -> " :- " 
            ++ intercalate ", " (map show cs)
    in show t ++ cs_s
    
flipEquality :: Equality a -> Equality a 
flipEquality (l :=: r) = r :=: l

equalityToPair :: Equality a -> (Expr a, Expr a)
equalityToPair (l :=: r) = (l, r)

pairToEquality :: (Expr a, Expr a) -> Equality a
pairToEquality = uncurry (:=:)

flipClauseEquality :: Clause a -> Clause a
flipClauseEquality cs = cs 
  { clauseEquality = flipEquality (clauseEquality cs) }
  
flipQuantifiedClauseEquality :: Quantified Clause a -> Quantified Clause a
flipQuantifiedClauseEquality q = q
  { quantifiedObject = flipClauseEquality (quantifiedObject q) }

addCondition :: Equality a -> Clause a -> Clause a
addCondition eq cs = cs 
  { clauseConditions = clauseConditions cs ++ [eq] }
  
removeCondition :: Eq a => Equality a -> Clause a -> Clause a
removeCondition cond (Clause eq conds) =
  Clause eq (delete cond conds)

