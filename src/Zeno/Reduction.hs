-- |This module 'reduceM's something to the conjunction of simpler, 
-- logically equivalent things, or falsity.
--
-- It implements simple /iff/ transformations, some of which are given below. 
-- These should be read from left to right, and uses lists to represent conjunction;
-- so [] is logical truth.
--
-- Extensionality: 
-- @
--    f = g <==> [f x = g x]  (for some new x)
-- @
--
-- Constructor factoring:
-- @
--    K x1 y1 = K x2 y2 <==> [x1 = x2, y1 = y2]
--    where K is a constructor
-- @
--
-- Constructor inequality:
-- @
--    K ... = J ... <==> _|_
--    where K and J are both constructors
-- @
--
-- Error equality:
-- @
--    _|_ = _|_ <==> []
-- @
--
-- Error-constructor inequality:
-- @
--    _|_ = K ... <==> _|_
--    where K is a constructor
-- @
--
-- Antecedent contradiction
-- @
--    (_|_ ==> A) <==> []
-- @
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Zeno.Reduction (
  reduceM, reduce, Reduction (..)
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Evaluation

-- |'Reduction a' is the logical reduction of a value of type 'a'.
-- It is either false ('ReducedToFalse') 
-- or the conjunction of a new set of values ('ReducedTo').
-- Truth is represented by 'ReducedTo []', as this is an empty conjunction.
data Reduction a = ReducedToFalse | ReducedTo [a]
  deriving ( Eq, Functor, Foldable, Traversable )

instance Show a => Show (Reduction a) where
  show ReducedToFalse = "_|_"
  show (ReducedTo xs) = "[" ++ intercalate "; " (map show xs) ++ "]"
  
-- |The Reducible class specifies types which can be logically reduceMd.
-- It possibly creates new variables and takes a list of background facts.
-- This reduction will always be iff.
class Reducible a where
  reduceM :: (IdCounter r, MonadReader [ZEquality] m, MonadState r m) => 
    a -> m (Reduction a)
 
reduce :: (Reducible a, IdCounter r, Monad m) => 
  [ZEquality] -> a -> StateT r m (Reduction a)
reduce facts = flip runReaderT facts . reduceM

-- |This is the 'Monoid' of reductions under logical conjunction. 
-- Think of 'mappend' as '(&&)' and 'mempty' as 'True'.
instance Monoid (Reduction a) where
  mempty = ReducedTo []
  
  mappend _ ReducedToFalse = ReducedToFalse
  mappend ReducedToFalse _ = ReducedToFalse
  mappend (ReducedTo xs) (ReducedTo ys) = ReducedTo (xs ++ ys)

instance Reducible ZQuantified where
  reduceM (Quantified vars cls) = do
    reduceMd_cls <- reduceM cls
    return (Quantified vars <$> reduceMd_cls)
    
instance Reducible ZHypothesis where
  reduceM (Hypothesis id binds cls) = do 
    reduceMd_cls <- reduceM cls
    return (Hypothesis id binds <$> reduceMd_cls)
  
instance Reducible ZClause where
  reduceM cls = do
    Clause goal conds <- mapExprM evaluateR cls
    reduceMd_goal <- reduceM goal
    reduceMd_conds <- mapM reduceM conds
    return $ case mconcat reduceMd_conds of  
      ReducedToFalse -> mempty
      ReducedTo new_conds -> case reduceMd_goal of
        ReducedToFalse ->
          if null new_conds 
            then ReducedToFalse
            else ReducedTo [Clause goal new_conds]
        ReducedTo new_goals ->
          ReducedTo $ map (\g -> Clause g new_conds) new_goals
          
instance Reducible ZEquality where
  reduceM (Err :=: Err) = 
    return (ReducedTo [])
  reduceM eq@(Err :=: x2) = 
    if isConstructorTerm x2
      then return ReducedToFalse
      else reduceMFail eq
  reduceM eq@(x1 :=: Err) =
    if isConstructorTerm x1
      then return ReducedToFalse
      else reduceMFail eq
  reduceM (Var v1 :=: Var v2)
    | v1 == v2 = return (ReducedTo [])
    | both_cons && v1 /= v2 = return ReducedToFalse
    where both_cons = isConstructorVar v1 && isConstructorVar v2
  reduceM eq@(x1 :=: x2) 
    | isConstructorTerm x1 && isConstructorTerm x2 =
      if fun1 /= fun2
        then return ReducedToFalse
        else assert (length args1 == length args2) 
           $ liftM mconcat
           $ zipWithM reduceMSubEq args1 args2
    where
    Var fun1 : args1 = flattenApp x1
    Var fun2 : args2 = flattenApp x2
    reduceMSubEq x1 x2 = do
      x1' <- evaluateR x1
      x2' <- evaluateR x2
      reduceM (x1' :=: x2')
  reduceM eq@(App f1 a1 :=: App f2 a2) = do
    eqF <- reduceM (f1 :=: f2)
    eqA <- reduceM (a1 :=: a2)
    case (eqF, eqA) of
      (ReducedToFalse, _) -> error "Impossible"
      (ReducedTo [], ReducedTo []) -> return (ReducedTo [])
      _ -> reduceMFail eq
  reduceM (Lam v1 x1 :=: Lam v2 x2) = do
    new_id <- newIdS
    let new_var = Var $ ZVar new_id Nothing (getType v1) defaultVarClass
    x1' <- evaluateR (App x1 new_var)
    x2' <- evaluateR (App x2 new_var)
    reduceM (x1' :=: x2')
  reduceM eq = reduceMFail eq
    
reduceMFail :: (IdCounter c, MonadReader [ZEquality] m, MonadState c m) => 
  ZEquality -> m (Reduction ZEquality)
reduceMFail eq@(x1 :=: x2) = do
  x1' <- evaluateR x1
  x2' <- evaluateR x2
  if x1' /= x1 || x2' /= x2
    then reduceM (x1' :=: x2')
    else return (ReducedTo [eq])
      

