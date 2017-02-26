module Zeno.Unification (
  Unifiable (..), Unification (..), 
  applyUnification, mergeUnifiers, allUnifiers,
) where 

import Prelude ()
import Zeno.Prelude
import Zeno.Utils
import Zeno.Traversing

import qualified Data.Map as Map

-- |The result of trying to unify two values where
-- 'NoUnifier' indicates that unification was impossible,
-- This is essentially 'Maybe (Substitution n a)'.
data Unification n a 
  = Unifier !(Substitution n a)
  | NoUnifier

-- |Values which can be unified
class Unifiable a where
  type Names a
  unify :: a -> a -> Unification (Names a) a
  
-- |Appending two unifiers will create a unifier that will
-- perform both unifications, if such a unifier is still valid.
instance (Ord a, Eq b) => Monoid (Unification a b) where
  mempty = Unifier mempty

  mappend NoUnifier _ = NoUnifier
  mappend _ NoUnifier = NoUnifier
  mappend (Unifier left) (Unifier right)
    | and (Map.elems inter) = Unifier (Map.union left right)
    | otherwise = NoUnifier
    where inter = Map.intersectionWith (==) left right
 
-- |This is like 'catMaybes'
mergeUnifiers :: [Unification a b] -> [Substitution a b]
mergeUnifiers = foldl' addUni []
  where addUni subs NoUnifier = subs
        addUni subs (Unifier sub) = sub : subs
        
applyUnification :: (WithinTraversable a f, Eq a) =>
  Unification a a -> f -> f
applyUnification NoUnifier = id
applyUnification (Unifier sub) = substitute sub

allUnifiers :: (Unifiable a, WithinTraversable a f, Eq a) => 
  a -> f -> [Substitution (Names a) a]
allUnifiers from = mergeUnifiers . execWriter . (mapWithinM unifiers)
  where unifiers to = tell [unify from to] >> return to 
  
