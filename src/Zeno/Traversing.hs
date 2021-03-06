module Zeno.Traversing (
  WithinTraversable (..), Substitution,
  mapWithin, substitute,
  replaceWithin, replaceManyWithin, 
  withinList, strictlyWithinList,
  contains, containsStrictly,
  removeSupersets, removeSubsets,
  showSubstitution
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Utils

import qualified Data.Map as Map
import qualified Data.Set as Set

type Substitution = Map

showSubstitution :: (Show k, Show v) => Substitution k v -> String
showSubstitution (Map.toList -> subs) =
  "[ " ++ (intercalate "; " . map showSub) subs ++ " ]"
  where showSub (k, v) = show k ++ " -> " ++ show v

class WithinTraversable t f where
  mapWithinM :: Monad m => (t -> m t) -> f -> m f
  
instance Traversable f => WithinTraversable a (f a) where
  mapWithinM = mapM
  
substitute :: (WithinTraversable a f, Eq a) => 
  Substitution a a -> f -> f
substitute map = replaceManyWithin (Map.toList map)

isOneToOne :: Ord b => Substitution a b -> Bool
isOneToOne = not . containsDuplicates . Map.elems
  
mapWithin :: WithinTraversable t f => (t -> t) -> f -> f
mapWithin = mapM_to_fmap mapWithinM

anyWithin :: forall t f .  WithinTraversable t f => (t -> Bool) -> f -> Bool
anyWithin p = getAny . execWriter . mapWithinM tellAny
  where
  tellAny :: t -> Writer Any t
  tellAny t | p t = tell (Any True) >> return t
            | otherwise = return t

replaceWithin :: (WithinTraversable t f, Eq t) => t -> t -> f -> f
replaceWithin = genericReplace mapWithin

replaceManyWithin :: (Foldable f, WithinTraversable a t, Eq a) => 
  f (a, a) -> t -> t
replaceManyWithin = genericReplaceMany mapWithin

withinList :: WithinTraversable t f => f -> [t]
withinList = execWriter . mapWithinM (\t -> tell [t] >> return t)

strictlyWithinList :: (WithinTraversable t t, Eq t) => t -> [t]
strictlyWithinList t = filter (/= t) (withinList t)

contains :: (WithinTraversable t f, Eq t) => f -> t -> Bool
contains f = flip elem (withinList f)

containsStrictly :: (WithinTraversable t t, Eq t) => t -> t -> Bool
containsStrictly t = flip elem (strictlyWithinList t)

removeSubsets :: (WithinTraversable a a, Eq a) => [a] -> [a]
removeSubsets sets = filter (not . isSubset) sets
  where isSubset set = any (flip containsStrictly set) sets

removeSupersets :: (WithinTraversable a a, Eq a) => [a] -> [a]
removeSupersets sets = filter (not . isSuperset) sets
  where isSuperset set = any (containsStrictly set) sets
  
