{-# LANGUAGE UndecidableInstances, DeriveFunctor, 
             DeriveFoldable, DeriveTraversable #-}
module Zeno.Program (
  Program (..), emptyProgram,
  addDataType, addBindings, 
  removeBindingsBy, removeDataTypesBy
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Expression
import Zeno.DataType
import Zeno.Type
import Zeno.Id
import Zeno.Flags

import qualified Data.Map as Map

data Program a
  = Program     { programBindings :: ![Bindings a],
                  programFunctions :: !(Map String (Expr a)),
                  programDataTypes :: !(Map String (DataType a)),
                  programCounter :: !Id,
                  programFlags :: !ZenoFlags }
  deriving ( Functor, Foldable, Traversable )
                  
instance IdCounter (Program a) where
  newId pgm = 
    let id = nextId (programCounter pgm)
    in (id, pgm { programCounter = id })
    
  largestId = programCounter
  
emptyProgram :: ZenoFlags -> Program a
emptyProgram flags
  = Program    { programBindings = mempty,
                 programFunctions = mempty,
                 programDataTypes = mempty,
                 programCounter = mempty,
                 programFlags = flags }
                           
addDataType :: MonadState (Program a) m => DataType a -> m ()
addDataType dtype@(DataType _ name _ _) = modify $ \z -> z 
  { programDataTypes = Map.insert name dtype (programDataTypes z) }
  
addBindings :: (Show a, MonadState (Program a) m) => Bindings a -> m ()
addBindings binds = modify $ \z -> z 
  { programBindings = (programBindings z) ++ [binds], 
    programFunctions = insertAll flat (programFunctions z) }
  where
  flat = map (first show)
       $ flattenBindings binds
  
  insertAll :: Ord k => [(k, v)] -> Map k v -> Map k v
  insertAll = flip (foldl' (flip (uncurry Map.insert)))
  
removeDataTypesBy :: (Show a, MonadState (Program a) m) => 
   (String -> Bool) -> m ()
removeDataTypesBy check = modify $ \z -> z
  { programDataTypes = Map.filterWithKey (flip $ const (not . check)) 
      (programDataTypes z) }
  
removeBindingsBy :: (Show a, MonadState (Program a) m) => 
    (String -> Bool) -> m ()
removeBindingsBy check = modify $ \z -> z
  { programFunctions = Map.filterWithKey (flip $ const (not . check))
      (programFunctions z),
    programBindings = filter filterer (programBindings z) }
  where
  filterer (boundVars -> []) = False
  filterer (boundVars -> [var]) = not . check . show $ var
  filterer _ = True

instance (Typed a, TypeVar a ~ DataType a, Show a) => Show (Program a) where
  show zeno = dtypes ++ binds
    where
    binds = (concatMap show . programBindings) zeno
    dtypes = (concatMap showDataType . Map.elems . programDataTypes) zeno
