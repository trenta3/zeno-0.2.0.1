-- |This module re-exports all of the modules that make up the /core/ of Zeno.
-- It also contains a lot of miscellaneous code that doesn't really belong anywhere
-- in particular.
module Zeno.Core (
  module Zeno.Type,
  module Zeno.DataType,
  module Zeno.Clause,
  module Zeno.Var,
  module Zeno.Expression,
  module Zeno.Id,
  module Zeno.Utils,
  module Zeno.Program,
  module Zeno.Unification,
  module Zeno.Traversing,
  module Zeno.Flags,
  
  ConstructorInstance, recursiveConstructorInstance,
  instantiateConstructors, mergeCriticalTerms,
  destructibleType, destructibleTerm, destructibleVar,
  dependencies, sortBindings,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Type
import Zeno.Expression
import Zeno.Clause
import Zeno.Var
import Zeno.DataType
import Zeno.Id
import Zeno.Utils
import Zeno.Traversing
import Zeno.Unification
import Zeno.Program
import Zeno.Flags

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |The return value from 'instantiateConstructors',
-- 'fst' is the instantiated constructor term,
-- 'snd' is the list of recursive variables in that term.
type ConstructorInstance = (ZTerm, [ZVar])

destructibleType :: Type a -> Bool
destructibleType = isVarType . head . flattenAppType

destructibleTerm :: ZTerm -> Bool
destructibleTerm term 
   = isTerm term
  && destructibleType (getType term)
  && notConstructor
  where
  notConstructor = fromMaybe False $ do
    fun <- termFunction term
    return (not (isConstructorVar fun))
  
destructibleVar :: ZVar -> Bool
destructibleVar = destructibleTerm . Var

recursiveConstructorInstance :: ConstructorInstance -> Bool
recursiveConstructorInstance (term, _) =
  case termFunction term of
    Just var -> isConstructorVar var 
             && isRecursiveConstructor (varClass var)
    Nothing -> False

proofCriticalTerm :: CriticalTerm -> Bool
proofCriticalTerm (term, src) =
  destructibleTerm term
  && not (null src || any invalid (allSources term))
  where
  invalid :: CriticalPath -> Bool
  invalid = orderedSupersetOf src

instantiateConstructors :: forall t m . (IdCounter t, MonadState t m) =>
    CriticalTerm -> m [ConstructorInstance]
instantiateConstructors (term, source) = mapM instantiate dt_cons
  where                          
  term_type = getType term
  VarType dtype@(DataType _ _ _ dt_cons) = 
    head (flattenAppType term_type)
  
  instantiate :: ZVar -> m ConstructorInstance
  instantiate con = do
    new_ids <- replicateM (length arg_types) newIdS
    let makeVar new_id new_type = ZVar new_id Nothing new_type var_class
        args = zipWith ($) (map makeVar new_ids) arg_types
        term = unflattenApp (map Var (con' : args))
        vars = filter ((== res_type) . varType) args
        
    let update :: (Typed a, TypeVar a ~ ZDataType) => a -> a
        update = conUnifier term
        
    return (update term, map update vars)
    where
    conUnifier :: (Typed a, TypeVar a ~ ZDataType) => ZTerm -> a -> a 
    conUnifier con_term = 
      case unify new_con_type term_type of
        NoUnifier -> error $
          "Couldn't unify types in constructor instantiation."
          ++ "\nTerm: " ++ showTyped term
          ++ "\nConstructor: " ++ showTyped con
        Unifier sub -> updateType sub
      where 
      new_con_type = unflattenForAllType poly_vars (getType con_term)

    (poly_vars, con_type) = flattenForAllType (getType con)
    flat_con_types = flattenFunType con_type
    (arg_types, [res_type]) = splitAt (length flat_con_types - 1) flat_con_types
    var_class = UniversalVar [source]
    con' = con { varType = con_type }
    
mergeCriticalTerms :: [CriticalTerm] -> [CriticalTerm] 
mergeCriticalTerms cterms = filterEach requiredSource `concatMap` clustered
  where
  clustered = clusterBy ((==) `on` fst) cterms

  requiredSource :: (CriticalTerm, [CriticalTerm]) -> Bool
  requiredSource ((_, src), other_terms) 
    = not 
    $ any (flip orderedSupersetOf src) 
    $ map snd 
    $ other_terms
 

data DS
  = DS    { dsVisited :: Set ZVar,
            dsDataTypes :: Set ZDataType,
            dsBindings :: [ZBindings] }

emptyDS :: DS
emptyDS = DS mempty mempty mempty

dependencies :: ZProgram -> [ZVar] -> ([ZDataType], [ZBindings])
dependencies pgm vars = (ds_dtypes, ds_binds)
  where
  ds = execState (mapM_ depends vars) emptyDS
  ds_binds = dsBindings ds
  ds_dtypes = Set.toList (dsDataTypes ds)
  
  bindingsDepend :: ZBindings -> State DS ()
  bindingsDepend binds = do
    modify $ \ds -> ds
      { dsVisited = foldr Set.insert (dsVisited ds) vars,
        dsBindings = binds : dsBindings ds }
    mapM_ depends 
      . nubOrd
      . concatMap toList
      $ exprs
    where
    (vars, exprs) = unzip (flattenBindings binds)
  
  depends :: ZVar -> State DS ()
  depends var = case varClass var of
    ConstructorVar {} -> do
      let VarType dtype = id
            . head . flattenAppType
            . last . flattenFunType 
            . snd . flattenForAllType
            . varType $ var
      modify $ \ds -> ds 
        { dsDataTypes = Set.insert dtype (dsDataTypes ds) }
        
    DefinedVar (Just _) _ -> do
      visited <- gets dsVisited
      if var `Set.member` visited
        then return ()
        else case Map.lookup var bindings of
          Nothing -> error
            $ "Proof depends upon an internally defined function \""
            ++ show var ++ "\" and "
            ++ "hence cannot be converted for checking by a proof assistant." 
          Just binds -> bindingsDepend binds 
          
    _ -> return ()
          
  bindings :: Map ZVar ZBindings
  bindings = Map.unions  
           . map bindingMap
           . programBindings $ pgm

  bindingMap :: ZBindings -> Map ZVar ZBindings
  bindingMap binds =
    Map.fromList $ zip (boundVars binds) (repeat binds) 
    
-- |This function will sort a list of bindings in dependence order.
-- Bindings will only ever depend on those before them in the ordering.
sortBindings :: [ZBindings] -> [ZBindings]
sortBindings binds = sortBy dependency binds
  where
  -- This code turns the "calls" ordering, 
  -- defined when one binding set calls another,
  -- into a total order by computing its transitive closure.
  
  call_map = foldl' (flip bindingCalls) mempty 
           $ concatMap flattenBindings binds
  all_vars = Map.keys call_map
  closure_map = Map.fromList 
    $ all_vars `zip` map (closure mempty) all_vars
           
  closure :: Set ZVar -> ZVar -> Set ZVar
  closure old_set var
    | var `Set.member` old_set = old_set
    | otherwise = new_set
      where
      new_vars = fromJust (Map.lookup var call_map)
      new_set = foldl' closure (Set.insert var old_set) new_vars
      
  totalClosure :: [ZVar] -> Set ZVar
  totalClosure = id 
    . Set.unions
    . map (fromJust . flip Map.lookup closure_map) 
    
  bindingCalls :: ZBinding -> Map ZVar (Set ZVar) -> Map ZVar (Set ZVar)
  bindingCalls (var, expr) map = Map.insert var new_set map
    where
    calls = Set.filter isDefinedVar
          . Set.fromList
          . toList
          $ expr
    old_set = (fromMaybe mempty . Map.lookup var) map
    new_set = old_set `Set.union` calls
                                                                         
  dependency :: ZBindings -> ZBindings -> Ordering
  dependency left right
    | left_overlap = LT
    | right_overlap = GT
    | otherwise = compare left_names right_names
    where
    left_names = boundVars left
    right_names = boundVars right
    left_closure = totalClosure left_names
    right_closure = totalClosure right_names
    
    left_overlap = not . Set.null 
      $ Set.intersection (Set.fromList left_names) right_closure
    right_overlap = not . Set.null 
      $ Set.intersection (Set.fromList right_names) left_closure

