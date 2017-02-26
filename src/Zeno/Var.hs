-- |Here we have the representation of variables inside Zeno; see 'ZVarClass' for the
-- different types of variable we can have.
module Zeno.Var (
  ZVar (..), ZVarClass (..), HasSources (..),
  ZDataType, ZType, ZExpr, ZTerm, ZAlt, 
  ZBinding, ZBindings, ZClause, ZExprSubstitution,
  ZEquality, ZHypothesis, ZQuantified, ZProgram,
  CriticalPath, CriticalTerm, 
  substituteTakingSources,
  defaultVarClass, isConstructorVar, isConstructorTerm,
  isUniversalVar, isDefinedVar,
  universalVariables, freeUniversalVariables,
  freshVariable,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.DataType
import Zeno.Type
import Zeno.Id
import Zeno.Expression
import Zeno.Clause
import Zeno.Utils
import Zeno.Program
import Zeno.Unification
import Zeno.Traversing

import qualified Data.Map as Map

type ZProgram = Program ZVar
type ZDataType = DataType ZVar
type ZType = Type ZDataType
type ZExpr = Expr ZVar
type ZTerm = Term ZVar
type ZAlt = Alt ZVar
type ZBindings = Bindings ZVar
type ZBinding = Binding ZVar
type ZClause = Clause ZVar
type ZEquality = Equality ZVar
type ZQuantified = Quantified Clause ZVar
type ZHypothesis = Hypothesis ZVar
type ZExprSubstitution = ExprSubstitution ZVar

data ZVar
  = ZVar        { varId :: !Id,
  
                  varName :: !(Maybe String),
                  
                  -- |The variable's 'Type'. This is non-strict so that we can tie the
                  -- knot for "variables have types which are made of data-types which
                  -- have constructors which are variables".
                  varType :: ZType,
                  
                  varClass :: !ZVarClass }

instance Eq ZVar where
  (==) = (==) `on` varId
  
instance Ord ZVar where
  compare = compare `on` varId
    
instance Show ZVar where
  show var = case varName var of
    Just name -> 
      let name' = stripModuleName name
      in if "$c" `isPrefixOf` name'
        then drop 2 name'
        else name' 
    Nothing -> "_" ++ show (varId var)
    where
    srs = case allSources var of
      [] -> ""
      srs -> "{" ++ (intercalate "," . map show) srs ++ "}"

-- |The different /classes/ of variable within Zeno.
data ZVarClass
  -- |A 'UniversalVar' is one used in theorem proving
  -- and hence is under universal quantification.
  = UniversalVar    { varSources :: ![CriticalPath] }
  
  | ConstructorVar  { isRecursiveConstructor :: !Bool }
  
  -- |A variable defined with a 'Let'.                    
  | DefinedVar      { 
                      -- |The definition of a variable will be 'Nothing' until its 'Let'
                      -- binding has been evaluated. Hence, top-level functions 
                      -- should not have a 'Nothing' definition.
                      varDefinition :: !(Maybe ZExpr),
                      
                      -- |Whether this was defined with recursive 'Let' 'Bindings'.
                      isRecursiveDefinition :: !Bool }
  deriving ( Eq )

type CriticalPath = [Id]
type CriticalTerm = (ZTerm, CriticalPath)

instance Typed ZVar where
  type TypeVar ZVar = ZDataType
  getType = varType
  updateType sub var = var
    { varType = updateType sub (varType var) }
  
instance Typed ZExpr where
  type TypeVar ZExpr = ZDataType

  updateType sub = fmap (updateType sub)

  getType Err = PolyVarType reservedId
  getType (Var v) = getType v
  getType (Let _ rhs) = getType rhs
  getType (Cse _ _ alts) = getType . altExpr . head $ alts
  getType (Lam var rhs) = FunType (getType var) (getType rhs)
  getType expr@(App lhs rhs) = updateType type_sub lhs_res
    where
    FunType lhs_arg lhs_res = snd (flattenForAllType (getType lhs))
    type_sub = case unify lhs_arg (getType rhs) of
      Unifier sub -> sub
      NoUnifier -> error
        $ "Could not unify types in term application."
        ++ "\n" ++ showTyped lhs
        ++ "\nand"
        ++ "\n" ++ showTyped rhs
        
defaultVarClass :: ZVarClass
defaultVarClass = UniversalVar []

isConstructorVar :: ZVar -> Bool
isConstructorVar (varClass -> ConstructorVar {}) = True
isConstructorVar _ = False

isConstructorTerm :: ZExpr -> Bool
isConstructorTerm = 
  fromMaybe False . fmap isConstructorVar . termFunction 

isUniversalVar :: ZVar -> Bool
isUniversalVar (varClass -> UniversalVar {}) = True
isUniversalVar _ = False

isDefinedVar :: ZVar -> Bool
isDefinedVar (varClass -> DefinedVar {}) = True
isDefinedVar _ = False

freshVariable :: (Monad m, IdCounter s) => ZVar -> StateT s m ZVar
freshVariable (ZVar id _ typ cls) = do
  new_id <- newIdS
  return (ZVar new_id Nothing typ cls)
      
universalVariables :: Foldable f => f ZVar -> [ZVar]
universalVariables = nubOrd . filter isUniversalVar . toList

freeUniversalVariables :: (WithinTraversable ZExpr (f ZVar), Foldable f) =>
  f ZVar -> [ZVar]
freeUniversalVariables = filter isUniversalVar . freeVariables

class HasSources a where
  allSources :: a -> [CriticalPath]
  addSources :: [CriticalPath] -> a -> a
  clearSources :: a -> a
  
instance HasSources ZVar where
  allSources (varClass -> UniversalVar srs) = srs
  allSources _ = []

  addSources more var@(varClass -> UniversalVar existing) =
    var { varClass = UniversalVar (more ++ existing) }
  addSources _ var = var
  
  clearSources var@(varClass -> UniversalVar _) =
    var { varClass = UniversalVar [] }
  clearSources var = var
  
instance (Foldable f, Functor f) => HasSources (f ZVar) where
  {-# SPECIALISE instance HasSources ZExpr #-}
  allSources = concatMap allSources . nubOrd . toList
  addSources srs = fmap (addSources srs)
  clearSources = fmap clearSources
  
substituteTakingSources :: (Ord a, WithinTraversable a f, HasSources a) => 
    Substitution a a -> f -> f
{-# SPECIALISE substituteTakingSources :: 
      ZExprSubstitution -> ZExpr -> ZExpr #-}
substituteTakingSources sub = mapWithin $ \from ->
  case Map.lookup from sub of
    Nothing -> from
    Just to -> addSources (allSources from) to

