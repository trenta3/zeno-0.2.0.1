{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Zeno.Type (
  Type (..), Typed (..), PolyTypeVar,
  
  unflattenFunType, unflattenAppType, unflattenForAllType,
  flattenFunType, flattenAppType, flattenForAllType,
  isFunType, isVarType, isAppType, isPolyVarType,
  fromVarType, fromPolyVarType, returnType,
  showTyped
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Id
import Zeno.Unification
import Zeno.Traversing

import qualified Data.Map as Map
import qualified Data.Set as Set

data Type a 
  = VarType !a
  | PolyVarType !PolyTypeVar
  | FunType !(Type a) !(Type a)
  | AppType !(Type a) !(Type a)
  | ForAllType !PolyTypeVar !(Type a)
  deriving ( Eq, Ord, Functor, Foldable, Traversable )

type PolyTypeVar = Id
type TypeSubstitution a = Substitution PolyTypeVar (Type a)

class Typed a where
  type TypeVar a
  getType :: a -> Type (TypeVar a)
  updateType :: TypeSubstitution (TypeVar a) -> a -> a
  
instance Typed (Type a) where
  type TypeVar (Type a) = a
  getType = id
  
  updateType sub (ForAllType var rhs) =
    ForAllType var (updateType sub' rhs)
    where sub' = Map.delete var sub
  updateType sub ty@(PolyVarType var) = 
    fromMaybe ty (Map.lookup var sub) 
  updateType sub (AppType fun arg) =
    AppType (updateType sub fun) (updateType sub arg)
  updateType sub (FunType arg res) =
    FunType (updateType sub arg) (updateType sub res)
  updateType _ ty@(VarType _) = ty
  
unflattenFunType :: [Type a] -> Type a
unflattenFunType ts = foldr1 FunType ts

unflattenAppType :: [Type a] -> Type a
unflattenAppType ts = foldl1 AppType ts

flattenFunType :: Type a -> [Type a]
flattenFunType (FunType f a) = f : flattenFunType a
flattenFunType t = [t]

flattenAppType :: Type a -> [Type a]
flattenAppType (AppType f a) = flattenAppType f ++ [a]
flattenAppType t = [t]

fromVarType :: Type a -> a
fromVarType (VarType x) = x

isPolyVarType :: Type a -> Bool
isPolyVarType (PolyVarType {}) = True
isPolyVarType _ = False

fromPolyVarType :: Type a -> PolyTypeVar
fromPolyVarType (PolyVarType var) = var

isFunType :: Type a -> Bool
isFunType (FunType {}) = True
isFunType _ = False

returnType :: Type a -> Type a
returnType = last . flattenFunType . snd . flattenForAllType

isVarType :: Type a -> Bool
isVarType (VarType {}) = True
isVarType _ = False

isAppType :: Type a -> Bool
isAppType (AppType {}) = True
isAppType _ = False

flattenForAllType :: Type a -> ([PolyTypeVar], Type a)
flattenForAllType (ForAllType var rhs) =
  let (vars, rhs') = flattenForAllType rhs in (var : vars, rhs')
flattenForAllType ty = ([], ty)

unflattenForAllType :: [PolyTypeVar] -> Type a -> Type a
unflattenForAllType = flip (foldl' (flip ForAllType))

showTyped :: (Typed a, Show (TypeVar a), Show a) => a -> String
showTyped a = show a ++ " : " ++ show (getType a)

instance WithinTraversable (Type a) (Type a) where
  mapWithinM f (FunType t1 t2) = 
    f =<< return FunType `ap` mapWithinM f t1 `ap` mapWithinM f t2
  mapWithinM f (AppType t1 t2) = 
    f =<< return AppType `ap` mapWithinM f t1 `ap` mapWithinM f t2
  mapWithinM f (ForAllType var rhs) = 
    f =<< return (ForAllType var) `ap` mapWithinM f rhs
  mapWithinM f t = f t
  
instance WithinTraversable PolyTypeVar (Type a) where
  mapWithinM f = mapWithinM (pvar f) 
    where
    pvar :: Monad m => (PolyTypeVar -> m PolyTypeVar) -> Type a -> m (Type a)
    pvar f (PolyVarType var) = 
      return PolyVarType `ap` f var
    pvar f (ForAllType var rhs) =
      return (flip ForAllType rhs) `ap` f var 
    pvar _ t = return t

instance Ord a => Unifiable (Type a) where
  type Names (Type a) = PolyTypeVar
  unify t1 t2 = runReader (unifyT t1 t2) mempty

unifyT :: forall a . Ord a => Type a -> Type a -> 
  Reader (Set PolyTypeVar) (Unification PolyTypeVar (Type a))
unifyT (ForAllType var t1) t2 =
  local (Set.insert var) (unifyT t1 t2)
unifyT t1 (ForAllType var t2) =
  local (Set.insert var) (unifyT t1 t2)
unifyT t1 t2
  | t1 == t2 = return mempty
  | otherwise =
    case (t1, t2) of
      (FunType a1 r1, FunType a2 r2) ->
        mappend <$> unifyT a1 a2 <*> unifyT r1 r2
      (AppType {}, AppType {}) -> do 
        let (f1 : as1) = flattenAppType t1
            (f2 : as2) = flattenAppType t2
        if f1 == f2 && length as1 == length as2
          then mconcat <$> zipWithM unifyT as1 as2
          else backup
      _ -> backup
  where
  backup = do
    free1 <- freePoly t1
    free2 <- freePoly t2
    return $ if free1
        then Unifier (Map.singleton (fromPolyVarType t1) t2)
      else if free2 
        then Unifier (Map.singleton (fromPolyVarType t2) t1)
      else if isPolyVarType t1
        -- This bit here is bad typing, but since we are not inferring types
        -- I don't think it will affect anything,
        -- and it makes things so much simplier ;)
        then Unifier (Map.singleton (fromPolyVarType t1) t2)
        else NoUnifier 
  
  freePoly :: Ord a => Type a -> Reader (Set PolyTypeVar) Bool
  freePoly (PolyVarType var) = 
    asks (Set.member var)
  freePoly _ = return False

  
instance Show a => Show (Type a) where
  show (VarType var) = show var
  show (PolyVarType id) = show id
  show (ForAllType var rhs) = 
    "forall " ++ show var ++ " . " ++ show rhs
  show (AppType fun arg) = show fun ++ " " ++ show_arg
    where
    show_arg = 
      case arg of
        AppType _ _ -> "(" ++ show arg ++ ")"
        _ -> show arg
  show (FunType arg res) = 
    show_arg ++ " -> " ++ show res
    where 
    show_arg = 
      case arg of 
        FunType _ _ -> "(" ++ show arg ++ ")"
        _ -> show arg
          

