{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Zeno.DataType (
  DataType (..), showDataType,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Id
import Zeno.Type
import Zeno.Utils ( stripModuleName )

data DataType a
  = DataType    { dataTypeId :: !Id,
                  dataTypeName :: !String,
                  dataTypeArgs :: ![PolyTypeVar],
                  dataTypeCons :: ![a] }
  deriving ( Functor, Foldable, Traversable ) 

instance Show (DataType a) where
  show = stripModuleName . dataTypeName
  
instance Eq (DataType a) where
  (==) = (==) `on` dataTypeId
  
instance Ord (DataType a) where
  compare = compare `on` dataTypeId

-- |Use when you want the full description of a data-type, as 'show' will just
-- output its name.
showDataType :: (Typed a, Show a, TypeVar a ~ DataType a) => DataType a -> String
showDataType (DataType _ name args cons) =
  "\ntype " ++ stripModuleName name ++ concatMap ((" " ++) . show) args ++ 
  " where" ++ concatMap (("\n  " ++) . showTyped) cons ++ "\n"
  

