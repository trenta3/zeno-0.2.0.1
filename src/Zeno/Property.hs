module Zeno.Property (
  PropertySet (..), Property, 
  ZProperty, ZPropertySet,
  PropertyCarrier (..),
  filterProperties,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Solver
import Zeno.Evaluation
import Zeno.Proof
import Zeno.Checker

import qualified Data.Map as Map

type ZProperty = Property ZVar
type ZPropertySet = PropertySet ZVar

type Property a = (String, Clause a)

data PropertySet a
  = PropertySet { propsetProgram :: !(Program a),
                  propsetProperties :: ![Property a] }
    
class PropertyCarrier a where
  loadProperties :: Program a -> PropertySet a
  
instance PropertyCarrier ZVar where
  loadProperties pgm = PropertySet pgm' props
    where
    removeBind name = stripModuleName name `elem` map fst props
    removeType name = name `elem` ["Zeno.Prop", "Zeno.Equals"]
    
    pgm' = flip execState pgm 
      $ removeBindingsBy removeBind 
        >> removeDataTypesBy removeType 
    
    props = id
      . sortWith fst
      . mapMaybe clausify
      . concatMap flattenBindings
      . programBindings
      $ pgm

filterProperties :: (String -> Bool) -> PropertySet a -> PropertySet a
filterProperties p (PropertySet pgm props) = 
  PropertySet pgm (filter p' props)
  where p' (n, _) = p n
  
instance Show a => Show (PropertySet a) where
  show (PropertySet _ props) =
    concatMap (("\n" ++) . showProperty) props
    where 
    showProperty (name, cls) = 
      name ++ " : \"" ++ show cls ++ "\""
  

