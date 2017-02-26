module Zeno.Isabellable.Class (
  Isabellable (..), quote, convert
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Utils
import Zeno.Flags

import qualified Data.Text as Text

class Isabellable a where
  toIsabelle :: a -> Text
  toIsabelle = runIndented . toIsabelleI
  
  toIsabelleI :: a -> Indented Text
  toIsabelleI = return . toIsabelle
  
quote :: Text -> Text
quote txt 
  | any (`Text.isInfixOf` txt) [" ", "(", ")"] = "\"" ++ txt ++ "\""
  | otherwise = txt

convert :: String -> String
convert = replace '.' '_'
        . replace ':' '_'
        . stripModuleName
