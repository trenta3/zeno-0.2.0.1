-- |This module, and the corresponding 'Zeno.Isabellable' modules,
-- deal with the conversion a 'ProofSet' into Isabelle/HOL code, outputting this
-- code into a file and then checking this file with Isabelle.
module Zeno.Isabelle (
  toIsabelle
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Proof

import Zeno.Isabellable.Class
import Zeno.Isabellable.Proof
import Zeno.Isabellable.Core

import qualified Data.Map as Map
import qualified Data.Text as Text

instance Isabellable ZProofSet where
  toIsabelle (ProofSet pgm named_proofs) = 
    "theory Zeno\nimports Plain List\nbegin"
    ++ isa_dtypes ++ isa_binds ++ isa_proofs ++ "\n\nend\n"
    where
    flags = programFlags pgm
    (names, proofs) = unzip named_proofs
    names' = map convert names
    
    all_vars = 
      (nubOrd . concatMap (toList . proofGoal)) proofs
      
    isa_proofs = foldl (++) mempty
               $ zipWith namedIsabelleProof names'  proofs
      
    binds = sortBindings binds'
    (dtypes, binds') 
      | flagIsabelleAll flags = 
          ( Map.elems . programDataTypes $ pgm, 
            programBindings $ pgm )
      | otherwise = 
          dependencies pgm all_vars
    
    builtInType dt = show dt `elem`
      ["list", "bool", "(,)", "(,,)", "(,,,)"]
    
    isa_binds = foldl (++) mempty
              . map toIsabelle 
              $ binds
    
    isa_dtypes = foldl (++) mempty
               . map toIsabelle 
               . filter (not . builtInType) 
               $ dtypes


