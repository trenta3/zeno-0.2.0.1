{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Zeno.Proof (
  Proof (..), ProofStep (..), ProofSet (..),
  ZProof, ZProofStep, ZProofSet,
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import qualified Data.Map as Map

type ZProof = Proof ZVar
type ZProofStep = ProofStep ZVar
type ZProofSet = ProofSet ZVar

data Proof a
  = Proof  { proofStep :: !(ProofStep a),
             proofGoal :: !(Clause a),
             proofHypotheses :: ![Hypothesis a] }
  deriving ( Eq, Functor, Foldable, Traversable )
 
data ProofStep a
  = Eql
  | Con
  | Sim !(Proof a)
  | Fac ![Proof a]
  | Gen !(Term a) !a !(Proof a)
  | Ind !a ![a] ![(Term a, Proof a)]
  | Csp !(Term a) ![(Term a, Proof a)]
  | Hyp !(Hypothesis a) !(Proof a)
  | Hcn !(Hypothesis a) !(Proof a)
  | Icn !(Equality a) !(Proof a) !(Proof a)
  deriving ( Eq, Functor, Foldable, Traversable )
  
data ProofSet a
  = ProofSet  { proofsetProgram :: !(Program a),
                proofsetProofs :: ![(String, Proof a)] }
  deriving ( Functor, Foldable, Traversable )

instance Show a => Show (Proof a) where
  show = runIndented . showProof

showProof :: forall a . Show a => Proof a -> Indented String
showProof (Proof step cls@(Clause (eq_l :=: eq_r) _) _) = do
  step' <- showStep step
  i <- indentation
  return $ i ++ "| " ++ show cls ++ " " ++ step'
  where
  showStep :: ProofStep a -> Indented String
  showStep Eql = return "[eql]"
  showStep Con = return "[con]"
  
  showStep (Sim proof) = do
    prf <- showProof proof
    return $ 
      "[sim]" ++ prf
  
  showStep (Fac proofs) =
    (if length proofs == 1 then id else indent) $ do
      prfs <- intercalate "\n" <$> mapM showProof proofs
      return $
        "[fac]" ++ prfs
    
  showStep (Gen term var proof) = do
    prf <- showProof proof 
    return $
      "[gen " ++ show term ++ " => " ++ show var ++ "]" ++ prf
    
  showStep (Hyp hyp proof) = do
    prf <- showProof proof
    return $
      "[hyp " ++ show (hypId hyp) ++ "]" ++ prf
    
  showStep (Hcn hyp proof) = do
    prf <- showProof proof
    return $
      "[hcn " ++ show (hypId hyp) ++ "]" ++ prf 
    
  showStep (Csp term cses) = 
    (if length cses == 1 then id else indent) $ do
      prfs <- intercalate "\n" <$> mapM (showProof . snd) cses
      return $
        "[cse " ++ show term ++ "]" ++ prfs
      
  showStep (Icn term proof1 proof2) = indent $ do
    prf1 <- showProof proof1
    prf2 <- showProof proof2
    return $
      "[icn " ++ show term ++ "]" ++ prf1 ++ "\n" ++ prf2
      
  showStep (Ind var _ cses) = 
    (if length cses == 1 then id else indent) $ do
      prfs <- intercalate "\n" <$> mapM (showProof . snd) cses
      return $
        "[ind " ++ show var ++ "]" ++ prfs
    
