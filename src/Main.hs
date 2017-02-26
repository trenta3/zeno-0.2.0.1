module Main where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.HaskellParser
import Zeno.Evaluation
import Zeno.Proof
import Zeno.Checker
import Zeno.Solver
import Zeno.Isabelle
import Zeno.Property
import Zeno.Flags

import Control.Parallel.Strategies
import Data.IORef
import System.IO.Unsafe
import System.IO
import System.Process
import System.Directory
import System.Exit
import System.Environment
import System.Timeout
import Text.Printf

import qualified Data.Map as Map
import qualified Data.Text.IO as Text

header :: String
header = "Zeno 0.2 - An automated theorem prover for Haskell programs."
  ++ "\nDeveloped at Imperial College London by "
  ++ "William Sonnex, Sophia Drossopoulou and Susan Eisenbach."
  ++ "\nhttp://www.haskell.org/haskellwiki/Zeno"

main :: IO ()
main = do  
  !flags <- readFlags <$> getArgs
  props <- loadProperties <$> loadHaskell flags
  zeno props

zeno :: ZPropertySet -> IO ()
zeno (PropertySet !pgm !props') = zenoTimeout $ do
  putStr header >> hFlush stdout
  
  when (flagPrintCore flags) $ do
    putStr "\n\nProgram Code:\n"
    print pgm
    putStr "\n\nDefined Properties:\n"
    forM_ props (putStrLn . showProperty)
    exitWith ExitSuccess
    
  unless (not (null props) 
      || (flagSkipChecker flags && flagSkipSolver flags)) $ do
    putStr "\n\nNo properties found."
    
  unless (null props || flagSkipChecker flags) $ do
    putStr "\n\nSearching for counter-examples... "
    hFlush stdout
    if null falses
      then putStr "None found."
      else do
        forM_ falses $ \(sub, prop) -> 
          printf "\nDisproved \"%s\"\n  with %s" 
            (showProperty prop) (showSubstitution sub)
    
  unless (null props || flagSkipSolver flags) $ do
    putStr "\n\nSearching for proofs... "
    hFlush stdout
    let proofs = proofsetProofs proofset
    if null proofs
      then putStr "None found."
      else do
        let showProp (name, proof) = showProperty (name, proofGoal proof)
            props = map showProp proofs 
        forM_ props (printf "\nProved \"%s\"")

  unless (null unknowns
      || (flagSkipSolver flags && flagSkipChecker flags)) $ do
    putStr "\n\nCould neither prove nor disprove: "
    let props = map showProperty unknowns
    forM_ props (printf "\n\"%s\"")
    
  when (flagWebMode flags) $ do
    putStrLn "\n\n\nIsabelle/HOL proofs:\n"
    Text.putStr proofs_code

  when (not (flagWebMode flags) 
      && (not (null proven) || flagIsabelleAll flags)) $ do
    createDirectoryIfMissing True output_dir
    writeFile ml_path ml_code
    Text.writeFile proofs_path proofs_code
    printf "\n\nZeno output at \"%s\"." proofs_path
    
    unless (flagSkipIsabelle flags) $ do
      putStr "\nChecking with Isabelle... "
      hFlush stdout
      (exitcode, isa_out, isa_err) <- 
        readProcessWithExitCode "isabelle" ["usedir", "HOL", output_dir] ""
      case exitcode of
        ExitSuccess -> putStr "Done."
        ExitFailure _ -> printf "Failed.%s" isa_err
  
  printf "\n"
  where
  zenoTimeout :: IO () -> IO ()
  zenoTimeout io
    | flagTimeout flags <= 0 = io
    | otherwise = do
        maybe_io <- timeout (flagTimeout flags * (10^6)) io
        case maybe_io of
          Nothing -> putStrLn 
            $ "\nTimed out (" ++ (show . flagTimeout) flags ++ "s)"
          _ -> return ()
          
  props 
    | null matches = props'
    | otherwise = flip filter props'
        $ \(n, _) -> any (`isInfixOf` n) matches
  
  showProperty (name, cls) = 
    name ++ " : " ++ show cls ++ ""
  
  flags = programFlags pgm
  matches = flagMatchWith flags
  
  output_dir = flagIsabelleDir flags
  ml_code = "use_thys [\"Zeno\"]"
  ml_path = output_dir ++ "/ROOT.ML"
  proofs_path = output_dir ++ "/Zeno.thy"
  proofs_code = toIsabelle proofset
  
  counter_exs 
    | flagSkipChecker flags = repeat Nothing
    | otherwise = withStrategy (parList rseq) 
        . flip runReader pgm
        $ mapM (falsify . snd) props
        
  (falses', to_prove') = partition (isJust . fst) (counter_exs `zip` props)
  to_prove = map snd to_prove'
  falses = map (first fromJust) falses'
  
  maybe_proofs 
    | flagSkipSolver flags = repeat Nothing
    | otherwise = withStrategy (parList rseq)
        $ map (solve pgm . snd) to_prove
    
  maybe_proven = to_prove `zip` maybe_proofs
  (proven, unproven) = partition (isJust . snd) maybe_proven
  
  proofs = flip map proven
    $ \((name, _), Just prf) -> (name, prf)
  proofset = ProofSet pgm proofs
  
  unknowns = flip map unproven
    $ \(prop, Nothing) -> prop

