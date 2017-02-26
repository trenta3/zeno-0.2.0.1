module Zeno.Flags (
  ZenoFlags (..), readFlags, defaultFlags
) where

import Prelude ()
import Zeno.Prelude
import System.Console.GetOpt

defaultIsabelleDir :: String
defaultIsabelleDir = "isa"

data ZenoFlags 
  = ZenoFlags { flagVerboseProof :: !Bool,
                flagPrintCore :: !Bool,
                flagKeepModuleNames :: !Bool,
                flagSkipChecker :: !Bool,
                flagSkipSolver :: !Bool,
                flagSkipIsabelle :: !Bool,
                flagIsabelleAll :: !Bool,
                flagWebMode :: !Bool,
                flagIncludeDirs :: ![String],
                flagIsabelleDir :: !String,
                flagMatchWith :: ![String],
                flagHaskellFiles :: ![String],
                flagTimeout :: !Int }
  
defaultFlags :: ZenoFlags
defaultFlags 
  = ZenoFlags { flagVerboseProof = False,
                flagPrintCore = False,
                flagKeepModuleNames = False,
                flagSkipChecker = False,
                flagSkipSolver = False,
                flagSkipIsabelle = False,
                flagIsabelleAll = False,
                flagWebMode = False,
                flagIncludeDirs = [],
                flagIsabelleDir = defaultIsabelleDir,
                flagMatchWith = [],
                flagHaskellFiles = [],
                flagTimeout = 0 }
                
readFlags :: [String] -> ZenoFlags
readFlags args 
  | not (null errors) = error (concat errors ++ usage) 
  | null (flagHaskellFiles flags) = 
      error ("No Haskell filenames specified!\n\n" ++ usage)
  | otherwise = flags
  where
  header = "Usage: zeno [OPTION] [FILENAME]"
  
  examples = "\n\nExamples:"
    ++ "\n\nzeno *"
    ++ "\n  Attempts to prove or disprove every property in every file "
    ++ "(ending in .hs or .lhs) in the current directory."
    ++ "\n\nzeno -m prop Test.hs"
    ++ "\n  Attempts to prove or disprove every property "
    ++ "with the text \"prop\" in its name in the file \"Test.hs\" or its imports."
    ++ "\n\nzeno -S Test.hs"
    ++ "\n  Disables the solver and hence runs Zeno as just a "
    ++ "counter-example finder on every property in \"Test.hs\"."
    ++ "\n\nzeno -CSa -o test Test.hs Test2.hs"
    ++ "\n  Uses Zeno as a Haskell-to-Isabelle conversion tool on the code in "
    ++ "\"Test.hs\" and \"Test2.hs\", outputting it to the directory \"test\""
    ++ "\n"
  
  usage = usageInfo (header ++ examples) options
  
  (flag_funs, [], errors) =  
    getOpt (ReturnInOrder hsFile) options args
    
  hsFile n f 
    | ".hs" `isSuffixOf` n || ".lhs" `isSuffixOf` n = 
        f { flagHaskellFiles = n : flagHaskellFiles f }
    | otherwise = f
    
  flags = foldl' (flip ($)) defaultFlags flag_funs

options :: [OptDescr (ZenoFlags -> ZenoFlags)]
options = [ 
  Option ['m'] ["match"] 
    (ReqArg (\m f -> f { flagMatchWith = m : flagMatchWith f }) "TEXT")
     $ "Only consider properties which contain this string. "
    ++ "This argument may be given multiple times, in which case Zeno considers "
    ++ "properties containing any of the given strings.",
{-
  Option ['v'] ["verbose"] (NoArg $ \f -> f { flagVerboseProof = True }) 
     $ "Enables verbose Isabelle proof output, adding a "
    ++ "comment to every step that Zeno has made in constructing a proof.",
-}    
  Option ['c'] ["print-core"] (NoArg $ \f -> f { flagPrintCore = True })
     $ "Prints the internal representation of any Haskell code that Zeno has loaded "
    ++ "along with any properties defined, then terminates Zeno. "
    ++ "This code Zeno uses has been through the GHC simplifier so may be "
    ++ "slightly different to the code you originally wrote. "
    ++ "If you are wondering why Zeno cannot work with a certain "
    ++ "function definition it might be worth checking how it came out here.",
{-
  Option ['q'] ["qualify"] (NoArg $ \f -> f { flagKeepModuleNames = True })
     $ "Stops Zeno from stripping modules from the beginning of names within your "
    ++ "program. Module names are removed by default for clarity, and will not affect "
    ++ "the Zeno system itself, but may cause naming clashes in the "
    ++ "Isabelle code that Zeno outputs.",
-}  
  Option ['C'] ["no-check"] (NoArg $ \f -> f { flagSkipChecker = True })
     $ "Stops Zeno from running its counter-example finder (think SmallCheck but "
    ++ "worse) on properties. Not sure why you'd want to turn this off but "
    ++ "who am I to judge.",
    
  Option ['S'] ["no-solve"] (NoArg $ \f -> f { flagSkipSolver = True })
     $ "Stops Zeno from attempting to prove properties. Might be useful if you "
    ++ "just wanted to run the counter-example finder.",
    
  Option ['I'] ["no-isa"] (NoArg $ \f -> f { flagSkipIsabelle = True })
     $ "Stops Zeno from automatically invoking Isabelle on any programs or proofs that "
    ++ "it outputs. Maybe Isabelle is hanging (Zeno could probably put the simplifier "
    ++ "into a loop with the right input), maybe you'd rather just fire up Emacs "
    ++ "and run through the proofs yourself, or maybe you were too lazy to install "
    ++ "Isabelle in the first place.",
    
  Option ['a'] ["isa-all"] (NoArg $ \f -> f { flagIsabelleAll = True })
     $ "Normally Zeno will only output functions to Isabelle if they are used "
    ++ "within proven properties. If you specify this option your entire program "
    ++ "will be printed to the Isabelle output file instead. "
    ++ "This feature is very experimental and the Isabelle output will often need "
    ++ "to be manually tweaked.",
    
  Option ['i'] ["include-dir"] 
    (ReqArg (\d f -> f { flagIncludeDirs = d : flagIncludeDirs f }) "DIR")
     $ "Specify a directory to be included when loading Haskell code. "
    ++ "Essentially this is just passed as an -i parameter to GHC.",
     
  Option ['o'] ["isa-dir"] (ReqArg (\d f -> f { flagIsabelleDir = d }) "DIR")
     $ "Specify the directory where Zeno will output its generated Isabelle code. "
    ++ "Defaults to \"" ++ defaultIsabelleDir ++ "\"",
    
  Option ['t'] ["timeout"] (ReqArg (\t f -> f { flagTimeout = read t }) "SECS")
     $ "Specify a timeout for Zeno to run within; any number less than one is ignored.",
     
  Option [] ["tryzeno"] (NoArg $ \f -> f { flagWebMode = True })
    $ "Formats the output for the TryZeno interface."
  ]
  
