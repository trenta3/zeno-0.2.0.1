-- |This module contains 'toIsabelle' definitions of all the core Zeno types.
module Zeno.Isabellable.Core () 
where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Isabellable.Class

import qualified Data.Map as Map
import qualified Data.Text as Text

instance Isabellable Id where
  toIsabelle = fromString . ("z_" ++) . show

instance Isabellable ZBindings where
  toIsabelle binds =
    "\n\nfun " ++ decls_s ++ "\nwhere\n  " ++ exprs_s
    where
    flat = flattenBindings binds
    
    exprs_s = intercalate "\n| " $ do
      (fun, expr) <- flat
      let (vars, expr') = flattenLambdas expr
      return $ 
        "\"" ++ (toIsabelle . unflattenApp . map Var) (fun : vars) 
        ++ " = " ++ (runIndented . indent . toIsabelleI) expr' ++ "\""
      
    decls_s = intercalate "\nand " $ do
      (var, _) <- flat
      let var_name = toIsabelle var
          type_s = " :: " ++ (quote . toIsabelle . getType) var
      return $ if (isOperator . Text.unpack) var_name 
        then (toIsabelle . varId) var ++ type_s ++ " (infix \"" ++ var_name ++ "\" 42)"
        else var_name ++ type_s
    
instance Isabellable ZVar where
  toIsabelle var =
    case varName var of
      Nothing -> toIsabelle (varId var)
      Just name -> (fromString . convertName) name
    where
    convertName :: String -> String
    convertName [':'] = "#"
    convertName ('$':'c':xs) = convertName xs
    convertName ('[':']':[]) = "[]"
    convertName name' = id 
      . prefixOperator
      . replace '/' '!' 
      $ name
      where 
      name = convert name'
      prefixOperator s 
        | isOperator s = "Z" ++ s
        | otherwise = s
    
instance Isabellable ZEquality where
  toIsabelle (x :=: y) = 
    case toIsabelle y of
      "True" -> toIsabelle x
      "False" -> "~(" ++ toIsabelle x ++ ")"
      y' -> toIsabelle x ++ " = " ++ y'
      
instance Isabellable ZClause where
  toIsabelle (Clause goal conds)
    | null conds = toIsabelle goal
    | otherwise = conds' ++ " ==> " ++ toIsabelle goal
      where
      conds' | length conds == 1 = toIsabelle (head conds)
             | otherwise = "[| " ++ 
                 intercalate "; " (map toIsabelle conds) 
                 ++ " |]"
    
instance Isabellable ZQuantified where
  toIsabelle (Quantified vars obj)
    | null vars = toIsabelle obj
    | otherwise = 
       "!! " ++ concatMap isaTyped vars 
        ++ ". " ++ toIsabelle obj
      where
      isaTyped var = "(" ++ toIsabelle var ++ 
        " :: " ++ toIsabelle (getType var) ++ ") " 
  
instance Isabellable ZHypothesis where
  toIsabelle = toIsabelle . hypClause
        
instance Isabellable ZExpr where
  toIsabelleI Err = error $
    "Cannot yet have _|_ in our Isabelle/HOL output; " ++
    "all your functions must be total. "
  toIsabelleI (Var var) = do
    var' <- toIsabelleI var
    if (isOperator . Text.unpack) var' && var' /= "[]"
      then toIsabelleI (varId var)
      else return var'
  toIsabelleI (flattenApp -> Var fun : args) 
    | (show fun == "(,)" && length args == 2)
      || (show fun == "(,,)" && length args == 3)
      || (show fun == "(,,,)" && length args == 4) = do
         args' <- mapM toIsabelleI args
         return $ 
           "(" ++ intercalate ", " args' ++ ")"
  toIsabelleI (App (App (Var fun) arg1) arg2) 
    | (isOperator . Text.unpack . toIsabelle) fun = do
      arg1' <- toIsabelleI arg1
      arg2' <- toIsabelleI arg2
      let arg1_s = if isTerm arg1 then arg1' else "(" ++ arg1' ++ ")"
          arg2_s = if isTerm arg2 then arg2' else "(" ++ arg2' ++ ")"
          fun_s = toIsabelle fun
      if fun_s == "#" && arg2_s == "[]" 
        then return $ "[" ++ arg1_s ++ "]"
        else return $ "(" ++ arg1_s ++ " " ++ fun_s ++ " " ++ arg2_s ++ ")"
  toIsabelleI (App x y) = do
    x' <- toIsabelleI x
    y' <- toIsabelleI y
    let y'' = if isApp y && Text.head y' /= '(' then "(" ++ y' ++ ")" else y'
    return $ x' ++ " " ++ y''
  toIsabelleI (Lam var rhs) = do
    rhs' <- toIsabelleI rhs
    return $ "(%" ++ toIsabelle var ++ ". " ++ rhs' ++ ")"
  toIsabelleI expr@(Let binds rhs) = do
    case flattenBindings binds of
      _ : _ : _ -> error $ 
        "Cannot have mutually recursive let bindings within an Isabelle/HOL expression." 
        ++ "\nThese can crop up with pre-defined type-class functions and I haven't "
        ++ "created a fix yet."
      [(var, expr)] -> do
        i <- indentation
        expr' <- toIsabelleI expr
        rhs' <- toIsabelleI rhs
        return $
          i ++ "(let " ++ toIsabelle var ++ " = " ++ expr' 
          ++ i ++ "in " ++ rhs' ++ ")"
  toIsabelleI (Cse _ expr alts) = indent $ do
    expr' <- toIsabelleI expr
    alts' <- mapM toIsabelleI alts
    i <- indentation
    let alts_s = intercalate (i ++ "| ") (reverse alts')
    return $ 
      i ++ "(case " ++ expr' ++ " of" 
      ++ i ++ "  " ++ alts_s ++ ")"
      
instance Isabellable ZAlt where
  toIsabelleI (Alt con vars rhs) = do 
    rhs' <- indent (toIsabelleI rhs)
    return $ lhs ++ " => " ++ rhs'
    where
    lhs = case con of
      AltCon var -> toIsabelle $ unflattenApp (map Var (var : vars))
      AltDefault -> "_"
      
instance Isabellable ZDataType where
  toIsabelle (DataType _ name args cons) =
    "\n\ndatatype" ++ fromString args_s ++ " " ++ fromString (convert name) 
      ++ "\n  = " ++ con_decl 
    where
    args' = map (("'" ++) . show) (reverse args)
    args_s = concatMap (" " ++) args'
    
    con_decl = intercalate "\n  | " con_decls
    
    con_decls = do
      con <- cons
      let con_name = toIsabelle con
          con_type = snd (flattenForAllType (getType con))
          arg_types = butlast (flattenFunType con_type)
          arg_list = concatMap ((" " ++) . quote . toIsabelle) arg_types
      return $
        if (isOperator . Text.unpack) con_name
          then toIsabelle (varId con) ++ arg_list 
            ++ " (infix \"" ++ con_name ++ "\" 42)"
          else con_name ++ arg_list
      
instance Isabellable ZType where
  toIsabelle (VarType var) = (fromString . convert . show) var
  toIsabelle (PolyVarType id) = fromString $ "'" ++ show id
  toIsabelle (ForAllType _ rhs) = toIsabelle rhs
  toIsabelle (flattenAppType -> VarType fun : args)
    | (show fun == "(,)" && length args == 2)
      || (show fun == "(,,)" && length args == 3)
      || (show fun == "(,,,)" && length args == 4) = 
         (intercalate " * " . map toIsabelle) args
  toIsabelle (AppType fun arg) = arg' ++ " " ++ fun' 
    where
    arg' = if isFunType arg || isAppType arg
      then "(" ++ toIsabelle arg ++ ")"
      else toIsabelle arg
      
    fun' = if isFunType fun
      then "(" ++ toIsabelle fun ++ ")"
      else toIsabelle fun
      
  toIsabelle (FunType arg res) = arg' ++ " => " ++ toIsabelle res
    where 
    arg' = if isFunType arg 
      then "(" ++ toIsabelle arg ++ ")"
      else toIsabelle arg


