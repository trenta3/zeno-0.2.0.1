{-# LANGUAGE DoRec #-}

-- |The title of this module is pretty self explanatory.
-- Uses the GHC API to get GHC Core syntax and parses this into 'Expr's and 'DataTypes'
-- returning a 'Program'
module Zeno.HaskellParser (
  loadHaskell
) where

import Prelude ()
import Zeno.Prelude
import Zeno.Core
import Zeno.Evaluation

import qualified Data.Set as Set

import System.Directory
import Outputable ( Outputable, ppr, defaultUserStyle, showPpr )

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified GHC.Paths as Paths
import qualified CoreSyn as Hs
import qualified Var as Hs
import qualified Type as Hs
import qualified HscTypes as Hs
import qualified DataCon as Hs
import qualified TyCon as Hs
import qualified GHC as Hs
import qualified DynFlags as Hs
import qualified Module as Hs
import qualified HscMain as Hs
import qualified Coercion as Hs
import qualified TidyPgm as Hs
import qualified Digraph as Hs

data HsEnv = HsEnv  { envVars :: Map (Either String Hs.Var) ZVar,
                      envTypes :: Map (Either String Hs.Type) ZType }

emptyEnv :: HsEnv
emptyEnv = HsEnv    { envVars = mempty,
                      envTypes = mempty }
                      
type HsZeno = StateT HsEnv (State ZProgram)
type HsExpr = Hs.Expr Hs.Var
type HsBinding = (Hs.Var, HsExpr)
type HsBindings = Hs.Bind Hs.Var

instance Eq Hs.Type where
  (==) = Hs.tcEqType
                     
instance Ord Hs.Type where
  compare = Hs.tcCmpType
  
instance WithinTraversable (Hs.Expr a) (Hs.Expr a) where
  mapWithinM f (Hs.App x y) = 
    f =<< Hs.App `liftM` mapWithinM f x `ap` mapWithinM f y 
  mapWithinM f (Hs.Let bind expr) = 
    f =<< Hs.Let `liftM` mapWithinM f bind `ap` mapWithinM f expr
  mapWithinM f (Hs.Lam x expr) = 
    f =<< Hs.Lam x `liftM` mapWithinM f expr
  mapWithinM f (Hs.Cast expr coer) = 
    f =<< (flip Hs.Cast coer) `liftM` mapWithinM f expr
  mapWithinM f (Hs.Note note expr) = 
    f =<< Hs.Note note `liftM` mapWithinM f expr
  mapWithinM f (Hs.Case expr b t alts) =
    f =<< Hs.Case `liftM` mapWithinM f expr `ap` 
      return b `ap` return t `ap` mapM traverseAlt alts
    where
    traverseAlt (con, b, expr) = do
      expr' <- mapWithinM f expr
      return (con, b, expr')      
  mapWithinM f x = f x
  
instance WithinTraversable (Hs.Expr a) (Hs.Bind a) where
  mapWithinM f (Hs.NonRec b ex) = Hs.NonRec b `liftM` mapWithinM f ex
  mapWithinM f (Hs.Rec binds) = Hs.Rec `liftM` mapM mapBinding binds
    where 
    mapBinding (b, ex) = do
      ex' <- mapWithinM f ex
      return (b, ex')

loadHaskell :: ZenoFlags -> IO ZProgram
loadHaskell zflags = do
  loadZeno <- runGhc $ do
    setupGhc
    mapM_ loadFile (flagHaskellFiles zflags)
    graph <- Hs.depanal [] True
    let sorted_graph = Hs.flattenSCCs
          $ Hs.topSortModuleGraph False graph Nothing
    guts <- mapM summaryToModule sorted_graph
    mods <- mapM simplifyModule guts
    return $ mapM_ loadModule mods

  return 
    . flip execState (emptyProgram zflags)
    . flip evalStateT emptyEnv
    $ addBuiltInTypes >> loadZeno
  where
  loadFile filename = do
    target <- Hs.guessTarget filename Nothing
    Hs.setTargets [target]
    Hs.load Hs.LoadAllTargets

  setupGhc = do
    flags <- Hs.getSessionDynFlags
    let paths = flagIncludeDirs zflags 
        flags' = flags 
          { Hs.importPaths = paths ++ (Hs.importPaths flags) }
    Hs.setSessionDynFlags flags'
  
  runGhc :: Hs.Ghc a -> IO a
  runGhc = Hs.defaultErrorHandler Hs.defaultDynFlags 
         . Hs.runGhc (Just Paths.libdir)

summaryToModule :: Hs.ModSummary -> Hs.Ghc Hs.ModGuts
summaryToModule = Hs.parseModule
             >=> Hs.typecheckModule
             >=> Hs.desugarModule
             >=> (return . Hs.coreModule)
             
simplifyModule :: Hs.ModGuts -> Hs.Ghc Hs.CoreModule
simplifyModule guts = do
  hsc_env <- Hs.getSession
  simpl_guts <- Hs.hscSimplify guts
  (cg, md) <- Hs.liftIO $ Hs.tidyProgram hsc_env simpl_guts
  return $ Hs.CoreModule 
    { Hs.cm_module = Hs.cg_module cg,    Hs.cm_types = Hs.md_types md,
      Hs.cm_imports = Hs.cg_dir_imps cg, Hs.cm_binds = Hs.cg_binds cg }
  
loadModule :: Hs.CoreModule -> HsZeno ()
loadModule core_mod = {- trace (output . Hs.cm_binds $ core_mod) $ -} do
  convertDataCons $ Hs.typeEnvDataCons 
    $ Hs.cm_types core_mod
  mapM_ convertTopLevelBindings
    $ Hs.cm_binds core_mod

addBuiltInTypes :: HsZeno ()
addBuiltInTypes = do
  addErrorTypes
  addBoolType
  addListType
  forM_ [2..4] addTupleType
  where
  addBoolType :: HsZeno ()
  addBoolType = do
    bool_id <- lift newIdS
    true_id <- lift newIdS
    false_id <- lift newIdS
    let true_var = ZVar true_id (Just "True") 
          bool_type (ConstructorVar False)
        false_var = ZVar false_id (Just "False") 
          bool_type (ConstructorVar False)
        bool_dtype = DataType bool_id "bool" [] [true_var, false_var]
        bool_type = VarType bool_dtype 
    addEnvVar  (Left "GHC.Bool.True")  true_var
    addEnvVar  (Left "GHC.Bool.False") false_var
    addEnvType (Left "GHC.Bool.Bool") bool_type
    lift $ addDataType bool_dtype                                      
        
  addListType :: HsZeno ()
  addListType = do
    [list_id, empty_id, cons_id, d0_id, d1_id, poly_id]
      <- lift $ replicateM 6 newIdS
    let poly_type = PolyVarType poly_id
        list_type_fun = VarType list_dtype
        list_type = AppType list_type_fun poly_type
        empty_type = ForAllType poly_id list_type
        cons_type = ForAllType poly_id (FunType poly_type (FunType list_type list_type))
        list_dtype = DataType list_id "list" [poly_id] [empty_var, cons_var]
        empty_var = ZVar empty_id (Just "[]") empty_type (ConstructorVar False)
        cons_var = ZVar cons_id (Just ":") cons_type (ConstructorVar True)
    addEnvVar  (Left "GHC.Types.[]") empty_var
    addEnvVar  (Left "GHC.Types.:")  cons_var
    addEnvType (Left "[]") list_type_fun
    lift $ addDataType list_dtype
              
  addTupleType :: Int -> HsZeno ()
  addTupleType n = do
    poly_vars <- replicateM n (lift newIdS)
    con_id <- lift newIdS
    dtype_id <- lift newIdS
    let symbol = "(" ++ replicate (n - 1) ',' ++ ")"
        poly_types = map PolyVarType poly_vars
        con_dtype = DataType dtype_id symbol poly_vars [con_var]
        ret_type = unflattenAppType (VarType con_dtype : poly_types)
        con_type = unflattenForAllType poly_vars 
                 $ unflattenFunType (poly_types ++ [ret_type])
        con_var = ZVar con_id (Just symbol) con_type (ConstructorVar False)
    addEnvVar (Left $ "GHC.Tuple." ++ symbol) con_var
    (addEnvType (Left symbol) . VarType) con_dtype
    (lift . addDataType) con_dtype

  addErrorTypes :: HsZeno ()
  addErrorTypes = do
    fun_id <- lift newIdS
    rw_id <- lift newIdS
    poly_var <- lift newIdS
    let any_type = ForAllType poly_var (PolyVarType poly_var)
        fun_var = ZVar fun_id (Just "patternMatchError") any_type err_class
        rw_var = ZVar rw_id (Just "realWorld#") any_type err_class
        err_class = DefinedVar (Just Err) False
    addEnvType (Left "GHC.Prim.Addr#") any_type
    addEnvType (Left "GHC.Prim.State#") any_type
    addEnvType (Left "GHC.Prim.RealWorld") any_type
    addEnvVar (Left "GHC.Prim.realWorld#") rw_var
    addEnvVar (Left "Control.Exception.Base.patError") fun_var

addEnvVar :: Either String Hs.Var -> ZVar -> HsZeno ()
addEnvVar var zvar = modify $ \env -> 
  env { envVars = Map.insert var zvar (envVars env) }
  
addEnvType :: Either String Hs.Type -> ZType -> HsZeno ()
addEnvType type_name ztype = modify $ \env -> 
  env { envTypes = Map.insert type_name ztype (envTypes env) }
 
output :: Outputable a => a -> String
output = showPpr --show . flip ppr defaultUserStyle 
  
outputName :: Outputable a => a -> String
outputName = output --stripEndNumber . stripModuleName . output

lookupTypeId :: Hs.Type -> MaybeT HsZeno ZType
lookupTypeId hs_type = do
  types <- envTypes <$> get
  case Map.lookup (Right hs_type) types of
    Just ztype -> return ztype
    Nothing -> 
      case Map.lookup (Left $ output hs_type) types of
        Just ztype -> return ztype
        Nothing -> mzero 
        {- error 
          $ "Zeno representation for type not found: " ++ output hs_type -}
    
lookupVar :: Hs.Var -> HsZeno ZVar 
lookupVar hs_var = do
  vars <- envVars <$> get
  case Map.lookup (Right hs_var) vars of
    Just var -> return var
    Nothing -> 
      case Map.lookup (Left $ output hs_var) vars of
        Just var -> return var
        Nothing -> error 
          $ "Zeno representation for variable not found: " ++ output hs_var

-- TODO: Make this work for mutually recursive types 
-- (and just properly in general).
recursiveDataCon :: Hs.DataCon -> Bool
recursiveDataCon con = any (== res_type) arg_types
  where
  res_type = Hs.tyConAppTyCon (Hs.dataConOrigResTy con)
  arg_types = mapMaybe (fmap fst . Hs.splitTyConApp_maybe)
            $ Hs.dataConOrigArgTys con
  
convertCoreType :: Hs.Type -> MaybeT HsZeno ZType
convertCoreType hs_type = all_type
  where
  all_type = case Hs.splitForAllTy_maybe hs_type of
    Just (tyvar, rest) -> do
      new_ptvar :: PolyTypeVar <- (lift . lift) newIdS
      lift $ addEnvType (Right $ Hs.mkTyVarTy tyvar) (PolyVarType new_ptvar)
      ForAllType new_ptvar <$> convertCoreType rest
    Nothing ->
      fun_type

  fun_type = case Hs.splitFunTy_maybe hs_type of
    Just (arg, res) -> do
      arg' <- convertCoreType arg
      res' <- convertCoreType res
      return (FunType arg' res')
    Nothing -> 
      app_type
      
  app_type = case Hs.splitAppTy_maybe hs_type of
    Just (fun, arg) -> do
      fun' <- convertCoreType fun
      arg' <- convertCoreType arg
      return (AppType fun' arg')
    Nothing -> 
      lookupTypeId hs_type

convertTopLevelBindings :: HsBindings -> HsZeno ()
convertTopLevelBindings hsbinds = do
  binds <- id
      . concatMap splitFakeRecs
      . map evaluateBindings
      . map (mapExpr simplify)
      . removeTypeClassPita7
      . removeTypeClassPita6
      . mapExpr simplify
      . mapWithin simplifyCases
      
    <$> convertBindings hsbinds

  let updateAll :: Functor f => [ZBindings] -> f ZVar -> f ZVar
      updateAll = foldl' (\f b -> f . updateDefinitions b) id
      
      binds' = map (updateAll binds) binds
      
  lift (mapM_ addBindings binds')
  modify $ \env -> env { envVars = updateAll binds' (envVars env) }
  
simplifyCases :: ZExpr -> ZExpr
simplifyCases (Let (NonRec (show -> "fail", _)) rhs) = rhs
simplifyCases (Cse id lhs@(Var _) alts) = 
  Cse id lhs (map rucAlt alts)
  where
  rucAlt :: ZAlt -> ZAlt
  rucAlt (Alt (AltCon con) args rhs) = 
    Alt (AltCon con) args (mapWithin substituteCase rhs) 
    where
    alt = (unflattenApp . map Var) (con : args)
    sub = Map.singleton lhs alt
    
    substituteCase :: ZExpr -> ZExpr
    substituteCase (Cse id lhs alts) =
      Cse id (substitute sub lhs) alts
    substituteCase expr = expr
 
  rucAlt alt = alt
simplifyCases expr = expr

splitFakeRecs :: ZBindings -> [ZBindings]
splitFakeRecs b@(NonRec _) = [b]
splitFakeRecs bs@(Rec binds) = 
  Rec mutual : map (Rec . return) rec_free ++ map NonRec free
  where
  names = (Set.fromList . boundVars) bs 
  (recr, free) = partition recursive binds 
  (mutual, rec_free) = partition mutuallyRecursive recr
  
  recursive (var, expr) = not 
    . Set.null . Set.intersection names 
    . Set.fromList . toList $ expr
    
  mutuallyRecursive (var, expr) = not 
    . Set.null . Set.intersection (Set.delete var names)
    . Set.fromList . toList $ expr

-- |Pita == Pain in the ass, and this is the one for GHC6
removeTypeClassPita6 :: ZBindings -> ZBindings
removeTypeClassPita6 bs@(NonRec (outer_name, outer_expr))
  | (not . null) outer_args = convertRhs rhs
  where
  (outer_args, rhs) = flattenLambdas outer_expr
  
  convertRhs (Let (Rec [(inner_name, inner_expr)]) rhs') 
    | all isVar flat 
      && fromVar inner_fun == inner_name
      && and (zipWith (==) inner_args real_args) =
        replace inner_name new_inner_name
          $ Rec [(outer_name, new_outer), (inner_name, new_inner)]
    where 
    flat@(inner_fun : inner_args') = flattenApp rhs'
    inner_args = map fromVar inner_args'
    (cls_args, real_args) = 
      splitAt (length outer_args - length inner_args) outer_args 
    
    new_outer = unflattenLambdas outer_args 
      $ unflattenApp (inner_fun : map Var outer_args)
    new_inner = unflattenLambdas cls_args 
      $ substitute add_args_sub inner_expr
    
    inner_with_args = (unflattenApp . map Var) (inner_name : cls_args) 
    add_args_sub = Map.singleton (Var inner_name) inner_with_args
    
    new_inner_name = 
      inner_name { varType = varType (outer_name) }
    
  convertRhs _ = bs
  
removeTypeClassPita6 bs = bs

-- |Pita == Pain in the ass, and this is the one for GHC7
removeTypeClassPita7 :: ZBindings -> [ZBindings]
removeTypeClassPita7 bs@(Rec binds) =
  case find pitaBind binds of
    Just pita@(var, expr) -> 
      let pita_sub = Map.singleton (Var var) expr
          new_binds = id
            . map (second $ substitute pita_sub)
            . delete pita
            $ binds
      in [Rec new_binds, NonRec pita] 
    _ -> [bs]
  where
  pitaBind (_, ex@(App {})) 
    | "D:" `isInfixOf` show ex = True
  pitaBind _= False
removeTypeClassPita7 bs = [bs]
  
convertBinds :: Bool -> [HsBinding] -> HsZeno [ZBinding]
convertBinds rc (unzip -> (hsvars, hsexprs)) = do
  vars <- mapM (flip createHsEnvVar (DefinedVar Nothing rc)) hsvars
  exprs <- mapM convertExpr hsexprs
  return (vars `zip` exprs)
      
convertBindings :: HsBindings -> HsZeno ZBindings
convertBindings (Hs.NonRec b expr) = 
  NonRec <$> head <$> convertBinds False [(b, expr)]
convertBindings (Hs.Rec binds) =
  Rec <$> convertBinds True binds

createHsEnvVar :: Hs.Var -> ZVarClass -> HsZeno ZVar
createHsEnvVar hs_var var_cls = do
  new_id <- lift newIdS
  var_type <- (fromJustT . convertCoreType . Hs.varType) hs_var
  let new_name = Just (outputName hs_var)
      new_var = ZVar new_id new_name var_type var_cls
  addEnvVar (Right hs_var) new_var 
  return new_var
  
convertExpr :: HsExpr -> HsZeno ZExpr
convertExpr (Hs.Note _ rhs) = convertExpr rhs
convertExpr (Hs.Var hsvar) = do
  var <- lookupVar hsvar
  return $ case varClass var of
    DefinedVar (Just expr) False -> expr
    _ -> Var var
convertExpr (Hs.Lit lit) = return Err
  -- This was producing a trace for pattern match messages,
  -- which should to be explicitly handled
  -- but for now I'm leaving this out
  {- flip trace (return Err)
  $ "Zeno does not handle literals yet, so could not parse " ++ output lit
  ++ "\nIt has been replaced by _|_" -}
convertExpr (Hs.App lhs (Hs.Type _)) = convertExpr lhs
convertExpr (Hs.App lhs rhs) = 
  App <$> convertExpr lhs <*> convertExpr rhs
convertExpr (Hs.Let bind rhs) = 
  Let <$> convertBindings bind <*> convertExpr rhs
convertExpr (Hs.Cast rhs coer) = do
  rhs' <- convertExpr rhs
  Just type_l <- runMaybeT (convertCoreType coer_l)
  Just type_r <- runMaybeT (convertCoreType coer_r)
  case (head . flattenAppType) type_r of
    VarType (dataTypeCons -> [con]) ->
      return (App (Var con) rhs') 
    _ -> case (head . flattenAppType) type_l of
      VarType (dataTypeCons -> [con]) -> do
        var_id <- lift newIdS
        cse_id <- lift newIdS
        let new_var = ZVar var_id Nothing type_r (UniversalVar [])
        return $ Cse cse_id rhs' 
          $ [Alt (AltCon con) [new_var] (Var new_var)]
      _ -> 
        return rhs'
  where
  (coer_l, coer_r) = Hs.coercionKind coer
convertExpr (Hs.Type _) = error 
  $ "Tried parsing a Type from the GHC core syntax. These should have been removed"
  ++ " beforehand so this is a bug in Zeno."
convertExpr (Hs.Lam var rhs) 
  | Hs.isTyVar var = do
      new_ptvar :: PolyTypeVar <- lift newIdS
      addEnvType (Right $ Hs.mkTyVarTy var) (PolyVarType new_ptvar)
      convertExpr rhs
  | otherwise =  Lam <$> createHsEnvVar var defaultVarClass <*> convertExpr rhs
convertExpr (Hs.Case of_expr var _ alts) = do
  z_var <- createHsEnvVar var defaultVarClass
  z_alts' <- mapM convertAlt alts
  z_of_expr <- convertExpr of_expr
  case_id <- lift newIdS
  let z_alts = map (replaceWithin (Var z_var) z_of_expr) z_alts' 
  return $ Cse case_id z_of_expr z_alts
  where
  convertAlt :: Hs.Alt Hs.Var -> HsZeno ZAlt
  convertAlt (Hs.DEFAULT, [], rhs) = 
    Alt AltDefault [] <$> convertExpr rhs
  convertAlt (Hs.DataAlt con, binds, rhs) = do
    z_con <- AltCon <$> lookupVar (Hs.dataConWorkId con)
    z_binds  <- mapM (flip createHsEnvVar defaultVarClass) binds
    z_rhs <- convertExpr rhs
    return $ Alt z_con z_binds z_rhs

convertDataCons :: [Hs.DataCon] -> HsZeno ()
convertDataCons cons = do
  let con_types = nubOrd $ map dataConReturnType cons
      typed_cons = map (\t -> (t, consOfType t)) con_types
  rec mapM_ (uncurry addEnvType) types
      types <- mapM createDataType typed_cons
  return ()
  where
  createDataType :: (Hs.Type, [Hs.DataCon]) -> 
      HsZeno (Either String Hs.Type, ZType)
  createDataType (hs_type, cons) = do
    (hs_type', arg_types) <- stripTypeArgs hs_type
    type_id <- lift newIdS
    cons' <- mapM (createDataConVar arg_types) cons
    let dt_name = outputName hs_type'
        datatype = DataType type_id dt_name arg_types cons'
    lift $ addDataType datatype
    return (Right hs_type', VarType datatype)
    where
    stripTypeArgs :: Hs.Type -> HsZeno (Hs.Type, [PolyTypeVar])
    stripTypeArgs hs_type = do
      let (fun_type, arg_types) = Hs.splitAppTys hs_type 
      ptypes <- mapM createPolyType arg_types
      return (fun_type, ptypes)
      where
      createPolyType :: Hs.Type -> HsZeno PolyTypeVar
      createPolyType hs_type = do
        new_id <- lift newIdS
        addEnvType (Right hs_type) (PolyVarType new_id)
        return new_id

    createDataConVar :: [PolyTypeVar] -> Hs.DataCon -> HsZeno ZVar
    createDataConVar poly_vars con = do
      mapM_ addTyVar (Hs.dataConAllTyVars con)
      con_type <- (fromJustT . convertCoreType . Hs.dataConUserType) con
      type_args <- fromJustT
        . fmap (tail . flattenAppType) 
        . convertCoreType 
        $ Hs.dataConOrigResTy con
      let poly_args = map fromPolyVarType type_args
          poly_sub = Map.fromList (poly_args `zip` poly_vars)
      con_id <- lift newIdS
      let con_cls = ConstructorVar (recursiveDataCon con)
          con_type' = substitute poly_sub con_type
          con_var = ZVar con_id (Just name) con_type' con_cls
      addEnvVar (Right $ Hs.dataConWorkId con) con_var
      return con_var
      where
      name = outputName $ Hs.dataConName con

      addTyVar :: Hs.TyVar -> HsZeno PolyTypeVar
      addTyVar tyvar = do
        type_id <- lift newIdS
        addEnvType (Right $ Hs.mkTyVarTy tyvar) (PolyVarType type_id)
        return type_id
                
  consOfType :: Hs.Type -> [Hs.DataCon]
  consOfType t = filter ((== t) . dataConReturnType) cons

  dataConReturnType :: Hs.DataCon -> Hs.Type
  dataConReturnType con = 
    let (_, _, _, t) = Hs.dataConSig con in t

      
      
      
