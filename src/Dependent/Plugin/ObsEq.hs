{-# LANGUAGE LambdaCase #-}

{- |
Module      : Dependent.Plugin.ObsEq
Description : Observational-equivalence TcPlugin for Dependent Haskell
License     : BSD-3-Clause
Maintainer  : mpg@mpg.is

GHC typechecker plugin that tests open type-level equalities via strong
three-valued Kleene approximation ('ObsTree') over total and partial
('ObsBottom') inputs, normalizes algebraic Givens via constructive
Knuth-Bendix completion, refutes false equalities with shrunk
counterexamples, and discharges explicit observational witnesses ('ObsEq',
'ObsEqOn', 'ObsEqBy').

Credit: Based on the observational-equivalence / QuickCheck @TcPlugin@ idea
proposed by Jules (\@analytichegel).
-}
module Dependent.Plugin.ObsEq (
    plugin,
    DischargePolicy (..),
    PluginOpts (..),
    parsePluginOpts,
) where

import Control.Monad (foldM, forM, guard, when, zipWithM)
import Data.Char (isSpace)
import Data.Graph qualified as Graph
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (isPrefixOf, nubBy)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing, mapMaybe)
import Data.Set qualified as Set
import Data.Time.Clock (getCurrentTime)
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Text.Read (readMaybe)

import Dependent.ObsEq.Domain (
    InconclusiveReason (..),
    renderInconclusiveReason,
 )
import Dependent.ObsEq.Internal (
    ObsConfig (..),
    defaultObsConfig,
 )
import Dependent.Plugin.ObsEq.Rewrite (
    KBEnv,
    applyKBVarSubst,
    buildKBEnv,
    normalizeTypeKB,
    proveGoalConstructively,
 )

import GHC.Builtin.Modules (mkInteractiveModule)
import GHC.ByteCode.Serialize qualified as ByteCode
import GHC.Core.Class (Class, classMethods, classTyCon)
import GHC.Core.Coercion.Axiom (
    closedTyFamCoAxiom_maybe,
    coAxBranchLHS,
    coAxBranchRHS,
    coAxBranchTyVars,
    coAxiomBranches,
    fromBranches,
 )
import GHC.Core.FamInstEnv (FamInstEnvs, normaliseType)
import GHC.Core.InstEnv (InstEnvs, instanceDFunId, lookupUniqueInstEnv)
import GHC.Core.Lint.Interactive (interactiveInScope)
import GHC.Core.Map.Type (
    TypeMap,
    emptyCME,
    emptyTypeMap,
    extendCMEs,
    extendTypeMap,
    extendTypeMapWithScope,
    lookupTypeMap,
    lookupTypeMapWithScope,
 )
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.Predicate (
    EqRel (NomEq),
    Pred (ClassPred, EqPred),
    classifyPredType,
    getClassPredTys_maybe,
    mkClassPred,
 )
import GHC.Core.Reduction (Reduction (..))
import GHC.Core.Subst qualified as CoreSubst
import GHC.Core.TyCo.FVs (mkUnivCoDeps, tyCoVarsOfTypeList)
import GHC.Core.TyCo.Rep (TyLit (..), Type (..), UnivCoProvenance (..))
import GHC.Core.TyCo.Subst qualified as TySubst
import GHC.Core.Unify (tcMatchTys)
import GHC.CoreToStg (coreToStg)
import GHC.CoreToStg.AddImplicitBinds (addImplicitBinds)
import GHC.CoreToStg.Prep (corePrepPgm)
import GHC.Data.Bag (Bag, lengthBag, unionBags)
import GHC.Data.OrdList (fromOL)
import GHC.Data.Pair (Pair (..))
import GHC.Data.Strict qualified as Strict
import GHC.Driver.Config.CoreToStg (initCoreToStgOpts)
import GHC.Driver.Config.CoreToStg.Prep (initCorePrepConfig, initCorePrepPgmConfig)
import GHC.Driver.Config.Stg.Pipeline (initStgPipelineOpts)
import GHC.Driver.Main (hscCompileCoreExpr)
import GHC.HsToCore.Binds (dsEvBinds, dsTopLHsBinds)
import GHC.HsToCore.Monad (initDsTc)
import GHC.Iface.Env (lookupOrig)
import GHC.Linker.Loader (getLoaderState, initLoaderState, loadDecls)
import GHC.Linker.Types (
    LinkablePart (DotGBC),
    LinkableUsage,
    LinkableWith (..),
    PkgsLoaded,
    bco_loader_state,
    emptyBytecodeLoaderState,
    lookupInfoTableBytecodeState,
    lookupNameBytecodeState,
 )
import GHC.Plugins hiding (TcPlugin, (<>))
import GHC.Runtime.Interpreter (Interp, evalString)
import GHC.Stg.Pipeline (stg2stg)
import GHC.StgToByteCode (byteCodeGen)
import GHC.Tc.Errors.Types (TcRnMessage (TcRnUnknownMessage))
import GHC.Tc.Instance.Family (tcGetFamInstEnvs)
import GHC.Tc.Plugin (findImportedModule, tcPluginIO, tcPluginTrace)
import GHC.Tc.Types (
    SourceCheckState (..),
    TcGblEnv (..),
    TcM,
    TcPlugin (..),
    TcPluginM,
    TcPluginSolveResult (..),
    unsafeTcPluginTcM,
 )
import GHC.Tc.Types.Constraint (
    Ct,
    ctEvCoercion,
    ctEvidence,
    ctLoc,
    ctPred,
    insolubleCt,
 )
import GHC.Tc.Types.CtLoc (ctLocOrigin, ctLocSpan)
import GHC.Tc.Types.Evidence (EvBind, EvBindsVar, EvTerm (EvExpr), evBindMapBinds, evCoercion)
import GHC.Tc.Types.Origin (CtOrigin (ExprHoleOrigin))
import GHC.Tc.Utils.Env (
    tcGetInstEnvs,
    tcLookupClass,
    tcLookupDataCon,
    tcLookupId,
    tcLookupIdMaybe,
    tcLookupTyCon,
 )
import GHC.Tc.Utils.Monad (
    addErrAt,
    getGblEnv,
    getTcEvBindsMap,
    getTopEnv,
    liftZonkM,
    newUnique,
    recordThNeededRuntimeDeps,
    tryAllM,
    updTcRef,
 )
import GHC.Tc.Utils.TcType (isMetaTyVar, isTyFamFree, tcEqType)
import GHC.Tc.Zonk.TcType (zonkTcType)
import GHC.Tc.Zonk.Type (zonkTopDecls)
import GHC.Types.Error (mkPlainError, mkSimpleUnknownDiagnostic, noHints)
import GHC.Types.Unique (getKey)
import GHC.Types.Unique.DFM (emptyUDFM, plusUDFM)
import GHC.Unit.Finder qualified as Finder

{- Note [Implicit solver discharge vs explicit obsEq]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Credit: Jules (@analytichegel) proposed using randomized property testing inside
a GHC @TcPlugin@ to test observational equalities on open terms in Dependent
Haskell.

This plugin supports three discharge policies ('DischargePolicy'):

1. 'RefuteOnly' (@-fplugin-opt=Dependent.Plugin.ObsEq:policy=refute-only@):
   * Emits constructive System FC coercions when in-scope Givens algebraically
     entail the goal, and refutes falsified goals with shrunk counterexamples.
   * Never emits 'UnivCo'; leaves probabilistically verified goals unsolved.

2. 'ExplicitOnly' (default, @-fplugin-opt=Dependent.Plugin.ObsEq:policy=explicit@):
   * Explicit observational constraints ('ObsEq', 'ObsEqOn', 'ObsEqBy') run
     three-valued Kleene testing. On 'Verified', the plugin constructs
     dictionary evidence backed by @UnivCo (PluginProv "dependent-obs-eq")@
     over the exact underlying equation (@lhs ~# rhs@, @proj lhs ~# proj rhs@,
     or @rel lhs rhs ~# True@) with complete 'UnivCoDeps'. On 'Inconclusive',
     the plugin reports the resource or polymorphism obstruction and leaves the
     constraint unsolved.
   * Bare Wanted nominal equalities (@[W] lhs ~# rhs@, such as bare @Refl@) run
     observational testing for counterexample refutation only.

3. 'ImplicitAssume' (@-fplugin-opt=Dependent.Plugin.ObsEq:policy=assume@):
   * Also discharges passing bare nominal equalities @[W] lhs ~# rhs@ when
     'Verified'.
-}

{- Note [Speculative ExprHoleOrigin isolation and polymorphic dictionaries]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
1. Speculative hole-fit isolation ('isSpeculativeHoleCt'):
   GHC's 'tcCheckHoleFit' wraps candidate checks inside 'discardErrs' and tags
   subtype constraints with 'ExprHoleOrigin'. 'discardErrs' rolls back compiler
   error messages, not plugin 'IORef's or 'tcg_source_check'. When
   'isSpeculativeHoleCt' is 'True':
   * Under 'RefuteOnly' and 'ExplicitOnly', 'BareNominalGoal' skips bytecode
     testing immediately because 'ExplicitOnly' never discharges bare nominal
     equalities and 'discardErrs' discards counterexample diagnostics.
   * For 'ExplicitDictGoal' (checking whether 'obsEq' itself fits a typed hole),
     the plugin runs 'buildGoalBcoTask' without mutating 'psReportedSpans',
     'tcg_source_check', or 'recordThNeededRuntimeDeps', and returns
     'TcPluginContradiction' on both 'ObsCheckRefuted' and
     'ObsCheckInconclusive' so GHC suggests 'obsEq' only when the goal verifies.

2. Polymorphic skolem specialization and dictionary preservation:
   Unconstrained parametric 'Type' skolems specialize to 'Ordering' (and unary
   type-constructor skolems @Type -> Type@ specialize to @[]@ for refutation).
   Before applying 'polySubst', 'detectPolyClassConstraint' inspects every
   'ClassAppTy' node and every function's invisible 'Anon' class predicates.
   When a class constraint mentions a skolem type variable:
   * Refutation stays enabled (using global coherent instances at 'Ordering' or
     fallback 'Int' to find concrete counterexamples).
   * Positive discharge is blocked: 'ObsCheckVerified' maps to
     @ObsCheckInconclusive (PolymorphicClassConstraint predStr)@, because
     agreement on one monomorphic instance cannot prove arbitrary user instances.
-}

{- | Policy controlling whether observational verification emits no 'UnivCo'
axioms ('RefuteOnly'), discharges only explicit goals ('ExplicitOnly'), or
also discharges bare nominal equalities ('ImplicitAssume').
-}
data DischargePolicy
    = RefuteOnly
    | ExplicitOnly
    | ImplicitAssume
    deriving (Eq, Ord, Show)

-- | Parsed command-line options for @Dependent.Plugin.ObsEq@.
data PluginOpts = PluginOpts
    { poConfig :: !ObsConfig
    , poPolicy :: !DischargePolicy
    , poWarnAssume :: !Bool
    }
    deriving (Eq, Show)

defaultPluginOpts :: PluginOpts
defaultPluginOpts =
    PluginOpts
        { poConfig = defaultObsConfig
        , poPolicy = ExplicitOnly
        , poWarnAssume = False
        }

-- | Parse @-fplugin-opt=Dependent.Plugin.ObsEq:...@ flags.
parsePluginOpts :: [CommandLineOption] -> Either String PluginOpts
parsePluginOpts rawOpts =
    foldM applyOpt defaultPluginOpts (concatMap splitCommas rawOpts)
  where
    splitCommas :: String -> [String]
    splitCommas s =
        case break (== ',') s of
            (chunk, []) -> [trim chunk | not (all isSpace chunk)]
            (chunk, _ : rest) ->
                [trim chunk | not (all isSpace chunk)] ++ splitCommas rest

    trim :: String -> String
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

    readNatOpt :: String -> String -> Either String Natural
    readNatOpt key val =
        case readMaybe val :: Maybe Natural of
            Just n -> Right n
            Nothing -> Left ("Dependent.Plugin.ObsEq: invalid natural for '" ++ key ++ "': " ++ val)

    applyOpt :: PluginOpts -> String -> Either String PluginOpts
    applyOpt st opt
        | opt == "refute-only" || opt == "policy=refute-only" =
            Right st{poPolicy = RefuteOnly}
        | opt == "explicit" || opt == "policy=explicit" =
            Right st{poPolicy = ExplicitOnly}
        | opt == "assume" || opt == "policy=assume" =
            Right st{poPolicy = ImplicitAssume}
        | opt == "warn-assume" =
            Right st{poWarnAssume = True}
        | Just v <- stripKey "tests=" opt = do
            n <- readNatOpt "tests" v
            Right st{poConfig = (poConfig st){obsTests = max 1 n}}
        | Just v <- stripKey "max-size=" opt = do
            n <- readNatOpt "max-size" v
            Right st{poConfig = (poConfig st){obsMaxSize = n}}
        | Just v <- stripKey "approx-depth=" opt = do
            n <- readNatOpt "approx-depth" v
            Right st{poConfig = (poConfig st){obsApproxDepth = max 1 n}}
        | Just v <- stripKey "partial-pct=" opt = do
            n <- readNatOpt "partial-pct" v
            Right st{poConfig = (poConfig st){obsPartialPct = min 100 n}}
        | Just v <- stripKey "timeout-us=" opt = do
            n <- readNatOpt "timeout-us" v
            Right st{poConfig = (poConfig st){obsTimeoutUs = max 1 n}}
        | Just v <- stripKey "seed=" opt = do
            n <- readNatOpt "seed" v
            Right st{poConfig = (poConfig st){obsSeed = n}}
        | otherwise =
            Left ("Dependent.Plugin.ObsEq: unrecognized option '" ++ opt ++ "'")

    stripKey :: String -> String -> Maybe String
    stripKey prefix s
        | prefix `isPrefixOf` s = Just (drop (length prefix) s)
        | otherwise = Nothing

-- | GHC plugin entry point.
plugin :: Plugin
plugin =
    defaultPlugin
        { tcPlugin = \rawOpts ->
            Just $
                TcPlugin
                    { tcPluginInit = initPluginState rawOpts
                    , tcPluginSolve = solveObsEq
                    , tcPluginRewrite = \_ -> emptyUFM
                    , tcPluginPostTc = \_ -> pure ()
                    , tcPluginShutdown = \_ -> pure ()
                    }
        , pluginRecompile = flagRecompile
        }

type VerdictCacheKey = (ObsConfig, Int)

data PluginState = PluginState
    { psOpts :: !PluginOpts
    , psOptErr :: !(Maybe String)
    , psCachedEnv :: !(IORef (Maybe CachedObsEnv))
    , psReportedSpans :: !(IORef (Set.Set (String, String)))
    , psDesugarCache :: !(IORef (Maybe (Module, Int, Int, NameEnv (Id, CoreExpr))))
    , psVerdictCache :: !(IORef (Map.Map VerdictCacheKey (TypeMap (TypeMap ObsCheckOutcome))))
    , psSideCache :: !(IORef (Map.Map ObsConfig (TypeMap [Word64])))
    }

data CachedObsEnv = CachedObsEnv
    { ceObsEqCls :: !Class
    , ceObsEqOnCls :: !Class
    , ceObsEqByCls :: !Class
    , ceObsGenCls :: !Class
    , ceTyEqTc :: !TyCon
    , ceReflDc :: !DataCon
    , ceUnsafeObsEquivOnDc :: !DataCon
    , ceUnsafeObsEquivByDc :: !DataCon
    , ceOrderingTc :: !TyCon
    , ceObsConfigTc :: !TyCon
    , ceObsConfigDc :: !DataCon
    , ceObsTreeTc :: !TyCon
    , ceObsConDc :: !DataCon
    , ceGenTc :: !TyCon
    , ceObsGenId :: !Id
    , ceObsGenPartialId :: !Id
    , ceObsShrinkId :: !Id
    , ceObsApproxId :: !Id
    , ceObsShowId :: !Id
    , ceDomGenPartialId :: !Id
    , ceDomShrinkId :: !Id
    , ceDomPredId :: !Id
    , ceDomShowId :: !Id
    , ceMkAdtDictId :: !Id
    , ceAdtGenId :: !Id
    , ceAdtGenPartialId :: !Id
    , ceAdtShrinkId :: !Id
    , ceAdtApproxId :: !Id
    , ceAdtShowId :: !Id
    , ceRunLoopId :: !Id
    , ceRunOnLoopId :: !Id
    , ceRunByLoopId :: !Id
    , ceEvalSideFpId :: !Id
    , ceNoBaselineId :: !Id
    , ceJustBaselineId :: !Id
    , ceAlwaysHoldsId :: !Id
    , cePredGuardId :: !Id
    , ceEqGuardId :: !Id
    , ceAndGuardId :: !Id
    , cePureGenId :: !Id
    , ceApGenId :: !Id
    , ceApHalfGenId :: !Id
    , cePureIOId :: !Id
    , ceBindIOId :: !Id
    , ceAppendStrId :: !Id
    , ceAppendListId :: !Id
    , ceMapListId :: !Id
    , cePairGenId :: !Id
    , cePairShrinkId :: !Id
    , cePairShowId :: !Id
    , ceNamedShowId :: !Id
    }

initPluginState :: [CommandLineOption] -> TcPluginM PluginState
initPluginState rawOpts = do
    let (parsedOpts, optErr) = case parsePluginOpts rawOpts of
            Right o -> (o, Nothing)
            Left err -> (defaultPluginOpts, Just err)
    envRef <- tcPluginIO (newIORef Nothing)
    repRef <- tcPluginIO (newIORef Set.empty)
    dsRef <- tcPluginIO (newIORef Nothing)
    vcRef <- tcPluginIO (newIORef Map.empty)
    scRef <- tcPluginIO (newIORef Map.empty)
    pure
        PluginState
            { psOpts = parsedOpts
            , psOptErr = optErr
            , psCachedEnv = envRef
            , psReportedSpans = repRef
            , psDesugarCache = dsRef
            , psVerdictCache = vcRef
            , psSideCache = scRef
            }

getCachedObsEnv :: PluginState -> TcPluginM (Maybe CachedObsEnv)
getCachedObsEnv st = do
    mb <- tcPluginIO (readIORef (psCachedEnv st))
    case mb of
        Just env -> pure (Just env)
        Nothing -> do
            obsFind <- findImportedModule (mkModuleName "Dependent.ObsEq") NoPkgQual
            case obsFind of
                Finder.Found _ obsMod -> do
                    let unitId = moduleUnit obsMod
                        intMod = mkModule unitId (mkModuleName "Dependent.ObsEq.Internal")
                        domMod = mkModule unitId (mkModuleName "Dependent.ObsEq.Domain")
                        eqMod = mkModule (stringToUnit "ghc-internal") (mkModuleName "GHC.Internal.Data.Type.Equality")
                        typesMod = mkModule (stringToUnit "ghc-internal") (mkModuleName "GHC.Internal.Types")
                    env <- unsafeTcPluginTcM $ do
                        obsEqCls <- lookupOrig obsMod (mkTcOcc "ObsEq") >>= tcLookupClass
                        obsEqOnCls <- lookupOrig obsMod (mkTcOcc "ObsEqOn") >>= tcLookupClass
                        obsEqByCls <- lookupOrig obsMod (mkTcOcc "ObsEqBy") >>= tcLookupClass
                        obsGenCls <- lookupOrig domMod (mkTcOcc "ObsGen") >>= tcLookupClass
                        tyEqTc <- lookupOrig eqMod (mkTcOcc ":~:") >>= tcLookupTyCon
                        reflDc <- lookupOrig eqMod (mkDataOcc "Refl") >>= tcLookupDataCon
                        equivOnDc <- lookupOrig obsMod (mkDataOcc "UnsafeObsEquivOn") >>= tcLookupDataCon
                        equivByDc <- lookupOrig obsMod (mkDataOcc "UnsafeObsEquivBy") >>= tcLookupDataCon
                        orderingTc <- lookupOrig typesMod (mkTcOcc "Ordering") >>= tcLookupTyCon
                        obsConfigTc <- lookupOrig intMod (mkTcOcc "ObsConfig") >>= tcLookupTyCon
                        obsConfigDc <- lookupOrig intMod (mkDataOcc "ObsConfig") >>= tcLookupDataCon
                        obsTreeTc <- lookupOrig domMod (mkTcOcc "ObsTree") >>= tcLookupTyCon
                        obsConDc <- lookupOrig domMod (mkDataOcc "ObsCon") >>= tcLookupDataCon
                        genTc <- lookupOrig domMod (mkTcOcc "Gen") >>= tcLookupTyCon
                        obsGenId <- lookupOrig domMod (mkVarOcc "obsGen") >>= tcLookupId
                        obsGenPartialId <- lookupOrig domMod (mkVarOcc "obsGenPartial") >>= tcLookupId
                        obsShrinkId <- lookupOrig domMod (mkVarOcc "obsShrink") >>= tcLookupId
                        obsApproxId <- lookupOrig domMod (mkVarOcc "obsApprox") >>= tcLookupId
                        obsShowId <- lookupOrig domMod (mkVarOcc "obsShow") >>= tcLookupId
                        domGenPartialId <- lookupOrig domMod (mkVarOcc "obsDomGenPartial") >>= tcLookupId
                        domShrinkId <- lookupOrig domMod (mkVarOcc "obsDomShrink") >>= tcLookupId
                        domPredId <- lookupOrig domMod (mkVarOcc "obsDomPred") >>= tcLookupId
                        domShowId <- lookupOrig domMod (mkVarOcc "obsDomShow") >>= tcLookupId
                        mkAdtDictId <- lookupOrig domMod (mkVarOcc "mkAdtObsDict") >>= tcLookupId
                        adtGenId <- lookupOrig domMod (mkVarOcc "adtGen") >>= tcLookupId
                        adtGenPartialId <- lookupOrig domMod (mkVarOcc "adtGenPartial") >>= tcLookupId
                        adtShrinkId <- lookupOrig domMod (mkVarOcc "adtShrink") >>= tcLookupId
                        adtApproxId <- lookupOrig domMod (mkVarOcc "adtApprox") >>= tcLookupId
                        adtShowId <- lookupOrig domMod (mkVarOcc "adtShow") >>= tcLookupId
                        runLoopId <- lookupOrig domMod (mkVarOcc "runObsTestLoop") >>= tcLookupId
                        runOnLoopId <- lookupOrig domMod (mkVarOcc "runObsOnLoop") >>= tcLookupId
                        runByLoopId <- lookupOrig domMod (mkVarOcc "runObsByLoop") >>= tcLookupId
                        evalSideFpId <- lookupOrig domMod (mkVarOcc "evalSideFingerprints") >>= tcLookupId
                        noBaselineId <- lookupOrig domMod (mkVarOcc "obsNoBaseline") >>= tcLookupId
                        justBaselineId <- lookupOrig domMod (mkVarOcc "obsJustBaseline") >>= tcLookupId
                        alwaysHoldsId <- lookupOrig domMod (mkVarOcc "obsAlwaysHolds") >>= tcLookupId
                        predGuardId <- lookupOrig domMod (mkVarOcc "obsPredGuard") >>= tcLookupId
                        eqGuardId <- lookupOrig domMod (mkVarOcc "obsEqGuard") >>= tcLookupId
                        andGuardId <- lookupOrig domMod (mkVarOcc "obsAndGuard") >>= tcLookupId
                        pureGenId <- lookupOrig domMod (mkVarOcc "obsPureGen") >>= tcLookupId
                        apGenId <- lookupOrig domMod (mkVarOcc "obsApGen") >>= tcLookupId
                        apHalfGenId <- lookupOrig domMod (mkVarOcc "obsApHalfGen") >>= tcLookupId
                        pureIOId <- lookupOrig domMod (mkVarOcc "obsPureIO") >>= tcLookupId
                        bindIOId <- lookupOrig domMod (mkVarOcc "obsBindIO") >>= tcLookupId
                        appendStrId <- lookupOrig domMod (mkVarOcc "obsAppendStr") >>= tcLookupId
                        appendListId <- lookupOrig domMod (mkVarOcc "obsAppendList") >>= tcLookupId
                        mapListId <- lookupOrig domMod (mkVarOcc "obsMapList") >>= tcLookupId
                        pairGenId <- lookupOrig domMod (mkVarOcc "obsPairGen") >>= tcLookupId
                        pairShrinkId <- lookupOrig domMod (mkVarOcc "obsPairShrink") >>= tcLookupId
                        pairShowId <- lookupOrig domMod (mkVarOcc "obsPairShow") >>= tcLookupId
                        namedShowId <- lookupOrig domMod (mkVarOcc "obsNamedShow") >>= tcLookupId
                        pure
                            CachedObsEnv
                                { ceObsEqCls = obsEqCls
                                , ceObsEqOnCls = obsEqOnCls
                                , ceObsEqByCls = obsEqByCls
                                , ceObsGenCls = obsGenCls
                                , ceTyEqTc = tyEqTc
                                , ceReflDc = reflDc
                                , ceUnsafeObsEquivOnDc = equivOnDc
                                , ceUnsafeObsEquivByDc = equivByDc
                                , ceOrderingTc = orderingTc
                                , ceObsConfigTc = obsConfigTc
                                , ceObsConfigDc = obsConfigDc
                                , ceObsTreeTc = obsTreeTc
                                , ceObsConDc = obsConDc
                                , ceGenTc = genTc
                                , ceObsGenId = obsGenId
                                , ceObsGenPartialId = obsGenPartialId
                                , ceObsShrinkId = obsShrinkId
                                , ceObsApproxId = obsApproxId
                                , ceObsShowId = obsShowId
                                , ceDomGenPartialId = domGenPartialId
                                , ceDomShrinkId = domShrinkId
                                , ceDomPredId = domPredId
                                , ceDomShowId = domShowId
                                , ceMkAdtDictId = mkAdtDictId
                                , ceAdtGenId = adtGenId
                                , ceAdtGenPartialId = adtGenPartialId
                                , ceAdtShrinkId = adtShrinkId
                                , ceAdtApproxId = adtApproxId
                                , ceAdtShowId = adtShowId
                                , ceRunLoopId = runLoopId
                                , ceRunOnLoopId = runOnLoopId
                                , ceRunByLoopId = runByLoopId
                                , ceEvalSideFpId = evalSideFpId
                                , ceNoBaselineId = noBaselineId
                                , ceJustBaselineId = justBaselineId
                                , ceAlwaysHoldsId = alwaysHoldsId
                                , cePredGuardId = predGuardId
                                , ceEqGuardId = eqGuardId
                                , ceAndGuardId = andGuardId
                                , cePureGenId = pureGenId
                                , ceApGenId = apGenId
                                , ceApHalfGenId = apHalfGenId
                                , cePureIOId = pureIOId
                                , ceBindIOId = bindIOId
                                , ceAppendStrId = appendStrId
                                , ceAppendListId = appendListId
                                , ceMapListId = mapListId
                                , cePairGenId = pairGenId
                                , cePairShrinkId = pairShrinkId
                                , cePairShowId = pairShowId
                                , ceNamedShowId = namedShowId
                                }
                    tcPluginIO (writeIORef (psCachedEnv st) (Just env))
                    pure (Just env)
                _ -> pure Nothing

data GoalFlavor
    = FlavorValue
    | -- | repKind, proj :: dom -> rep
      FlavorProj !Kind !Type
    | -- | rel :: dom -> dom -> Bool
      FlavorRel !Type

data CandidateGoal
    = ExplicitDictGoal
        { cgCt :: !Ct
        , cgClass :: !Class
        , cgClassArgs :: ![Type]
        , cgFlavor :: !GoalFlavor
        , cgKind :: !Kind
        , cgOrigLhs :: !Type
        , cgOrigRhs :: !Type
        , cgCfgTy :: !Type
        }
    | BareNominalGoal
        { cgCt :: !Ct
        , cgKind :: !Kind
        , cgOrigLhs :: !Type
        , cgOrigRhs :: !Type
        }

isSpeculativeHoleCt :: Ct -> Bool
isSpeculativeHoleCt ct =
    case ctLocOrigin (ctLoc ct) of
        ExprHoleOrigin _ -> True
        _ -> False

solveObsEq :: PluginState -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solveObsEq st evBindsVar givens wanteds
    | null wanteds = pure (TcPluginOk [] [])
    | Just errMsg <- psOptErr st = do
        case wanteds of
            ct : _ ->
                unsafeTcPluginTcM
                    $ addErrAt (RealSrcSpan (ctLocSpan (ctLoc ct)) Strict.Nothing)
                    $ TcRnUnknownMessage (mkSimpleUnknownDiagnostic (mkPlainError noHints (text errMsg)))
            [] -> pure ()
        pure (TcPluginOk [] [])
    | otherwise = do
        mbEnv <- getCachedObsEnv st
        case mbEnv of
            Nothing -> pure (TcPluginOk [] [])
            Just cenv -> do
                let candidates = mapMaybe (classifyWanted cenv) wanteds
                if null candidates
                    then pure (TcPluginOk [] [])
                    else do
                        let goalTys = concatMap goalSeedTypes candidates
                            kbEnv = buildKBEnv givens goalTys
                            rawGuards = extractTestableGuards kbEnv givens
                        adtCacheRef <- tcPluginIO (newIORef emptyTypeMap)
                        prepared <- forM candidates (prepareGoal st cenv evBindsVar kbEnv rawGuards adtCacheRef)
                        let tasks = [t | PreparedTask t <- prepared]
                        batchOuts <-
                            case tasks of
                                [] -> pure (Just [])
                                t0 : _ ->
                                    let locSpan = pbtLocSpan t0
                                        anyReal = any (not . pbtSpeculative) tasks
                                     in unsafeTcPluginTcM $
                                            runCoreIOStringBatch st cenv evBindsVar locSpan anyReal (map pbtBatchIo tasks)
                        outcomes <- finalizePreparedGoals st cenv prepared batchOuts
                        let bads = [ct | Left ct <- outcomes]
                            solved = [pair | Right (Just pair) <- outcomes]
                        if not (null bads)
                            then pure (TcPluginContradiction bads)
                            else pure (TcPluginOk solved [])

goalSeedTypes :: CandidateGoal -> [Type]
goalSeedTypes BareNominalGoal{cgOrigLhs = l, cgOrigRhs = r} = [l, r]
goalSeedTypes ExplicitDictGoal{cgFlavor = flv, cgOrigLhs = l, cgOrigRhs = r} =
    case flv of
        FlavorValue -> [l, r]
        FlavorProj _ proj -> [l, r, mkAppTy proj l, mkAppTy proj r]
        FlavorRel rel -> [l, r, mkAppTys rel [l, r], mkAppTys rel [r, l]]

classifyWanted :: CachedObsEnv -> Ct -> Maybe CandidateGoal
classifyWanted cenv ct
    | insolubleCt ct = Nothing
    | hasCoercionHole predTy = Nothing
    | any isMetaTyVar (tyCoVarsOfTypeList predTy) = Nothing
    | otherwise =
        case classifyPredType predTy of
            ClassPred cls args
                | cls == ceObsEqCls cenv
                , [k, cfgTy, lhs, rhs] <- args
                , validPromotedKind k ->
                    Just
                        ExplicitDictGoal
                            { cgCt = ct
                            , cgClass = cls
                            , cgClassArgs = args
                            , cgFlavor = FlavorValue
                            , cgKind = k
                            , cgOrigLhs = lhs
                            , cgOrigRhs = rhs
                            , cgCfgTy = cfgTy
                            }
                | cls == ceObsEqOnCls cenv
                , [aKind, repKind, cfgTy, projTy, lhs, rhs] <- args
                , validPromotedKind aKind
                , validPromotedKind repKind ->
                    Just
                        ExplicitDictGoal
                            { cgCt = ct
                            , cgClass = cls
                            , cgClassArgs = args
                            , cgFlavor = FlavorProj repKind projTy
                            , cgKind = aKind
                            , cgOrigLhs = lhs
                            , cgOrigRhs = rhs
                            , cgCfgTy = cfgTy
                            }
                | cls == ceObsEqByCls cenv
                , [aKind, cfgTy, relTy, lhs, rhs] <- args
                , validPromotedKind aKind ->
                    Just
                        ExplicitDictGoal
                            { cgCt = ct
                            , cgClass = cls
                            , cgClassArgs = args
                            , cgFlavor = FlavorRel relTy
                            , cgKind = aKind
                            , cgOrigLhs = lhs
                            , cgOrigRhs = rhs
                            , cgCfgTy = cfgTy
                            }
            EqPred NomEq lhs rhs
                | let k = typeKind lhs
                , k `tcEqType` typeKind rhs
                , validPromotedKind k
                , not (lhs `tcEqType` rhs) ->
                    Just
                        BareNominalGoal
                            { cgCt = ct
                            , cgKind = k
                            , cgOrigLhs = lhs
                            , cgOrigRhs = rhs
                            }
            _ -> Nothing
  where
    predTy = ctPred ct
    validPromotedKind k =
        not (tcIsLiftedTypeKind k) && tcIsLiftedTypeKind (typeKind k)

-- ---------------------------------------------------------------------------
-- Testable Given Precondition Guards ([G] pred ~# True)
-- ---------------------------------------------------------------------------

data TestableGuard = TestableGuard
    { tgKind :: !Kind
    , tgLhs :: !Type
    , tgRhs :: !Type
    , tgVars :: ![Var]
    , tgUsedCos :: ![Coercion]
    }

extractTestableGuards :: KBEnv -> [Ct] -> [TestableGuard]
extractTestableGuards kbEnv = concatMap extractOne
  where
    extractOne ct =
        let baseCo = ctEvCoercion (ctEvidence ct)
            candidates =
                case classifyPredType (ctPred ct) of
                    EqPred NomEq lhs rhs
                        | typeKind lhs `tcEqType` typeKind rhs ->
                            [(lhs, rhs, baseCo)]
                    ClassPred cls args
                        | getOccString cls `elem` ["~", "~~"]
                        , rhs : lhs : _ <- reverse args
                        , typeKind lhs `tcEqType` typeKind rhs ->
                            let selCo = mkSelCo (SelTyCon (length args - 1) Nominal) baseCo
                                Pair l r = coercionKind selCo
                             in [(lhs, rhs, selCo) | l `tcEqType` lhs && r `tcEqType` rhs]
                    _ -> []
         in [ TestableGuard
                { tgKind = gKind
                , tgLhs = lhsSub
                , tgRhs = rhsSub
                , tgVars = vars
                , tgUsedCos = baseCo : (cosL ++ cosR)
                }
            | (lhs, rhs, _) <- candidates
            , let (lhsSub, cosL) = applyKBVarSubst kbEnv lhs
            , let (rhsSub, cosR) = applyKBVarSubst kbEnv rhs
            , not (lhsSub `tcEqType` rhsSub)
            , let gKind = typeKind lhsSub
            , not (tcIsLiftedTypeKind gKind) && tcIsLiftedTypeKind (typeKind gKind)
            , let vars = collectValueVars [lhsSub, rhsSub]
            , not (null vars)
            ]

collectFreeTermAndTyVars :: [Type] -> [Var]
collectFreeTermAndTyVars tys =
    nubBy (\a b -> getUnique a == getUnique b) (concatMap walk tys)
  where
    isQuantifiedVar v = isLocalVar v && not (isExternalName (varName v))
    walk ty =
        case coreFullView ty of
            TermVarTy v
                | isQuantifiedVar v -> walk (varType v) ++ [v]
                | otherwise -> walk (varType v)
            TermAppTy f arg
                | isQuantifiedVar f -> walk (varType f) ++ [f] ++ walk arg
                | otherwise -> walk (varType f) ++ walk arg
            TyVarTy tv -> walk (tyVarKind tv) ++ [tv]
            TyConApp _ args -> concatMap walk args
            AppTy f a -> walk f ++ walk a
            FunTy _ ma mult a r -> walk ma ++ walk mult ++ walk a ++ walk r
            ForAllTy ma b r ->
                walk ma
                    ++ filter (/= binderVar b) (walk (varType (binderVar b)) ++ walk r)
            CastTy t _ -> walk t
            ClassAppTy _ i d x k -> walk i ++ walk d ++ walk x ++ walk k
            DepFunTy _ b r ->
                walk (varType b) ++ filter (/= b) (walk r)
            DepDictTy b r ->
                walk (varType b) ++ filter (/= b) (walk r)
            ExistsTy _ tv r ->
                walk (tyVarKind tv) ++ filter (/= tv) (walk r)
            _ -> []

collectValueVars :: [Type] -> [Var]
collectValueVars tys =
    [ v
    | v <- collectFreeTermAndTyVars tys
    , let vk = if isTyVar v then tyVarKind v else varType v
    , not (tcIsLiftedTypeKind vk)
    , tcIsLiftedTypeKind (typeKind vk)
    ]

-- ---------------------------------------------------------------------------
-- Preparing, Caching, and Finalizing Candidate Goals
-- ---------------------------------------------------------------------------

data ObsCheckOutcome
    = ObsCheckVerified
    | ObsCheckRefuted !String
    | ObsCheckInconclusive !InconclusiveReason

data PreparedGoal
    = PreparedDone !(Either Ct (Maybe (EvTerm, Ct)))
    | PreparedTask !PreparedBcoTask

data PreparedBcoTask = PreparedBcoTask
    { pbtGoal :: !CandidateGoal
    , pbtLocSpan :: !SrcSpan
    , pbtSpeculative :: !Bool
    , pbtUsedGivenCos :: ![Coercion]
    , pbtHasPolyDict :: !(Maybe String)
    , pbtCacheInfo :: !(Maybe (VerdictCacheKey, [Var], Type, Type))
    , pbtSideProbeInfo :: !(Maybe (ObsConfig, [Var], Type, Type))
    , pbtBatchIo :: !CoreExpr
    }

tryConstructiveProof :: KBEnv -> CandidateGoal -> Maybe Coercion
tryConstructiveProof kbEnv BareNominalGoal{cgOrigLhs = lhs, cgOrigRhs = rhs} =
    proveGoalConstructively kbEnv lhs rhs
tryConstructiveProof kbEnv ExplicitDictGoal{cgFlavor = flv, cgOrigLhs = lhs, cgOrigRhs = rhs} =
    case flv of
        FlavorValue -> proveGoalConstructively kbEnv lhs rhs
        FlavorProj _ proj ->
            proveGoalConstructively kbEnv (mkAppTy proj lhs) (mkAppTy proj rhs)
        FlavorRel rel -> do
            let trueTy = mkTyConApp promotedTrueDataCon []
            coLR <- proveGoalConstructively kbEnv (mkAppTys rel [lhs, rhs]) trueTy
            _ <- proveGoalConstructively kbEnv (mkAppTys rel [rhs, lhs]) trueTy
            _ <- proveGoalConstructively kbEnv (mkAppTys rel [lhs, lhs]) trueTy
            _ <- proveGoalConstructively kbEnv (mkAppTys rel [rhs, rhs]) trueTy
            pure coLR

prepareGoal ::
    PluginState ->
    CachedObsEnv ->
    EvBindsVar ->
    KBEnv ->
    [TestableGuard] ->
    IORef AdtCache ->
    CandidateGoal ->
    TcPluginM PreparedGoal
prepareGoal st cenv evBindsVar kbEnv allGuards adtCacheRef goal = do
    let ct = cgCt goal
        speculative = isSpeculativeHoleCt ct
        locSpan = RealSrcSpan (ctLocSpan (ctLoc ct)) Strict.Nothing
        origLhs = cgOrigLhs goal
        origRhs = cgOrigRhs goal

    -- Step 1: Zero-UnivCo constructive KBO check (valid under all policies!)
    case tryConstructiveProof kbEnv goal of
        Just constructiveCo ->
            case goal of
                ExplicitDictGoal{} -> do
                    let ev = mkExplicitGoalEv cenv goal constructiveCo
                    pure (PreparedDone (Right (Just (ev, ct))))
                BareNominalGoal{} ->
                    pure (PreparedDone (Right (Just (evCoercion constructiveCo, ct))))
        Nothing ->
            -- Step 2: Speculative ExprHoleOrigin fast skip on BareNominalGoal
            case (speculative, goal, poPolicy (psOpts st)) of
                (True, BareNominalGoal{}, RefuteOnly) -> pure (PreparedDone (Right Nothing))
                (True, BareNominalGoal{}, ExplicitOnly) -> pure (PreparedDone (Right Nothing))
                _ -> do
                    let (lhsSub, _, cosL) = normalizeTypeKB kbEnv origLhs
                        (rhsSub, _, cosR) = normalizeTypeKB kbEnv origRhs
                        (flvSub, cosF) = normalizeFlavor kbEnv (goalFlavor goal)

                    mbParsedCfg <- case goal of
                        BareNominalGoal{} -> pure (Just (emptyParsedConfig (poConfig (psOpts st))))
                        ExplicitDictGoal{cgCfgTy = cfgTy} ->
                            unsafeTcPluginTcM (evalParsedObsConfig st cenv evBindsVar locSpan speculative cfgTy)
                    case mbParsedCfg of
                        Nothing -> pure (PreparedDone (Right Nothing))
                        Just parsedCfg -> do
                            let cfg = pocScalar parsedCfg
                                hasDomainOverrides = not (null (pocVarDomains parsedCfg) && null (pocTypeDomains parsedCfg))
                                goalVarKeys = Set.fromList (map (getKey . getUnique) (collectValueVars (flavorTypes flvSub ++ [lhsSub, rhsSub])))
                                activeGuards =
                                    [ g
                                    | g <- allGuards
                                    , any (\v -> getKey (getUnique v) `Set.member` goalVarKeys) (tgVars g)
                                    ]
                                guardCos = concatMap tgUsedCos activeGuards
                                usedGivenCos = cosL ++ cosR ++ cosF ++ guardCos
                                canCache =
                                    not hasDomainOverrides
                                        && null activeGuards
                                        && case flvSub of
                                            FlavorValue -> True
                                            _ -> False
                                canonVars = collectValueVars [lhsSub, rhsSub]
                                cacheKey = (cfg, 0)

                            mbCached <-
                                if canCache
                                    then lookupCachedVerdict st cacheKey canonVars lhsSub rhsSub
                                    else pure Nothing
                            case mbCached of
                                Just cachedOutcome -> do
                                    res <- applyVerdictToGoal st cenv goal locSpan speculative usedGivenCos cachedOutcome
                                    pure (PreparedDone res)
                                Nothing -> do
                                    mbBuilt <-
                                        unsafeTcPluginTcM $
                                            buildGoalBcoTask st cenv adtCacheRef parsedCfg activeGuards flvSub (cgKind goal) lhsSub rhsSub
                                    case mbBuilt of
                                        Nothing -> pure (PreparedDone (Right Nothing))
                                        Just (batchIo, hasPolyDict, needSideProbes) ->
                                            let cacheInfo =
                                                    if canCache
                                                        then Just (cacheKey, canonVars, lhsSub, rhsSub)
                                                        else Nothing
                                                sideInfo =
                                                    if needSideProbes && canCache
                                                        then Just (cfg, canonVars, lhsSub, rhsSub)
                                                        else Nothing
                                             in pure $
                                                    PreparedTask
                                                        PreparedBcoTask
                                                            { pbtGoal = goal
                                                            , pbtLocSpan = locSpan
                                                            , pbtSpeculative = speculative
                                                            , pbtUsedGivenCos = usedGivenCos
                                                            , pbtHasPolyDict = hasPolyDict
                                                            , pbtCacheInfo = cacheInfo
                                                            , pbtSideProbeInfo = sideInfo
                                                            , pbtBatchIo = batchIo
                                                            }
  where
    goalFlavor BareNominalGoal{} = FlavorValue
    goalFlavor ExplicitDictGoal{cgFlavor = f} = f

    normalizeFlavor _ FlavorValue = (FlavorValue, [])
    normalizeFlavor env (FlavorProj repK pTy) =
        let (pSub, _, cosP) = normalizeTypeKB env pTy
         in (FlavorProj repK pSub, cosP)
    normalizeFlavor env (FlavorRel rTy) =
        let (rSub, _, cosR) = normalizeTypeKB env rTy
         in (FlavorRel rSub, cosR)

    flavorTypes FlavorValue = []
    flavorTypes (FlavorProj repK pTy) = [repK, pTy]
    flavorTypes (FlavorRel rTy) = [rTy]

lookupCachedVerdict ::
    PluginState ->
    VerdictCacheKey ->
    [Var] ->
    Type ->
    Type ->
    TcPluginM (Maybe ObsCheckOutcome)
lookupCachedVerdict st key vars lhs rhs = do
    let cmEnv = extendCMEs emptyCME vars
    vcMap <- tcPluginIO (readIORef (psVerdictCache st))
    pure $ do
        outerTm <- Map.lookup key vcMap
        let direct = lookupTypeMapWithScope outerTm cmEnv lhs >>= \inner -> lookupTypeMapWithScope inner cmEnv rhs
            symHit = do
                innerSym <- lookupTypeMapWithScope outerTm cmEnv rhs
                out <- lookupTypeMapWithScope innerSym cmEnv lhs
                case out of
                    ObsCheckVerified -> Just ObsCheckVerified
                    _ -> Nothing
        case direct of
            Just hit -> Just hit
            Nothing -> symHit

storeCachedVerdict ::
    PluginState ->
    VerdictCacheKey ->
    [Var] ->
    Type ->
    Type ->
    ObsCheckOutcome ->
    TcPluginM ()
storeCachedVerdict st key vars lhs rhs outcome = do
    let cmEnv = extendCMEs emptyCME vars
    vcMap <- tcPluginIO (readIORef (psVerdictCache st))
    let outer0 = Map.findWithDefault emptyTypeMap key vcMap
        inner0 = case lookupTypeMapWithScope outer0 cmEnv lhs of
            Just m -> m
            Nothing -> emptyTypeMap
        inner1 = extendTypeMapWithScope inner0 cmEnv rhs outcome
        outer1 = extendTypeMapWithScope outer0 cmEnv lhs inner1
    tcPluginIO (writeIORef (psVerdictCache st) (Map.insert key outer1 vcMap))

finalizePreparedGoals ::
    PluginState ->
    CachedObsEnv ->
    [PreparedGoal] ->
    Maybe [String] ->
    TcPluginM [Either Ct (Maybe (EvTerm, Ct))]
finalizePreparedGoals st cenv prepared mbStrings = go prepared mbStrings
  where
    go [] _ = pure []
    go (PreparedDone res : rest) mbOut = (res :) <$> go rest mbOut
    go (PreparedTask task : rest) Nothing =
        let fallback =
                if pbtSpeculative task && isExplicitGoal (pbtGoal task)
                    then Left (cgCt (pbtGoal task))
                    else Right Nothing
         in (fallback :) <$> go rest Nothing
    go (PreparedTask task : rest) (Just []) =
        let fallback =
                if pbtSpeculative task && isExplicitGoal (pbtGoal task)
                    then Left (cgCt (pbtGoal task))
                    else Right Nothing
         in (fallback :) <$> go rest (Just [])
    go (PreparedTask task : rest) (Just (rawOut : moreOuts)) = do
        let (verdictLine, mbFpLines) = splitProbePayload rawOut
        when (not (pbtSpeculative task)) $
            case (pbtSideProbeInfo task, mbFpLines) of
                (Just (cfg, vars, lhs, rhs), Just (fpL, fpR)) ->
                    storeSideFingerprints st cfg vars lhs rhs fpL fpR
                _ -> pure ()
        case decodeLoopString (pbtHasPolyDict task) verdictLine of
            Nothing -> do
                let fallback =
                        if pbtSpeculative task && isExplicitGoal (pbtGoal task)
                            then Left (cgCt (pbtGoal task))
                            else Right Nothing
                (fallback :) <$> go rest (Just moreOuts)
            Just outcome -> do
                when (not (pbtSpeculative task)) $
                    case pbtCacheInfo task of
                        Just (key, vars, lhs, rhs) -> storeCachedVerdict st key vars lhs rhs outcome
                        Nothing -> pure ()
                res <-
                    applyVerdictToGoal
                        st
                        cenv
                        (pbtGoal task)
                        (pbtLocSpan task)
                        (pbtSpeculative task)
                        (pbtUsedGivenCos task)
                        outcome
                (res :) <$> go rest (Just moreOuts)

    isExplicitGoal ExplicitDictGoal{} = True
    isExplicitGoal BareNominalGoal{} = False

splitProbePayload :: String -> (String, Maybe ([Word64], [Word64]))
splitProbePayload raw =
    case break (== '\x1f') raw of
        (verdict, []) -> (verdict, Nothing)
        (verdict, _ : rest1) ->
            case break (== '\x1f') rest1 of
                (sL, _ : sR) ->
                    let parseWords = traverse readMaybe . words
                     in (verdict, (,) <$> parseWords sL <*> parseWords sR)
                _ -> (verdict, Nothing)

storeSideFingerprints ::
    PluginState ->
    ObsConfig ->
    [Var] ->
    Type ->
    Type ->
    [Word64] ->
    [Word64] ->
    TcPluginM ()
storeSideFingerprints st cfg vars lhs rhs fpL fpR = do
    let cmEnv = extendCMEs emptyCME vars
    scMap <- tcPluginIO (readIORef (psSideCache st))
    let tm0 = Map.findWithDefault emptyTypeMap cfg scMap
        tm1 =
            if all (== 0) fpL
                then tm0
                else extendTypeMapWithScope tm0 cmEnv lhs fpL
        tm2 =
            if all (== 0) fpR
                then tm1
                else extendTypeMapWithScope tm1 cmEnv rhs fpR
    tcPluginIO (writeIORef (psSideCache st) (Map.insert cfg tm2 scMap))

decodeLoopString :: Maybe String -> String -> Maybe ObsCheckOutcome
decodeLoopString mbPolyDict out
    | out == "PASS" =
        pure $ case mbPolyDict of
            Just predStr -> ObsCheckInconclusive (PolymorphicClassConstraint predStr)
            Nothing -> ObsCheckVerified
    | "FAIL:" `isPrefixOf` out =
        Just (ObsCheckRefuted (drop 5 out))
    | "INCONCLUSIVE:" `isPrefixOf` out
    , Just reason <- readMaybe (drop 13 out) =
        Just (ObsCheckInconclusive reason)
    | otherwise = Nothing

applyVerdictToGoal ::
    PluginState ->
    CachedObsEnv ->
    CandidateGoal ->
    SrcSpan ->
    Bool ->
    [Coercion] ->
    ObsCheckOutcome ->
    TcPluginM (Either Ct (Maybe (EvTerm, Ct)))
applyVerdictToGoal st cenv goal locSpan speculative usedGivenCos outcome = do
    let ct = cgCt goal
        (dispLhs, dispRhs) = goalDisplayTypes goal
    case outcome of
        ObsCheckRefuted counterexample -> do
            when (not speculative) $
                emitCounterexampleOnce st locSpan dispLhs dispRhs counterexample
            pure (Left ct)
        ObsCheckInconclusive reason ->
            case (speculative, poPolicy (psOpts st), goal) of
                (True, _, ExplicitDictGoal{}) -> pure (Left ct)
                (True, _, BareNominalGoal{}) -> pure (Right Nothing)
                (_, RefuteOnly, _) -> pure (Right Nothing)
                (_, _, ExplicitDictGoal{}) -> do
                    emitInconclusiveOnce st locSpan dispLhs dispRhs (renderInconclusiveReason reason)
                    pure (Right Nothing)
                (_, _, BareNominalGoal{}) -> pure (Right Nothing)
        ObsCheckVerified ->
            case poPolicy (psOpts st) of
                RefuteOnly ->
                    case (speculative, goal) of
                        (True, ExplicitDictGoal{}) -> pure (Left ct)
                        _ -> pure (Right Nothing)
                ExplicitOnly ->
                    case goal of
                        ExplicitDictGoal{} -> do
                            when (not speculative) $
                                tcPluginTrace "dependent-obs-eq: discharged explicit goal" (ppr (ctPred ct))
                            let co = mkGoalUnivCo usedGivenCos goal
                                ev = mkExplicitGoalEv cenv goal co
                            pure (Right (Just (ev, ct)))
                        BareNominalGoal{} -> pure (Right Nothing)
                ImplicitAssume ->
                    case goal of
                        ExplicitDictGoal{} -> do
                            when (not speculative) $
                                tcPluginTrace "dependent-obs-eq: discharged explicit goal" (ppr (ctPred ct))
                            let co = mkGoalUnivCo usedGivenCos goal
                                ev = mkExplicitGoalEv cenv goal co
                            pure (Right (Just (ev, ct)))
                        BareNominalGoal{cgOrigLhs = origLhs, cgOrigRhs = origRhs} -> do
                            let co = mkPluginUnivCo usedGivenCos origLhs origRhs
                            when (not speculative) $ do
                                tcPluginTrace "dependent-obs-eq: implicitly assumed nominal equality" (ppr (ctPred ct))
                                when (poWarnAssume (psOpts st)) $
                                    emitCounterexampleOnce
                                        st
                                        locSpan
                                        origLhs
                                        origRhs
                                        "Note: assumed via policy=assume"
                            pure (Right (Just (evCoercion co, ct)))

goalDisplayTypes :: CandidateGoal -> (Type, Type)
goalDisplayTypes BareNominalGoal{cgOrigLhs = l, cgOrigRhs = r} = (l, r)
goalDisplayTypes ExplicitDictGoal{cgFlavor = flv, cgOrigLhs = l, cgOrigRhs = r} =
    case flv of
        FlavorValue -> (l, r)
        FlavorProj _ proj -> (mkAppTy proj l, mkAppTy proj r)
        FlavorRel rel -> (mkAppTys rel [l, r], mkTyConApp promotedTrueDataCon [])

mkGoalUnivCo :: [Coercion] -> CandidateGoal -> Coercion
mkGoalUnivCo usedGivenCos BareNominalGoal{cgOrigLhs = l, cgOrigRhs = r} =
    mkPluginUnivCo usedGivenCos l r
mkGoalUnivCo usedGivenCos ExplicitDictGoal{cgFlavor = flv, cgOrigLhs = l, cgOrigRhs = r} =
    case flv of
        FlavorValue -> mkPluginUnivCo usedGivenCos l r
        FlavorProj _ proj -> mkPluginUnivCo usedGivenCos (mkAppTy proj l) (mkAppTy proj r)
        FlavorRel rel -> mkPluginUnivCo usedGivenCos (mkAppTys rel [l, r]) (mkTyConApp promotedTrueDataCon [])

mkPluginUnivCo :: [Coercion] -> Type -> Type -> Coercion
mkPluginUnivCo usedGivenCos lhs rhs =
    mkUnivCoAddTypeDeps
        (PluginProv "dependent-obs-eq")
        (mkUnivCoDeps usedGivenCos)
        Nominal
        lhs
        rhs

mkExplicitGoalEv :: CachedObsEnv -> CandidateGoal -> Coercion -> EvTerm
mkExplicitGoalEv _ BareNominalGoal{} co = evCoercion co
mkExplicitGoalEv cenv ExplicitDictGoal{cgClass = cls, cgClassArgs = clsArgs, cgFlavor = flv, cgKind = domKind, cgOrigLhs = lhs, cgOrigRhs = rhs} co =
    let clsDc = tyConSingleDataCon (classTyCon cls)
        mkPropEq eqK eqL eqCo =
            let reflBase = mkCoreApps (Var (dataConWrapId (ceReflDc cenv))) [Type eqK, Type eqL]
                tyEqCo = mkSubCo (mkTyConAppCo Nominal (ceTyEqTc cenv) [mkNomReflCo eqK, mkNomReflCo eqL, eqCo])
             in mkCast reflBase tyEqCo
        methodExpr =
            case flv of
                FlavorValue -> mkPropEq domKind lhs co
                FlavorProj repKind projTy ->
                    let projLhs = mkAppTy projTy lhs
                        eqExpr = mkPropEq repKind projLhs co
                     in mkCoreApps
                            (Var (dataConWrapId (ceUnsafeObsEquivOnDc cenv)))
                            [Type domKind, Type repKind, Type projTy, Type lhs, Type rhs, eqExpr]
                FlavorRel relTy ->
                    let relApp = mkAppTys relTy [lhs, rhs]
                        eqExpr = mkPropEq boolTy relApp co
                     in mkCoreApps
                            (Var (dataConWrapId (ceUnsafeObsEquivByDc cenv)))
                            [Type domKind, Type relTy, Type lhs, Type rhs, eqExpr]
     in EvExpr (mkCoreApps (Var (dataConWrapId clsDc)) (map Type clsArgs ++ [methodExpr]))

emitCounterexampleOnce :: PluginState -> SrcSpan -> Type -> Type -> String -> TcPluginM ()
emitCounterexampleOnce st sp lhs rhs details =
    emitPluginDocOnce st sp lhs rhs ("refuted|" ++ details) $
        hang
            (text "Observational equivalence refuted for" <+> hcat [quotes (ppr lhs <+> text "~" <+> ppr rhs), text ":"])
            2
            (text details)

emitInconclusiveOnce :: PluginState -> SrcSpan -> Type -> Type -> String -> TcPluginM ()
emitInconclusiveOnce st sp lhs rhs details =
    emitPluginDocOnce st sp lhs rhs ("inconclusive|" ++ details) $
        hang
            (text "Observational equivalence inconclusive for" <+> hcat [quotes (ppr lhs <+> text "~" <+> ppr rhs), text ":"])
            2
            (text details)

emitPluginDocOnce :: PluginState -> SrcSpan -> Type -> Type -> String -> SDoc -> TcPluginM ()
emitPluginDocOnce st sp lhs rhs tag detailsDoc = do
    let spKey = showSDocUnsafe (ppr sp)
        summary = showSDocUnsafe (ppr lhs <+> text "~" <+> ppr rhs) ++ "|" ++ tag
    seen <- tcPluginIO (readIORef (psReportedSpans st))
    when (not ((spKey, summary) `Set.member` seen)) $ do
        tcPluginIO (writeIORef (psReportedSpans st) (Set.insert (spKey, summary) seen))
        unsafeTcPluginTcM $ do
            dflags <- getDynFlags
            when (not (gopt Opt_DeferTypeErrors dflags))
                $ addErrAt sp
                $ TcRnUnknownMessage (mkSimpleUnknownDiagnostic (mkPlainError noHints detailsDoc))

-- ---------------------------------------------------------------------------
-- Peeling and Evaluating ObsConfig + ObsDomain Overrides
-- ---------------------------------------------------------------------------

{- Note [Composable ObsConfig peeling over local bindings]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
An explicit configuration argument such as @forVar n evenDom localCfg@ or
@forType evenDom localCfg@ can wrap domain overrides around a same-module or
computed @ObsConfig@ binding:

1. Outer 'forVar', 'forType', and scalar modifier layers ('peelTypeLayers')
   peel off before inspecting the inner @ObsConfig@ term. Free @foreach@
   binders such as @n@ stay in 'LayerVarDomain', so if the inner @ObsConfig@
   requires bytecode @Show@ evaluation ('evaluateShowableCfg'), 'reifyTypeToCore'
   receives a closed @ObsConfig@ type and 'applyConfigLayers' re-attaches all
   collected 'pocVarDomains' and 'pocTypeDomains' afterward.
2. Unoptimized Core from 'dsTopLHsBinds' wraps overloaded numeric literals in
   local dictionary @let@ bindings and @fromInteger \@Natural $dNum (IS n#)@
   calls. 'peelObsConfigCore' tracks local @let@ bindings in a 'VarEnv' and
   'extractNatCore' inspects the numeric payload argument so local @ObsConfig@
   bindings peel directly without bytecode evaluation.
-}

data ParsedObsConfig = ParsedObsConfig
    { pocScalar :: !ObsConfig
    , pocVarDomains :: ![(Word64, Type, Either Type CoreExpr)]
    , pocTypeDomains :: ![(Type, Either Type CoreExpr)]
    }

data ConfigLayer
    = LayerVarDomain !Word64 !Type !(Either Type CoreExpr)
    | LayerTypeDomain !Type !(Either Type CoreExpr)
    | LayerScalarMod !(ObsConfig -> ObsConfig)

emptyParsedConfig :: ObsConfig -> ParsedObsConfig
emptyParsedConfig cfg =
    ParsedObsConfig
        { pocScalar = cfg
        , pocVarDomains = []
        , pocTypeDomains = []
        }

applyConfigLayers :: [ConfigLayer] -> ParsedObsConfig -> ParsedObsConfig
applyConfigLayers [] cfg = cfg
applyConfigLayers (layer : rest) inner0 =
    let inner = applyConfigLayers rest inner0
     in case layer of
            LayerVarDomain k dTy src ->
                inner{pocVarDomains = (k, dTy, src) : pocVarDomains inner}
            LayerTypeDomain dTy src ->
                inner{pocTypeDomains = (dTy, src) : pocTypeDomains inner}
            LayerScalarMod f ->
                inner{pocScalar = f (pocScalar inner)}

peelTypeLayers :: Int -> Type -> ([ConfigLayer], Type)
peelTypeLayers 0 ty = ([], ty)
peelTypeLayers fuel ty0 =
    case coreFullView ty0 of
        TyConApp tc args ->
            let cleanOcc = stripSynthPrefix (getOccString (tyConName tc))
             in case (cleanOcc, args) of
                    ("forVar", [domTy, targetTy, domArgTy, innerTy])
                        | Just targetV <- extractVarFromType targetTy ->
                            let (rest, baseTy) = peelTypeLayers (fuel - 1) innerTy
                             in (LayerVarDomain (getKey (getUnique targetV)) domTy (Left domArgTy) : rest, baseTy)
                    ("forType", [domTy, domArgTy, innerTy]) ->
                        let (rest, baseTy) = peelTypeLayers (fuel - 1) innerTy
                         in (LayerTypeDomain domTy (Left domArgTy) : rest, baseTy)
                    (fn, [nTy, innerTy])
                        | Just n <- isNumLitTy (coreFullView nTy)
                        , Just modFn <- scalarModFn fn (fromInteger (max 0 n)) ->
                            let (rest, baseTy) = peelTypeLayers (fuel - 1) innerTy
                             in (LayerScalarMod modFn : rest, baseTy)
                    _ -> ([], ty0)
        _ -> ([], ty0)

extractVarFromType :: Type -> Maybe Var
extractVarFromType t =
    case coreFullView t of
        TermVarTy v -> Just v
        TyVarTy tv -> Just tv
        _ -> Nothing

evalParsedObsConfig ::
    PluginState ->
    CachedObsEnv ->
    EvBindsVar ->
    SrcSpan ->
    Bool ->
    Type ->
    TcM (Maybe ParsedObsConfig)
evalParsedObsConfig st cenv evBindsVar locSpan speculative cfgTy = do
    gblEnv <- getGblEnv
    localDefs <- getCachedModuleDefs st evBindsVar gblEnv
    let baseCfg = poConfig (psOpts st)
        (outerLayers, innerTy) = peelTypeLayers 24 cfgTy
    mbDirect <- peelObsConfigType localDefs baseCfg 24 innerTy
    case mbDirect of
        Just parsed -> pure (Just (applyConfigLayers outerLayers parsed))
        Nothing -> do
            mbCore <- reifyTypeToCore cenv emptyUFM innerTy
            case mbCore of
                Nothing -> pure Nothing
                Just cfgExpr
                    | not (exprType cfgExpr `tcEqType` mkTyConApp (ceObsConfigTc cenv) []) ->
                        pure Nothing
                    | Just parsed <- peelObsConfigCore localDefs baseCfg emptyVarEnv 24 cfgExpr ->
                        pure (Just (applyConfigLayers outerLayers parsed))
                    | otherwise -> do
                        showCls <- lookupOrig (moduleNameToGhcInternal "GHC.Internal.Show") (mkTcOcc "Show") >>= tcLookupClass
                        instEnvs <- tcGetInstEnvs
                        case resolveClassDict cenv emptyTypeMap instEnvs (mkClassPred showCls [mkTyConApp (ceObsConfigTc cenv) []]) of
                            Nothing -> pure Nothing
                            Just showDict ->
                                case classMethods showCls of
                                    (_ : showId : _) -> fmap (applyConfigLayers outerLayers) <$> evaluateShowableCfg showId showDict cfgExpr
                                    (showId : _) -> fmap (applyConfigLayers outerLayers) <$> evaluateShowableCfg showId showDict cfgExpr
                                    [] -> pure Nothing
  where
    moduleNameToGhcInternal str =
        mkModule (stringToUnit "ghc-internal") (mkModuleName str)

    evaluateShowableCfg showId showDict cfgExpr = do
        let cfgKind = mkTyConApp (ceObsConfigTc cenv) []
            strExpr = mkCoreApps (Var showId) [Type cfgKind, showDict, cfgExpr]
            ioExpr = mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, strExpr]
        mbOuts <- runCoreIOStringBatch st cenv evBindsVar locSpan (not speculative) [ioExpr]
        pure $ case mbOuts of
            Just [s] -> fmap emptyParsedConfig (parseShownObsConfig s)
            _ -> Nothing

peelObsConfigType :: NameEnv (Id, CoreExpr) -> ObsConfig -> Int -> Type -> TcM (Maybe ParsedObsConfig)
peelObsConfigType localDefs baseCfg = go
  where
    go 0 _ = pure Nothing
    go fuel ty0
        | Just cfg <- decodePromotedObsConfig ty0 = pure (Just (emptyParsedConfig cfg))
        | otherwise =
            case coreFullView ty0 of
                TermVarTy v -> pure (peelVar (fuel - 1) v)
                TyConApp tc args ->
                    let cleanOcc = stripSynthPrefix (getOccString (tyConName tc))
                     in case (cleanOcc, args) of
                            ("DefaultObsConfig", []) -> pure (Just (emptyParsedConfig baseCfg))
                            ("defaultObsConfig", []) -> pure (Just (emptyParsedConfig baseCfg))
                            ("totalObsConfig", []) -> pure (Just (emptyParsedConfig baseCfg{obsPartialPct = 0}))
                            ("forVar", [domTy, targetTy, domArgTy, innerTy])
                                | Just targetV <- extractVarFromType targetTy -> do
                                    mbInner <- go (fuel - 1) innerTy
                                    pure $ do
                                        inner <- mbInner
                                        pure inner{pocVarDomains = (getKey (getUnique targetV), domTy, Left domArgTy) : pocVarDomains inner}
                            ("forType", [domTy, domArgTy, innerTy]) -> do
                                mbInner <- go (fuel - 1) innerTy
                                pure $ do
                                    inner <- mbInner
                                    pure inner{pocTypeDomains = (domTy, Left domArgTy) : pocTypeDomains inner}
                            (fn, [nTy, innerTy])
                                | Just n <- isNumLitTy (coreFullView nTy)
                                , Just modFn <- scalarModFn fn (fromInteger (max 0 n)) -> do
                                    mbInner <- go (fuel - 1) innerTy
                                    pure $ do
                                        inner <- mbInner
                                        pure inner{pocScalar = modFn (pocScalar inner)}
                            (fn, []) ->
                                case peelByOcc localDefs baseCfg (fuel - 1) fn of
                                    Just parsed -> pure (Just parsed)
                                    Nothing -> do
                                        mbOwner <- recoverFamilyOwnerId tc
                                        pure (mbOwner >>= peelVar (fuel - 1))
                            _ -> pure Nothing
                _ -> pure Nothing

    peelVar fuel v
        | getOccString v == "defaultObsConfig" = Just (emptyParsedConfig baseCfg)
        | getOccString v == "totalObsConfig" = Just (emptyParsedConfig baseCfg{obsPartialPct = 0})
        | Just (_, rhs) <- lookupNameEnv localDefs (idName v) =
            peelObsConfigCore localDefs baseCfg emptyVarEnv fuel rhs
        | Just parsed <- peelByOcc localDefs baseCfg fuel (getOccString v) =
            Just parsed
        | CoreUnfolding{uf_tmpl = rhs} <- realIdUnfolding v =
            peelObsConfigCore localDefs baseCfg emptyVarEnv fuel rhs
        | otherwise = Nothing

stripSynthPrefix :: String -> String
stripSynthPrefix occ
    | "U:@" `isPrefixOf` occ = reverse (takeWhile (/= ':') (reverse occ))
    | "U:" `isPrefixOf` occ = drop 2 occ
    | "T:" `isPrefixOf` occ = drop 2 occ
    | otherwise = occ

peelByOcc :: NameEnv (Id, CoreExpr) -> ObsConfig -> Int -> String -> Maybe ParsedObsConfig
peelByOcc localDefs baseCfg fuel occ =
    case [rhs | (fnId, rhs) <- nonDetEltsUFM localDefs, getOccString fnId == occ] of
        rhs : _ -> peelObsConfigCore localDefs baseCfg emptyVarEnv fuel rhs
        [] -> Nothing

peelObsConfigCore ::
    NameEnv (Id, CoreExpr) ->
    ObsConfig ->
    VarEnv CoreExpr ->
    Int ->
    CoreExpr ->
    Maybe ParsedObsConfig
peelObsConfigCore localDefs baseCfg = go
  where
    go _ 0 _ = Nothing
    go varLets fuel expr0 =
        case stripTicks expr0 of
            Let (NonRec b r) body ->
                go (extendVarEnv varLets b r) fuel body
            Let (Rec prs) body ->
                go (extendVarEnvList varLets prs) fuel body
            stripped ->
                let (hd, args) = collectArgs stripped
                    tyArgs = [t | Type t <- args]
                    valArgs = [a | a <- args, not (isTypeArg a)]
                 in case hd of
                        Var fn
                            | getOccString fn == "ObsConfig"
                            , [a, b, c, d, e, f] <- valArgs -> do
                                n1 <- extractNatCore varLets (fuel - 1) a
                                n2 <- extractNatCore varLets (fuel - 1) b
                                n3 <- extractNatCore varLets (fuel - 1) c
                                n4 <- extractNatCore varLets (fuel - 1) d
                                n5 <- extractNatCore varLets (fuel - 1) e
                                n6 <- extractNatCore varLets (fuel - 1) f
                                Just $
                                    emptyParsedConfig
                                        ObsConfig
                                            { obsTests = max 1 n1
                                            , obsMaxSize = n2
                                            , obsApproxDepth = max 1 n3
                                            , obsPartialPct = min 100 n4
                                            , obsTimeoutUs = max 1 n5
                                            , obsSeed = n6
                                            }
                            | getOccString fn == "defaultObsConfig"
                            , null valArgs ->
                                Just (emptyParsedConfig baseCfg)
                            | getOccString fn == "totalObsConfig"
                            , null valArgs ->
                                Just (emptyParsedConfig baseCfg{obsPartialPct = 0})
                            | getOccString fn == "forType"
                            , domTy : _ <- tyArgs
                            , [domExpr, innerExpr] <- valArgs -> do
                                inner <- go varLets (fuel - 1) innerExpr
                                pure inner{pocTypeDomains = (domTy, Right (substVarLets varLets domExpr)) : pocTypeDomains inner}
                            | getOccString fn == "forVar"
                            , domTy : _ <- tyArgs
                            , [targetExpr, domExpr, innerExpr] <- valArgs
                            , Var targetV <- stripTicks targetExpr -> do
                                inner <- go varLets (fuel - 1) innerExpr
                                pure
                                    inner
                                        { pocVarDomains =
                                            (getKey (getUnique targetV), domTy, Right (substVarLets varLets domExpr))
                                                : pocVarDomains inner
                                        }
                            | [nExpr, innerExpr] <- valArgs
                            , Just n <- extractNatCore varLets (fuel - 1) nExpr
                            , Just inner <- go varLets (fuel - 1) innerExpr
                            , Just modFn <- scalarModFn (getOccString fn) n ->
                                Just inner{pocScalar = modFn (pocScalar inner)}
                            | null valArgs ->
                                lookupRhs varLets fn >>= go varLets (fuel - 1)
                        _ -> Nothing

    stripTicks (Tick _ e) = stripTicks e
    stripTicks (Cast e _) = stripTicks e
    stripTicks e = e

    substVarLets varLets e
        | isEmptyVarEnv varLets = e
        | otherwise =
            let pairs = [(v, r) | v <- exprSomeFreeVarsList isId e, Just r <- [lookupVarEnv varLets v]]
             in if null pairs
                    then e
                    else
                        let fvs = exprSomeFreeVarsList (const True) e ++ concatMap (exprSomeFreeVarsList (const True) . snd) pairs
                            inScope = mkInScopeSet (mkVarSet (fvs ++ map fst pairs))
                            subst = CoreSubst.extendIdSubstList (CoreSubst.mkEmptySubst inScope) pairs
                         in CoreSubst.substExpr subst e

    lookupRhs varLets fn
        | Just rhs <- lookupVarEnv varLets fn = Just rhs
        | Just (_, rhs) <- lookupNameEnv localDefs (idName fn) = Just rhs
        | rhs : _ <- [r | (b, r) <- nonDetEltsUFM localDefs, getOccString b == getOccString fn] = Just rhs
        | CoreUnfolding{uf_tmpl = rhs} <- realIdUnfolding fn = Just rhs
        | otherwise = Nothing

    extractNatCore _ 0 _ = Nothing
    extractNatCore varLets fuel e0 =
        case stripTicks e0 of
            Lit (LitNumber _ n)
                | n >= 0 -> Just (fromInteger n)
            Let (NonRec b r) body ->
                extractNatCore (extendVarEnv varLets b r) fuel body
            Let (Rec prs) body ->
                extractNatCore (extendVarEnvList varLets prs) fuel body
            stripped ->
                case collectArgs stripped of
                    (Var fn, args) ->
                        let valArgs = [x | x <- args, not (isTypeArg x)]
                         in case reverse valArgs of
                                lastArg : _
                                    | getOccString fn `elem` ["NS", "IS", "I#", "W#", "fromInteger", "naturalFromInteger", "integerFromInt", "wordToNatural"] ->
                                        extractNatCore varLets fuel lastArg
                                [] -> lookupRhs varLets fn >>= extractNatCore varLets (fuel - 1)
                                _ -> Nothing
                    _ -> Nothing

scalarModFn :: String -> Natural -> Maybe (ObsConfig -> ObsConfig)
scalarModFn fn n =
    case fn of
        "setTests" -> Just (\cfg -> cfg{obsTests = max 1 n})
        "setMaxSize" -> Just (\cfg -> cfg{obsMaxSize = n})
        "setApproxDepth" -> Just (\cfg -> cfg{obsApproxDepth = max 1 n})
        "setPartialPct" -> Just (\cfg -> cfg{obsPartialPct = min 100 n})
        "setTimeoutUs" -> Just (\cfg -> cfg{obsTimeoutUs = max 1 n})
        "setSeed" -> Just (\cfg -> cfg{obsSeed = n})
        _ -> Nothing

decodePromotedObsConfig :: Type -> Maybe ObsConfig
decodePromotedObsConfig ty =
    case splitTyConApp_maybe (coreFullView ty) of
        Just (tc, [a, b, c, d, e, f])
            | Just dc <- isPromotedDataCon_maybe tc
            , getOccString (dataConName dc) == "ObsConfig" -> do
                tTests <- isNumLitTy (coreFullView a)
                tMaxSz <- isNumLitTy (coreFullView b)
                tDepth <- isNumLitTy (coreFullView c)
                tPart <- isNumLitTy (coreFullView d)
                tTmo <- isNumLitTy (coreFullView e)
                tSeed <- isNumLitTy (coreFullView f)
                pure
                    ObsConfig
                        { obsTests = fromInteger (max 1 tTests)
                        , obsMaxSize = fromInteger (max 0 tMaxSz)
                        , obsApproxDepth = fromInteger (max 1 tDepth)
                        , obsPartialPct = fromInteger (min 100 (max 0 tPart))
                        , obsTimeoutUs = fromInteger (max 1 tTmo)
                        , obsSeed = fromInteger (max 0 tSeed)
                        }
        _ -> Nothing

parseShownObsConfig :: String -> Maybe ObsConfig
parseShownObsConfig s = do
    let digitsAndSpaces c = if c `elem` ("0123456789" :: String) then c else ' '
    case mapMaybe readMaybe (words (map digitsAndSpaces s)) :: [Natural] of
        [n1, n2, n3, n4, n5, n6] ->
            Just
                ObsConfig
                    { obsTests = max 1 n1
                    , obsMaxSize = n2
                    , obsApproxDepth = max 1 n3
                    , obsPartialPct = min 100 n4
                    , obsTimeoutUs = max 1 n5
                    , obsSeed = n6
                    }
        _ -> Nothing

-- ---------------------------------------------------------------------------
-- Building the Bytecode Test Harness (Value, Projection, Relation, & Guards)
-- ---------------------------------------------------------------------------

data DomainOps = DomainOps
    { doType :: !Type
    , doDict :: !CoreExpr
    , doGenTotal :: !CoreExpr
    , doGenPartial :: !CoreExpr
    , doShrink :: !CoreExpr
    , doApprox :: !CoreExpr
    , doShow :: !CoreExpr
    }

data VarSamplingSpec = VarSamplingSpec
    { vssOrigVar :: !Var
    , vssParamId :: !Id
    , vssDomTy :: !Type
    , vssGenPartial :: !CoreExpr
    , vssShrink :: !CoreExpr
    , vssShow :: !CoreExpr
    , vssCustomPred :: !(Maybe CoreExpr)
    , vssBaselineOps :: !(Maybe DomainOps)
    , vssIsOverridden :: !Bool
    }

buildGoalBcoTask ::
    PluginState ->
    CachedObsEnv ->
    IORef AdtCache ->
    ParsedObsConfig ->
    [TestableGuard] ->
    GoalFlavor ->
    Kind ->
    Type ->
    Type ->
    TcM (Maybe (CoreExpr, Maybe String, Bool))
buildGoalBcoTask st cenv adtCacheRef parsedCfg activeGuards flv0 domKind0 lhs0 rhs0 = do
    instEnvs <- tcGetInstEnvs
    let cfg = pocScalar parsedCfg
        extraTys0 = flavorExtraTypes flv0 ++ concat [[tgKind g, tgLhs g, tgRhs g] | g <- activeGuards]
        rawFree = collectFreeTermAndTyVars (domKind0 : lhs0 : rhs0 : extraTys0)
        typeSkolems = [tv | tv <- rawFree, isTyVar tv, tcIsLiftedTypeKind (tyVarKind tv)]
        hkSkolems = [tv | tv <- rawFree, isTyVar tv, isUnaryTypeConKind (tyVarKind tv)]
        allPolySet = mkVarSet (typeSkolems ++ hkSkolems)
        orderingCarrier = mkTyConTy (ceOrderingTc cenv)
    (mbPolyClass, needsIntFallback) <-
        detectPolyClassConstraint instEnvs orderingCarrier allPolySet (domKind0 : lhs0 : rhs0 : extraTys0)
    let hasPolyDict =
            case mbPolyClass of
                Just p -> Just p
                Nothing
                    | not (null hkSkolems) -> Just "higher-kinded type constructor variable"
                    | otherwise -> Nothing
        scalarCarrier = if needsIntFallback then intTy else orderingCarrier
        polySubst =
            TySubst.extendTvSubstList
                (TySubst.mkEmptySubst (mkInScopeSet (mkVarSet rawFree)))
                ([(tv, scalarCarrier) | tv <- typeSkolems] ++ [(tv, mkTyConTy listTyCon) | tv <- hkSkolems])
        substPoly = substTermAndTyVars polySubst
        domKind = substPoly domKind0
        lhs = substPoly lhs0
        rhs = substPoly rhs0
        flv = substFlavor substPoly flv0
        guards =
            [ g{tgKind = substPoly (tgKind g), tgLhs = substPoly (tgLhs g), tgRhs = substPoly (tgRhs g)}
            | g <- activeGuards
            ]
        valVars =
            [ (v, vk)
            | v <- collectFreeTermAndTyVars (lhs : rhs : flavorExtraTypes flv ++ concat [[tgLhs g, tgRhs g] | g <- guards])
            , let vk = substPoly (if isTyVar v then tyVarKind v else varType v)
            , not (tcIsLiftedTypeKind vk)
            , tcIsLiftedTypeKind (typeKind vk)
            ]

    if not (noFreeVarsOfType domKind && isTyFamFree domKind && all (noFreeVarsOfType . snd) valVars && all (isTyFamFree . snd) valVars && flavorClosed flv)
        then pure Nothing
        else do
            paramIds <- forM (zip ([1 :: Int ..]) valVars) $ \(idx, (v, domTy)) -> do
                u <- newUnique
                let occ = mkVarOcc ("obs_arg_" ++ show idx ++ "_" ++ getOccString v)
                pure (v, domTy, mkSysLocal (fsLit (occNameString occ)) u ManyTy domTy)
            let varEnv = listToUFM [(origV, pid) | (origV, _, pid) <- paramIds]

            mbVarSpecs <- traverse (resolveVarSpec cenv adtCacheRef instEnvs varEnv parsedCfg) paramIds
            mbLhsCore <- reifyTypeToCore cenv varEnv lhs
            mbRhsCore <- reifyTypeToCore cenv varEnv rhs

            case (sequence mbVarSpecs, mbLhsCore, mbRhsCore) of
                (Just varSpecs, Just lhsCore, Just rhsCore)
                    | exprType lhsCore `tcEqType` domKind && exprType rhsCore `tcEqType` domKind -> do
                        (envTy, envGenExpr, envShrinkExpr, envShowExpr, bindEnvVars) <-
                            foldEnvComponents
                                cenv
                                [ ( vssDomTy sp
                                  , vssGenPartial sp
                                  , vssShrink sp
                                  , mkCoreApps (Var (ceNamedShowId cenv)) [Type (vssDomTy sp), mkCharListExpr (getOccString (vssOrigVar sp)), vssShow sp]
                                  , vssParamId sp
                                  )
                                | sp <- varSpecs
                                ]

                        -- Baseline boundary sweep when any overridden variable has no Given guard mentioning it
                        let guardedVarKeys = Set.fromList [getKey (getUnique v) | g <- guards, v <- tgVars g]
                            hasUnguardedOverride =
                                any
                                    (\sp -> vssIsOverridden sp && not (getKey (getUnique (vssOrigVar sp)) `Set.member` guardedVarKeys))
                                    varSpecs
                        mbBaseExpr <-
                            if hasUnguardedOverride
                                then case traverse vssBaselineOps varSpecs of
                                    Just baseOpsList -> do
                                        (_, baseGenFn, _, _, _) <-
                                            foldEnvComponents
                                                cenv
                                                [ (doType bOps, doGenPartial bOps, doShrink bOps, doShow bOps, vssParamId sp)
                                                | (sp, bOps) <- zip varSpecs baseOpsList
                                                ]
                                        pure (mkCoreApps (Var (ceJustBaselineId cenv)) [Type envTy, baseGenFn])
                                    Nothing -> pure (mkCoreApps (Var (ceNoBaselineId cenv)) [Type envTy])
                                else pure (mkCoreApps (Var (ceNoBaselineId cenv)) [Type envTy])

                        mbGuardExpr <-
                            buildGuardExpr cenv adtCacheRef instEnvs varEnv cfg envTy bindEnvVars varSpecs guards
                        case mbGuardExpr of
                            Nothing -> pure Nothing
                            Just guardExpr -> do
                                cfgExpr <- buildObsConfigCore cenv cfg
                                envArgL <- freshLocal "obs_env_l" envTy
                                envArgR <- freshLocal "obs_env_r" envTy
                                let evalLhsFn = Lam envArgL (bindEnvVars (Var envArgL) lhsCore)
                                    evalRhsFn = Lam envArgR (bindEnvVars (Var envArgR) rhsCore)

                                case flv of
                                    FlavorValue -> do
                                        mbResOps <- resolveDomainOps cenv adtCacheRef instEnvs domKind
                                        case mbResOps of
                                            Nothing -> pure Nothing
                                            Just resOps -> do
                                                let loopCall =
                                                        mkCoreApps
                                                            (Var (ceRunLoopId cenv))
                                                            [ Type envTy
                                                            , Type domKind
                                                            , cfgExpr
                                                            , mbBaseExpr
                                                            , guardExpr
                                                            , envGenExpr
                                                            , envShrinkExpr
                                                            , envShowExpr
                                                            , doApprox resOps
                                                            , evalLhsFn
                                                            , evalRhsFn
                                                            ]
                                                scMap <- liftIO (readIORef (psSideCache st))
                                                let cmEnv = extendCMEs emptyCME (map fst valVars)
                                                    sideMap = Map.findWithDefault emptyTypeMap cfg scMap
                                                    hasCachedFp =
                                                        isJust (lookupTypeMapWithScope sideMap cmEnv lhs0)
                                                            && isJust (lookupTypeMapWithScope sideMap cmEnv rhs0)
                                                    wantFp =
                                                        not (any vssIsOverridden varSpecs)
                                                            && null guards
                                                            && isNothing hasPolyDict
                                                            && length valVars <= 3
                                                            && not hasCachedFp
                                                if not wantFp
                                                    then pure (Just (loopCall, hasPolyDict, False))
                                                    else do
                                                        let fpLCall =
                                                                mkCoreApps
                                                                    (Var (ceEvalSideFpId cenv))
                                                                    [Type envTy, Type domKind, cfgExpr, envGenExpr, doApprox resOps, evalLhsFn]
                                                            fpRCall =
                                                                mkCoreApps
                                                                    (Var (ceEvalSideFpId cenv))
                                                                    [Type envTy, Type domKind, cfgExpr, envGenExpr, doApprox resOps, evalRhsFn]
                                                        combined <- chainSepIO cenv "\x1f" [loopCall, fpLCall, fpRCall]
                                                        pure (Just (combined, hasPolyDict, True))
                                    FlavorProj repKind projTy -> do
                                        mbRepOps <- resolveDomainOps cenv adtCacheRef instEnvs repKind
                                        mbProjCore <- reifyTypeToCore cenv varEnv projTy
                                        case (mbRepOps, mbProjCore) of
                                            (Just repOps, Just projCore)
                                                | Just (_, _, _, pDom, pRep) <- splitFunTy_maybe (exprType projCore)
                                                , pDom `tcEqType` domKind && pRep `tcEqType` repKind -> do
                                                    let loopCall =
                                                            mkCoreApps
                                                                (Var (ceRunOnLoopId cenv))
                                                                [ Type envTy
                                                                , Type domKind
                                                                , Type repKind
                                                                , cfgExpr
                                                                , mbBaseExpr
                                                                , guardExpr
                                                                , envGenExpr
                                                                , envShrinkExpr
                                                                , envShowExpr
                                                                , doApprox repOps
                                                                , projCore
                                                                , evalLhsFn
                                                                , evalRhsFn
                                                                ]
                                                    pure (Just (loopCall, hasPolyDict, False))
                                            _ -> pure Nothing
                                    FlavorRel relTy -> do
                                        mbRelCore <- reifyTypeToCore cenv varEnv relTy
                                        case mbRelCore of
                                            Just relCore
                                                | let (_, relArrows, relRes) = splitFunTys (exprType relCore)
                                                , [d1, d2] <- map scaledThing relArrows
                                                , d1 `tcEqType` domKind && d2 `tcEqType` domKind && relRes `tcEqType` boolTy -> do
                                                    let relNameStr = renderRelName relTy
                                                        loopCall =
                                                            mkCoreApps
                                                                (Var (ceRunByLoopId cenv))
                                                                [ Type envTy
                                                                , Type domKind
                                                                , cfgExpr
                                                                , mbBaseExpr
                                                                , guardExpr
                                                                , envGenExpr
                                                                , envShrinkExpr
                                                                , envShowExpr
                                                                , mkCharListExpr relNameStr
                                                                , relCore
                                                                , evalLhsFn
                                                                , evalRhsFn
                                                                ]
                                                    pure (Just (loopCall, hasPolyDict, False))
                                            _ -> pure Nothing
                _ -> pure Nothing
  where
    flavorExtraTypes FlavorValue = []
    flavorExtraTypes (FlavorProj repK pTy) = [repK, pTy]
    flavorExtraTypes (FlavorRel rTy) = [rTy]

    substFlavor _ FlavorValue = FlavorValue
    substFlavor sub (FlavorProj repK pTy) = FlavorProj (sub repK) (sub pTy)
    substFlavor sub (FlavorRel rTy) = FlavorRel (sub rTy)

    flavorClosed FlavorValue = True
    flavorClosed (FlavorProj repK _) = noFreeVarsOfType repK && isTyFamFree repK
    flavorClosed (FlavorRel _) = True

    renderRelName ty =
        case splitTyConApp_maybe (coreFullView ty) of
            Just (tc, _) -> stripSynthPrefix (getOccString (tyConName tc))
            Nothing -> showSDocUnsafe (ppr ty)

resolveVarSpec ::
    CachedObsEnv ->
    IORef AdtCache ->
    InstEnvs ->
    UniqFM Var Id ->
    ParsedObsConfig ->
    (Var, Type, Id) ->
    TcM (Maybe VarSamplingSpec)
resolveVarSpec cenv adtCacheRef instEnvs varEnv parsedCfg (origV, domTy, pid) = do
    mbBaseOps <- resolveDomainOps cenv adtCacheRef instEnvs domTy
    let varKey = getKey (getUnique origV)
        mbOverrideSrc =
            case [src | (k, dTy, src) <- pocVarDomains parsedCfg, k == varKey, dTy `tcEqType` domTy] of
                src : _ -> Just src
                [] ->
                    case [src | (dTy, src) <- pocTypeDomains parsedCfg, dTy `tcEqType` domTy] of
                        src : _ -> Just src
                        [] -> Nothing
    case mbOverrideSrc of
        Nothing ->
            pure $ case mbBaseOps of
                Nothing -> Nothing
                Just bOps ->
                    Just
                        VarSamplingSpec
                            { vssOrigVar = origV
                            , vssParamId = pid
                            , vssDomTy = domTy
                            , vssGenPartial = doGenPartial bOps
                            , vssShrink = doShrink bOps
                            , vssShow = doShow bOps
                            , vssCustomPred = Nothing
                            , vssBaselineOps = Just bOps
                            , vssIsOverridden = False
                            }
        Just src -> do
            mbDomExpr <- case src of
                Right expr -> pure (Just expr)
                Left domArgTy -> reifyTypeToCore cenv varEnv domArgTy
            pure $ case mbDomExpr of
                Nothing -> Nothing
                Just domExpr ->
                    Just
                        VarSamplingSpec
                            { vssOrigVar = origV
                            , vssParamId = pid
                            , vssDomTy = domTy
                            , vssGenPartial = mkCoreApps (Var (ceDomGenPartialId cenv)) [Type domTy, domExpr]
                            , vssShrink = mkCoreApps (Var (ceDomShrinkId cenv)) [Type domTy, domExpr]
                            , vssShow = mkCoreApps (Var (ceDomShowId cenv)) [Type domTy, domExpr]
                            , vssCustomPred = Just (mkCoreApps (Var (ceDomPredId cenv)) [Type domTy, domExpr])
                            , vssBaselineOps = mbBaseOps
                            , vssIsOverridden = True
                            }

buildGuardExpr ::
    CachedObsEnv ->
    IORef AdtCache ->
    InstEnvs ->
    UniqFM Var Id ->
    ObsConfig ->
    Type ->
    (CoreExpr -> CoreExpr -> CoreExpr) ->
    [VarSamplingSpec] ->
    [TestableGuard] ->
    TcM (Maybe CoreExpr)
buildGuardExpr cenv adtCacheRef instEnvs varEnv cfg envTy bindEnvVars varSpecs guards = do
    dflags <- getDynFlags
    let plat = targetPlatform dflags
        tmoIntExpr = mkIntExpr plat (toInteger (max 1 (obsTimeoutUs cfg)))
        depthIntExpr = mkIntExpr plat (toInteger (max 2 (obsApproxDepth cfg)))
        alwaysExpr = mkCoreApps (Var (ceAlwaysHoldsId cenv)) [Type envTy]

    domPredExprs <- forM [(vssParamId sp, pr) | sp <- varSpecs, Just pr <- [vssCustomPred sp]] $ \(pid, predFn) -> do
        envArg <- freshLocal "obs_dpred_env" envTy
        let body = bindEnvVars (Var envArg) (App predFn (Var pid))
        pure (mkCoreApps (Var (cePredGuardId cenv)) [Type envTy, tmoIntExpr, Lam envArg body])

    mbGivenExprs <- forM guards $ \g -> do
        mbGOps <- resolveDomainOps cenv adtCacheRef instEnvs (tgKind g)
        mbGLhs <- reifyTypeToCore cenv varEnv (tgLhs g)
        mbGRhs <- reifyTypeToCore cenv varEnv (tgRhs g)
        case (mbGOps, mbGLhs, mbGRhs) of
            (Just gOps, Just gLhsCore, Just gRhsCore)
                | exprType gLhsCore `tcEqType` tgKind g && exprType gRhsCore `tcEqType` tgKind g -> do
                    envArgL <- freshLocal "obs_g_env_l" envTy
                    envArgR <- freshLocal "obs_g_env_r" envTy
                    let gLhsFn = Lam envArgL (bindEnvVars (Var envArgL) gLhsCore)
                        gRhsFn = Lam envArgR (bindEnvVars (Var envArgR) gRhsCore)
                    pure
                        $ Just
                        $ mkCoreApps
                            (Var (ceEqGuardId cenv))
                            [Type envTy, Type (tgKind g), tmoIntExpr, depthIntExpr, doApprox gOps, gLhsFn, gRhsFn]
            _ -> pure Nothing

    pure $ do
        givenExprs <- sequence mbGivenExprs
        let allChecks = domPredExprs ++ givenExprs
            combine a b = mkCoreApps (Var (ceAndGuardId cenv)) [Type envTy, a, b]
        pure $ case allChecks of
            [] -> alwaysExpr
            c : cs -> foldl combine c cs

isUnaryTypeConKind :: Kind -> Bool
isUnaryTypeConKind k =
    case splitFunTy_maybe (coreFullView k) of
        Just (_, _, _, dom, res) -> tcIsLiftedTypeKind dom && tcIsLiftedTypeKind res
        Nothing -> False

detectPolyClassConstraint ::
    InstEnvs ->
    Type ->
    VarSet ->
    [Type] ->
    TcM (Maybe String, Bool)
detectPolyClassConstraint instEnvs orderingCarrier polySet tys
    | isEmptyVarSet polySet = pure (Nothing, False)
    | otherwise = do
        found <- fmap concat (traverse walk tys)
        pure $ case found of
            [] -> (Nothing, False)
            (predStr, _) : _ -> (Just predStr, any snd found)
  where
    walk ty =
        case coreFullView ty of
            ClassAppTy sel instTy dictTy argTy resK -> do
                sub <- fmap concat (traverse walk [instTy, dictTy, argTy, resK])
                let here =
                        case isClassOpId_maybe sel of
                            Just cls
                                | not (isEmptyVarSet (tyCoVarsOfType instTy `intersectVarSet` polySet))
                                    || isLocalDictTerm dictTy ->
                                    let predTy = mkClassPred cls [instTy]
                                        noOrd = isLeftEither (lookupUniqueInstEnv instEnvs cls [orderingCarrier])
                                        hasInt = not (isLeftEither (lookupUniqueInstEnv instEnvs cls [intTy]))
                                     in [(showSDocUnsafe (ppr predTy), noOrd && hasInt)]
                            _ -> []
                pure (here ++ sub)
            TyConApp tc args -> do
                sub <- fmap concat (traverse walk args)
                if isJust (isPromotedDataCon_maybe tc)
                    then pure sub
                    else do
                        mbFun <- recoverFamilyOwnerId tc
                        let here = case mbFun of
                                Nothing -> []
                                Just fun -> inspectFunClassPreds instEnvs orderingCarrier polySet (idType fun) args
                        pure (here ++ sub)
            AppTy f a -> (++) <$> walk f <*> walk a
            TermAppTy f a -> (++) <$> walk (varType f) <*> walk a
            FunTy _ ma mult a r -> fmap concat (traverse walk [ma, mult, a, r])
            CastTy t _ -> walk t
            _ -> pure []

    isLocalDictTerm (TermVarTy v) = isLocalVar v
    isLocalDictTerm _ = False

    isLeftEither (Left _) = True
    isLeftEither (Right _) = False

inspectFunClassPreds :: InstEnvs -> Type -> VarSet -> Type -> [Type] -> [(String, Bool)]
inspectFunClassPreds instEnvs orderingCarrier polySet funTy tyArgs =
    let (_, bndrs, _) = splitPiTys funTy
        namedTvs = [tv | Named (Bndr tv _) <- bndrs, isTyVar tv]
        inScope = mkInScopeSet (mkVarSet namedTvs `unionVarSet` polySet)
        subst =
            TySubst.extendTvSubstList
                (TySubst.mkEmptySubst inScope)
                (zip namedTvs tyArgs)
        preds =
            [ TySubst.substTy subst (scaledThing sc)
            | Anon sc af <- bndrs
            , not (isVisibleFunArg af)
            ]
     in [ (showSDocUnsafe (ppr predTy), needsInt predTy)
        | predTy <- preds
        , not (isEmptyVarSet (tyCoVarsOfType predTy `intersectVarSet` polySet))
        ]
  where
    needsInt predTy =
        case getClassPredTys_maybe predTy of
            Just (cls, [_]) ->
                case (lookupUniqueInstEnv instEnvs cls [orderingCarrier], lookupUniqueInstEnv instEnvs cls [intTy]) of
                    (Left _, Right _) -> True
                    _ -> False
            _ -> False

substTermAndTyVars :: TySubst.Subst -> Type -> Type
substTermAndTyVars subst = go
  where
    go ty =
        case coreFullView ty of
            TermVarTy v ->
                let v' = setVarType v (go (varType v))
                 in TermVarTy v'
            TermAppTy f arg ->
                let f' = setVarType f (go (varType f))
                 in TermAppTy f' (go arg)
            TyVarTy tv -> TySubst.substTy subst (mkTyVarTy tv)
            TyConApp tc args -> mkTyConApp tc (map go args)
            AppTy f a -> mkAppTy (go f) (go a)
            FunTy af ma mult a r -> FunTy af (go ma) (go mult) (go a) (go r)
            CastTy t _ -> go t
            ClassAppTy sel i d x k ->
                ClassAppTy sel (go i) (go d) (go x) (go k)
            other -> TySubst.substTy subst other

freshLocal :: String -> Type -> TcM Id
freshLocal prefix ty = do
    u <- newUnique
    pure (mkSysLocal (fsLit prefix) u ManyTy ty)

buildObsConfigCore :: CachedObsEnv -> ObsConfig -> TcM CoreExpr
buildObsConfigCore cenv cfg = do
    dflags <- getDynFlags
    let plat = targetPlatform dflags
        natLit n = mkNaturalExpr plat (toInteger n)
    pure $
        mkCoreApps
            (Var (dataConWrapId (ceObsConfigDc cenv)))
            [ natLit (obsTests cfg)
            , natLit (obsMaxSize cfg)
            , natLit (obsApproxDepth cfg)
            , natLit (obsPartialPct cfg)
            , natLit (obsTimeoutUs cfg)
            , natLit (obsSeed cfg)
            ]

foldEnvComponents ::
    CachedObsEnv ->
    [(Type, CoreExpr, CoreExpr, CoreExpr, Id)] ->
    TcM (Type, CoreExpr, CoreExpr, CoreExpr, CoreExpr -> CoreExpr -> CoreExpr)
foldEnvComponents cenv [] = do
    pctVar <- freshLocal "obs_pct0" intTy
    uVar1 <- freshLocal "obs_u1" unitTy
    uVar2 <- freshLocal "obs_u2" unitTy
    let genUnit = Lam pctVar (mkCoreApps (Var (cePureGenId cenv)) [Type unitTy, Var unitDataConId])
        -- unit has no smaller shrinks
        shrinkUnit = Lam uVar1 (mkListExpr unitTy [])
        showUnit = Lam uVar2 (mkListExpr charTy [])
    pure (unitTy, genUnit, shrinkUnit, showUnit, \_ body -> body)
foldEnvComponents _ [(ty, genE, shrinkE, showE, pid)] =
    pure (ty, genE, shrinkE, showE, \scrut body -> Let (NonRec pid scrut) body)
foldEnvComponents cenv ((ty1, gen1, shrink1, show1, pid1) : rest) = do
    (tyRest, genRest, shrinkRest, showRest, unpackRest) <- foldEnvComponents cenv rest
    let pairTy = mkTupleTy Boxed [ty1, tyRest]
        pairDc = tupleDataCon Boxed 2
        genPair = mkCoreApps (Var (cePairGenId cenv)) [Type ty1, Type tyRest, gen1, genRest]
        shrinkPair = mkCoreApps (Var (cePairShrinkId cenv)) [Type ty1, Type tyRest, shrink1, shrinkRest]
        showPair = mkCoreApps (Var (cePairShowId cenv)) [Type ty1, Type tyRest, show1, showRest]
    caseBndr <- freshLocal "obs_pair_bndr" pairTy
    restBndr <- freshLocal "obs_pair_rest" tyRest
    let unpackPair scrut body =
            Case
                scrut
                caseBndr
                (exprType body)
                [ Alt
                    (DataAlt pairDc)
                    [pid1, restBndr]
                    (unpackRest (Var restBndr) body)
                ]
    pure (pairTy, genPair, shrinkPair, showPair, unpackPair)

-- ---------------------------------------------------------------------------
-- Resolving and Synthesizing ObsGen Dictionaries (with Field Shrinking)
-- ---------------------------------------------------------------------------

type AdtCache = TypeMap DomainOps

resolveDomainOps ::
    CachedObsEnv ->
    IORef AdtCache ->
    InstEnvs ->
    Type ->
    TcM (Maybe DomainOps)
resolveDomainOps cenv cacheRef instEnvs domTy = do
    cached <- liftIO (readIORef cacheRef)
    case lookupTypeMap cached domTy of
        Just ops -> pure (Just ops)
        Nothing -> do
            famEnvs <- tcGetFamInstEnvs
            let predTy = mkClassPred (ceObsGenCls cenv) [domTy]
            case resolveClassDictNorm cenv cached famEnvs instEnvs predTy of
                Just dictExpr -> do
                    let ops = mkOpsFromObsGenDict cenv domTy dictExpr
                    liftIO (writeIORef cacheRef (extendTypeMap cached domTy ops))
                    pure (Just ops)
                Nothing -> synthesizeAdtDomainOps cenv cacheRef instEnvs domTy

mkOpsFromObsGenDict :: CachedObsEnv -> Type -> CoreExpr -> DomainOps
mkOpsFromObsGenDict cenv domTy dictExpr =
    DomainOps
        { doType = domTy
        , doDict = dictExpr
        , doGenTotal = mkCoreApps (Var (ceObsGenId cenv)) [Type domTy, dictExpr]
        , doGenPartial = mkCoreApps (Var (ceObsGenPartialId cenv)) [Type domTy, dictExpr]
        , doShrink = mkCoreApps (Var (ceObsShrinkId cenv)) [Type domTy, dictExpr]
        , doApprox = mkCoreApps (Var (ceObsApproxId cenv)) [Type domTy, dictExpr]
        , doShow = mkCoreApps (Var (ceObsShowId cenv)) [Type domTy, dictExpr]
        }

resolveClassDict :: CachedObsEnv -> AdtCache -> InstEnvs -> PredType -> Maybe CoreExpr
resolveClassDict cenv adtCache instEnvs predTy = do
    (cls, clsArgs) <- getClassPredTys_maybe predTy
    case lookupUniqueInstEnv instEnvs cls clsArgs of
        Right (clsInst, instTys) -> do
            let dfun = instanceDFunId clsInst
                (maTvs, rho) = splitForAllTyCoVars (idType dfun)
                tvs = map snd maTvs
                (_, scaledTheta, _) = splitFunTys rho
                subst = TySubst.extendTvSubstList (TySubst.mkEmptySubst (mkInScopeSet (mkVarSet tvs))) (zip tvs instTys)
                subPreds = [TySubst.substTy subst (scaledThing sc) | sc <- scaledTheta]
            subDicts <- traverse (resolveClassDict cenv adtCache instEnvs) subPreds
            pure (mkCoreApps (Var dfun) (map Type instTys ++ subDicts))
        Left _
            | cls == ceObsGenCls cenv
            , [argTy] <- clsArgs ->
                doDict <$> lookupTypeMap adtCache argTy
            | otherwise -> Nothing

resolveClassDictNorm ::
    CachedObsEnv ->
    AdtCache ->
    FamInstEnvs ->
    InstEnvs ->
    PredType ->
    Maybe CoreExpr
resolveClassDictNorm cenv adtCache famEnvs instEnvs predTy = do
    (cls, clsArgs) <- getClassPredTys_maybe predTy
    let redns = map (normaliseType famEnvs Nominal) clsArgs
        normArgs = map reductionReducedType redns
        symCos = map (mkSymCo . reductionCoercion) redns
        castBack e
            | all (isReflexiveCo . reductionCoercion) redns = e
            | otherwise = mkCast e (mkSubCo (mkTyConAppCo Nominal (classTyCon cls) symCos))
    case lookupUniqueInstEnv instEnvs cls normArgs of
        Right (clsInst, instTys) -> do
            let dfun = instanceDFunId clsInst
                (maTvs, rho) = splitForAllTyCoVars (idType dfun)
                tvs = map snd maTvs
                (_, scaledTheta, _) = splitFunTys rho
                subst = TySubst.extendTvSubstList (TySubst.mkEmptySubst (mkInScopeSet (mkVarSet tvs))) (zip tvs instTys)
                subPreds = [TySubst.substTy subst (scaledThing sc) | sc <- scaledTheta]
            subDicts <- traverse (resolveClassDictNorm cenv adtCache famEnvs instEnvs) subPreds
            pure (castBack (mkCoreApps (Var dfun) (map Type instTys ++ subDicts)))
        Left _
            | cls == ceObsGenCls cenv
            , [argTy] <- normArgs ->
                castBack . doDict <$> lookupTypeMap adtCache argTy
            | otherwise -> Nothing

synthesizeAdtDomainOps ::
    CachedObsEnv ->
    IORef AdtCache ->
    InstEnvs ->
    Type ->
    TcM (Maybe DomainOps)
synthesizeAdtDomainOps cenv cacheRef instEnvs domTy
    | Just (tc, tcArgs) <- splitTyConApp_maybe (coreFullView domTy)
    , isVanillaAlgTyCon tc
    , isBoxedDataTyCon tc
    , let dcs = tyConDataCons tc
    , not (null dcs)
    , all isVanillaDataCon dcs = do
        let adtBundleTy = mkTyConApp (idResultTyCon (ceMkAdtDictId cenv)) [domTy]
        recBundleId <- freshLocal ("adt_bundle_" ++ getOccString (tyConName tc)) adtBundleTy
        let placeholderOps = mkPlaceholderOps cenv domTy (Var recBundleId)
        prevCache <- liftIO (readIORef cacheRef)
        liftIO (writeIORef cacheRef (extendTypeMap prevCache domTy placeholderOps))

        let fieldTypesFor dc = map scaledThing (dataConInstArgTys dc tcArgs)
            allFields = concatMap fieldTypesFor dcs
        if not (all (tcIsLiftedTypeKind . typeKind) allFields)
            then do
                liftIO (writeIORef cacheRef prevCache)
                pure Nothing
            else do
                mbFieldOps <- traverse (resolveDomainOps cenv cacheRef instEnvs) allFields
                case sequence mbFieldOps of
                    Nothing -> do
                        liftIO (writeIORef cacheRef prevCache)
                        pure Nothing
                    Just _ -> do
                        curCache <- liftIO (readIORef cacheRef)
                        let lookupOps fTy = lookupTypeMap curCache fTy
                        mbRhs <- buildMkAdtDictCall cenv domTy dcs tcArgs lookupOps
                        case mbRhs of
                            Nothing -> do
                                liftIO (writeIORef cacheRef prevCache)
                                pure Nothing
                            Just bundleRhs -> do
                                let letBundle body = Let (Rec [(recBundleId, bundleRhs)]) body
                                    finalPlaceholder = mkPlaceholderOps cenv domTy (letBundle (Var recBundleId))
                                liftIO $ do
                                    cur2 <- readIORef cacheRef
                                    writeIORef cacheRef (extendTypeMap cur2 domTy finalPlaceholder)
                                pure (Just finalPlaceholder)
    | otherwise = pure Nothing
  where
    idResultTyCon fnId =
        let (_, rho) = splitForAllTyCoVars (idType fnId)
            (_, _, res) = splitFunTys rho
         in case splitTyConApp_maybe res of
                Just (tc, _) -> tc
                Nothing -> error "Dependent.Plugin.ObsEq: expected AdtObsDict TyCon"

mkPlaceholderOps :: CachedObsEnv -> Type -> CoreExpr -> DomainOps
mkPlaceholderOps cenv domTy bundleExpr =
    let genTotalE = mkCoreApps (Var (ceAdtGenId cenv)) [Type domTy, bundleExpr]
        genPartE = mkCoreApps (Var (ceAdtGenPartialId cenv)) [Type domTy, bundleExpr]
        shrinkE = mkCoreApps (Var (ceAdtShrinkId cenv)) [Type domTy, bundleExpr]
        approxE = mkCoreApps (Var (ceAdtApproxId cenv)) [Type domTy, bundleExpr]
        showE = mkCoreApps (Var (ceAdtShowId cenv)) [Type domTy, bundleExpr]
        obsGenDc = tyConSingleDataCon (classTyCon (ceObsGenCls cenv))
        obsDictE =
            mkCoreApps
                (Var (dataConWrapId obsGenDc))
                [Type domTy, genTotalE, genPartE, shrinkE, approxE, showE]
     in DomainOps
            { doType = domTy
            , doDict = obsDictE
            , doGenTotal = genTotalE
            , doGenPartial = genPartE
            , doShrink = shrinkE
            , doApprox = approxE
            , doShow = showE
            }

buildMkAdtDictCall ::
    CachedObsEnv ->
    Type ->
    [DataCon] ->
    [Type] ->
    (Type -> Maybe DomainOps) ->
    TcM (Maybe CoreExpr)
buildMkAdtDictCall cenv domTy dcs tcArgs lookupOps = do
    let genDomTy = mkTyConApp (ceGenTc cenv) [domTy]
        nullaryDcs = [dc | dc <- dcs, dataConSourceArity dc == 0]
        nonNullaryDcs = [dc | dc <- dcs, dataConSourceArity dc > 0]
        baseGenExprs =
            [ mkCoreApps (Var (cePureGenId cenv)) [Type domTy, mkCoreApps (Var (dataConWorkId dc)) (map Type tcArgs)]
            | dc <- nullaryDcs
            ]

    mbTotalCons <- traverse buildTotalCon nonNullaryDcs
    mbPartCons <- traverse buildPartialCon nonNullaryDcs
    mbShrinkFn <- buildShrinkFn nullaryDcs
    mbApproxFn <- buildApproxFn
    mbShowFn <- buildShowFn

    pure $ do
        totalCons <- sequence mbTotalCons
        partCons <- sequence mbPartCons
        shrinkFn <- mbShrinkFn
        approxFn <- mbApproxFn
        showFn <- mbShowFn
        pure $
            mkCoreApps
                (Var (ceMkAdtDictId cenv))
                [ Type domTy
                , mkListExpr genDomTy baseGenExprs
                , mkListExpr (mkVisFunTyManyU intTy genDomTy) totalCons
                , mkListExpr (mkVisFunTyManyU intTy (mkVisFunTyManyU intTy genDomTy)) partCons
                , shrinkFn
                , approxFn
                , showFn
                ]
  where
    fieldTypes dc = map scaledThing (dataConInstArgTys dc tcArgs)

    mkEtaConExpr dc fTys = do
        argIds <- zipWithM (\i ft -> freshLocal ("con_arg" ++ show i) ft) [1 :: Int ..] fTys
        let satApp = mkCoreApps (Var (dataConWorkId dc)) (map Type tcArgs ++ map Var argIds)
        pure (mkLams argIds satApp)

    buildTotalCon dc = do
        szId <- freshLocal "adt_sz" intTy
        let fTys = fieldTypes dc
            apId = if length fTys >= 2 then ceApHalfGenId cenv else ceApGenId cenv
        case traverse lookupOps fTys of
            Nothing -> pure Nothing
            Just fOps -> do
                conHead <- mkEtaConExpr dc fTys
                let pureHead = mkCoreApps (Var (cePureGenId cenv)) [Type (exprType conHead), conHead]
                    step acc ops =
                        let curArrow = exprType acc
                            resTy = case splitFunTy_maybe (extractGenElem curArrow) of
                                Just (_, _, _, _, r) -> r
                                Nothing -> error "Dependent.Plugin.ObsEq: expected FunTy in constructor"
                         in mkCoreApps (Var apId) [Type (doType ops), Type resTy, acc, doGenTotal ops]
                    body = foldl step pureHead fOps
                pure (Just (Lam szId body))

    buildPartialCon dc = do
        pctId <- freshLocal "adt_pct" intTy
        szId <- freshLocal "adt_szp" intTy
        let fTys = fieldTypes dc
            apId = if length fTys >= 2 then ceApHalfGenId cenv else ceApGenId cenv
        case traverse lookupOps fTys of
            Nothing -> pure Nothing
            Just fOps -> do
                conHead <- mkEtaConExpr dc fTys
                let pureHead = mkCoreApps (Var (cePureGenId cenv)) [Type (exprType conHead), conHead]
                    step acc ops =
                        let curArrow = exprType acc
                            resTy = case splitFunTy_maybe (extractGenElem curArrow) of
                                Just (_, _, _, _, r) -> r
                                Nothing -> error "Dependent.Plugin.ObsEq: expected FunTy in partial constructor"
                            partField = App (doGenPartial ops) (Var pctId)
                         in mkCoreApps (Var apId) [Type (doType ops), Type resTy, acc, partField]
                    body = foldl step pureHead fOps
                pure (Just (Lam pctId (Lam szId body)))

    extractGenElem ty =
        case splitTyConApp_maybe ty of
            Just (_, [elemTy]) -> elemTy
            _ -> error "Dependent.Plugin.ObsEq: expected Gen type"

    buildShrinkFn nullaryDcs = do
        scrutId <- freshLocal "adt_sh_x" domTy
        caseBndr <- freshLocal "adt_sh_bndr" domTy
        let listDomTy = mkListTy domTy
            baseShrinks = [mkCoreApps (Var (dataConWorkId dc)) (map Type tcArgs) | dc <- take 1 nullaryDcs]
            catLists a b = mkCoreApps (Var (ceAppendListId cenv)) [Type domTy, a, b]
        mbAlts <- forM dcs $ \dc -> do
            let fTys = fieldTypes dc
            fIds <- zipWithM (\i ft -> freshLocal ("sh_f" ++ show i) ft) [1 :: Int ..] fTys
            case traverse lookupOps fTys of
                Nothing -> pure Nothing
                Just fOps -> do
                    let directRec = [Var fid | (fid, ft) <- zip fIds fTys, ft `tcEqType` domTy]
                        initials = if null fIds then [] else directRec ++ baseShrinks
                    fieldLists <- forM (zip [0 :: Int ..] (zip fIds fOps)) $ \(idx, (fid, ops)) -> do
                        let ft = doType ops
                        candId <- freshLocal ("sh_cand" ++ show idx) ft
                        let argsWithCand =
                                [ if j == idx then Var candId else Var fj
                                | (j, fj) <- zip [0 :: Int ..] fIds
                                ]
                            rebuiltCon = mkCoreApps (Var (dataConWorkId dc)) (map Type tcArgs ++ argsWithCand)
                        pure $
                            mkCoreApps
                                (Var (ceMapListId cenv))
                                [Type ft, Type domTy, Lam candId rebuiltCon, App (doShrink ops) (Var fid)]
                    let rhs = foldl catLists (mkListExpr domTy initials) fieldLists
                    pure (Just (Alt (DataAlt dc) fIds rhs))
        pure $ do
            alts <- sequence mbAlts
            pure (Lam scrutId (Case (Var scrutId) caseBndr listDomTy alts))

    buildApproxFn = do
        depthId <- freshLocal "adt_ap_d" intTy
        scrutId <- freshLocal "adt_ap_x" domTy
        caseBndr <- freshLocal "adt_ap_bndr" domTy
        let treeTy = mkTyConApp (ceObsTreeTc cenv) []
            ioTreeTy =
                exprType
                    ( mkCoreApps
                        (Var (cePureIOId cenv))
                        [ Type treeTy
                        , mkCoreApps
                            (Var (dataConWrapId (ceObsConDc cenv)))
                            [mkCharListExpr "?", mkListExpr treeTy []]
                        ]
                    )
        mbAlts <- forM dcs $ \dc -> do
            let fTys = fieldTypes dc
            fIds <- zipWithM (\i ft -> freshLocal ("ap_f" ++ show i) ft) [1 :: Int ..] fTys
            tIds <- mapM (\i -> freshLocal ("ap_t" ++ show i) treeTy) [1 :: Int .. length fTys]
            case traverse lookupOps fTys of
                Nothing -> pure Nothing
                Just fOps -> do
                    let conLeaf =
                            mkCoreApps
                                (Var (cePureIOId cenv))
                                [ Type treeTy
                                , mkCoreApps
                                    (Var (dataConWrapId (ceObsConDc cenv)))
                                    [mkCharListExpr (getOccString (dataConName dc)), mkListExpr treeTy (map Var tIds)]
                                ]
                        bindField ((fid, ops), tid) restIO =
                            mkCoreApps
                                (Var (ceBindIOId cenv))
                                [ Type treeTy
                                , Type treeTy
                                , mkCoreApps (doApprox ops) [Var depthId, Var fid]
                                , Lam tid restIO
                                ]
                        rhs = foldr bindField conLeaf (zip (zip fIds fOps) tIds)
                    pure (Just (Alt (DataAlt dc) fIds rhs))
        pure $ do
            alts <- sequence mbAlts
            pure (Lam depthId (Lam scrutId (Case (Var scrutId) caseBndr ioTreeTy alts)))

    buildShowFn = do
        scrutId <- freshLocal "adt_sw_x" domTy
        caseBndr <- freshLocal "adt_sw_bndr" domTy
        let ioStrTy = exprType (mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, mkCharListExpr ""])
        mbAlts <- forM dcs $ \dc -> do
            let fTys = fieldTypes dc
                conStr = getOccString (dataConName dc)
            fIds <- zipWithM (\i ft -> freshLocal ("sw_f" ++ show i) ft) [1 :: Int ..] fTys
            case traverse lookupOps fTys of
                Nothing -> pure Nothing
                Just fOps -> do
                    let catStr a b = mkCoreApps (Var (ceAppendStrId cenv)) [a, b]
                        strExpr
                            | null fIds = mkCharListExpr conStr
                            | otherwise =
                                let parts = [catStr (mkCharListExpr " ") (App (doShow ops) (Var fid)) | (fid, ops) <- zip fIds fOps]
                                 in foldl catStr (mkCharListExpr ("(" ++ conStr)) parts `catStr` mkCharListExpr ")"
                        rhs = mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, strExpr]
                    pure (Just (Alt (DataAlt dc) fIds rhs))
        pure $ do
            alts <- sequence mbAlts
            pure (Lam scrutId (Case (Var scrutId) caseBndr ioStrTy alts))

mkCharListExpr :: String -> CoreExpr
mkCharListExpr s = mkListExpr charTy (map mkCharExpr s)

-- ---------------------------------------------------------------------------
-- Reifying Promoted / Uninterpreted Types to Core Expressions
-- ---------------------------------------------------------------------------

reifyTypeToCore :: CachedObsEnv -> UniqFM Var Id -> Type -> TcM (Maybe CoreExpr)
reifyTypeToCore cenv varEnv = go
  where
    go ty0 = do
        let ty = coreFullView ty0
        case ty of
            TermVarTy v ->
                case lookupUFM varEnv v of
                    Just pid -> pure (Just (Var pid))
                    Nothing
                        | isGlobalId v -> pure (Just (Var v))
                        | otherwise -> pure Nothing
            TyVarTy tv ->
                pure (Var <$> lookupUFM varEnv tv)
            LitTy (NumTyLit n)
                | typeKind ty `tcEqType` naturalTy -> do
                    dflags <- getDynFlags
                    pure (Just (mkNaturalExpr (targetPlatform dflags) n))
                | typeKind ty `tcEqType` intTy -> do
                    dflags <- getDynFlags
                    pure (Just (mkIntExpr (targetPlatform dflags) n))
                | otherwise -> pure Nothing
            LitTy (CharTyLit c) ->
                pure (Just (mkCharExpr c))
            LitTy (StrTyLit fs) ->
                pure (Just (mkCharListExpr (unpackFS fs)))
            TermAppTy f arg -> do
                mf <- go (TermVarTy f)
                ma <- go arg
                pure (App <$> mf <*> ma)
            ClassAppTy sel instTy _ argTy _ -> do
                case isClassOpId_maybe sel of
                    Nothing -> pure Nothing
                    Just cls -> do
                        instEnvs <- tcGetInstEnvs
                        case resolveClassDict cenv emptyTypeMap instEnvs (mkClassPred cls [instTy]) of
                            Nothing -> pure Nothing
                            Just dictExpr -> do
                                mbArg <- go argTy
                                pure ((\argExpr -> mkCoreApps (Var sel) [Type instTy, dictExpr, argExpr]) <$> mbArg)
            TyConApp tc args
                | Just dc <- isPromotedDataCon_maybe tc
                , isVanillaDataCon dc -> do
                    let valTys = filterOutInvisibleTypes tc args
                        nVal = dataConSourceArity dc
                    if length valTys > nVal
                        then pure Nothing
                        else do
                            let (_, remArrows, finalResTy) = splitFunTys (typeKind ty)
                                remDoms = map scaledThing remArrows
                                univTys = case splitTyConApp_maybe (coreFullView finalResTy) of
                                    Just (_, ts) -> ts
                                    Nothing -> []
                            mbVals <- traverse go valTys
                            case sequence mbVals of
                                Nothing -> pure Nothing
                                Just valExprs -> do
                                    etaIds <- zipWithM (\i dom -> freshLocal ("dc_eta" ++ show i) dom) [1 :: Int ..] remDoms
                                    let satCon = mkCoreApps (Var (dataConWrapId dc)) (map Type univTys ++ valExprs ++ map Var etaIds)
                                    pure (Just (mkLams etaIds satCon))
                | otherwise -> do
                    mbFun <- recoverFamilyOwnerId tc
                    case mbFun of
                        Just fun -> instantiateAndApply cenv fun args (typeKind ty) go
                        Nothing -> reifySingleBranchLambdaFamily cenv varEnv tc args (typeKind ty)
            AppTy f a -> do
                mf <- go f
                ma <- go a
                pure (App <$> mf <*> ma)
            CastTy inner _ -> go inner
            _ -> pure Nothing

recoverFamilyOwnerId :: TyCon -> TcM (Maybe Id)
recoverFamilyOwnerId tc =
    let tcNm = tyConName tc
        occStr = occNameString (nameOccName tcNm)
     in if "U:@" `isPrefixOf` occStr
            then case splitUnitModOcc (drop 3 occStr) of
                Just (unitStr, modStr, varStr) -> do
                    let defMod = mkModule (stringToUnit unitStr) (mkModuleName modStr)
                    nm <- lookupOrig defMod (mkVarOcc varStr)
                    lookupTermId nm
                Nothing -> pure Nothing
            else
                if "U:" `isPrefixOf` occStr
                    then do
                        let varStr = drop 2 occStr
                        nm <- lookupOrig (nameModule tcNm) (mkVarOcc varStr)
                        lookupTermId nm
                    else
                        if "T:field:" `isPrefixOf` occStr
                            then pure Nothing
                            else
                                if "T:" `isPrefixOf` occStr
                                    then do
                                        let varStr = drop 2 occStr
                                        nm <- lookupOrig (nameModule tcNm) (mkVarOcc varStr)
                                        lookupTermId nm
                                    else pure Nothing
  where
    splitUnitModOcc s = do
        let (u, r1) = break (== ':') s
        guard (not (null r1))
        let (m, r2) = break (== ':') (drop 1 r1)
        guard (not (null r2))
        pure (u, m, drop 1 r2)

lookupTermId :: Name -> TcM (Maybe Id)
lookupTermId nm = do
    gbl <- getGblEnv
    if nameIsLocalOrFrom (tcg_semantic_mod gbl) nm
        then case lookupNameEnv (tcg_local_open_defs gbl) nm of
            Just (fun, _) -> pure (Just fun)
            Nothing -> tcLookupIdMaybe nm
        else tcLookupIdMaybe nm

reifySingleBranchLambdaFamily ::
    CachedObsEnv ->
    UniqFM Var Id ->
    TyCon ->
    [Type] ->
    Kind ->
    TcM (Maybe CoreExpr)
reifySingleBranchLambdaFamily cenv varEnv tc args expectedKind =
    case famTyConFlav_maybe tc of
        Just (ClosedTypeFamilyTyCon ctf)
            | Just ax <- closedTyFamCoAxiom_maybe ctf
            , [br] <- fromBranches (coAxiomBranches ax) -> do
                let lhsPats = coAxBranchLHS br
                    rhsTy0 = coAxBranchRHS br
                    (_, remArrows, _) = splitFunTys expectedKind
                    remDoms = map scaledThing remArrows
                if length args + length remDoms /= length lhsPats
                    then pure Nothing
                    else do
                        let (prefixPats, suffixPats) = splitAt (length args) lhsPats
                            mbPrefixTvs = traverse getTyVar_maybe prefixPats
                            mbSuffixTvs = traverse getTyVar_maybe suffixPats
                        case (mbPrefixTvs, mbSuffixTvs) of
                            (Just prefixTvs, Just suffixTvs) -> do
                                let inScope = mkInScopeSet (mkVarSet (coAxBranchTyVars br))
                                    subst = TySubst.extendTvSubstList (TySubst.mkEmptySubst inScope) (zip prefixTvs args)
                                    rhsTy = TySubst.substTy subst rhsTy0
                                lamIds <- zipWithM (\i dom -> freshLocal ("fam_lam" ++ show i) dom) [1 :: Int ..] remDoms
                                let varEnv' = addListToUFM varEnv (zip suffixTvs lamIds)
                                mbBody <- reifyTypeToCore cenv varEnv' rhsTy
                                pure (mkLams lamIds <$> mbBody)
                            _ -> pure Nothing
        _ -> pure Nothing

instantiateAndApply ::
    CachedObsEnv ->
    Id ->
    [Type] ->
    Kind ->
    (Type -> TcM (Maybe CoreExpr)) ->
    TcM (Maybe CoreExpr)
instantiateAndApply cenv fun allArgs expectedRes reifyArg = do
    let (invisBndrs, rho0) = splitInvisBinders (idType fun)
        (_, scaledArrows, _) = splitFunTys rho0
        nVal = length scaledArrows
        nInvisTvs = length [() | Named (Bndr tv _) <- invisBndrs, isTyVar tv]
        valArgTys
            | length allArgs >= nInvisTvs && length allArgs - nInvisTvs <= nVal =
                drop nInvisTvs allArgs
            | length allArgs >= nVal =
                drop (length allArgs - nVal) allArgs
            | otherwise = []
        canAlign =
            (length allArgs >= nInvisTvs && length allArgs - nInvisTvs <= nVal)
                || length allArgs >= nVal
    if not canAlign
        then pure Nothing
        else do
            mbValExprs <- traverse reifyArg valArgTys
            case sequence mbValExprs of
                Nothing -> pure Nothing
                Just valExprs -> do
                    let actualDomains = map exprType valExprs
                    instEnvs <- tcGetInstEnvs
                    pure (buildSpecialisedCall cenv instEnvs fun invisBndrs (map scaledThing scaledArrows) rho0 actualDomains expectedRes valExprs)
  where
    splitInvisBinders ty =
        let (mas, bndrs, body) = splitPiTys ty
            (invis, rest) = span (isInvisiblePiTyBinder . snd) (zip mas bndrs)
         in (map snd invis, mkPiTys rest body)

buildSpecialisedCall ::
    CachedObsEnv ->
    InstEnvs ->
    Id ->
    [PiTyBinder] ->
    [Type] ->
    Type ->
    [Type] ->
    Type ->
    [CoreExpr] ->
    Maybe CoreExpr
buildSpecialisedCall cenv instEnvs fun invisBndrs declDomains rho0 actualDomains expectedRes valExprs = do
    let (_, _, declRes) = splitFunTys rho0
        namedTvs = [tv | Named (Bndr tv _) <- invisBndrs]
        initSubst =
            foldl
                ( \s tv ->
                    let ki = TySubst.substTy s (tyVarKind tv)
                     in if ki `tcEqType` runtimeRepTy
                            then TySubst.extendTvSubstAndInScope s tv liftedRepTy
                            else
                                if ki `tcEqType` levityTy
                                    then TySubst.extendTvSubstAndInScope s tv liftedDataConTy
                                    else
                                        let tv' = setVarType tv ki
                                         in TySubst.extendTvSubstAndInScope s tv (mkTyVarTy tv')
                )
                (TySubst.mkEmptySubst (mkInScopeSet (mkVarSet namedTvs)))
                namedTvs
        substDomains = map (TySubst.substTy initSubst) declDomains
        substRes = TySubst.substTy initSubst declRes
        nGiven = length valExprs
        (givenDeclDoms, remDeclDoms) = splitAt nGiven substDomains
        (_, expRemArrows, expFinalRes) = splitFunTys expectedRes
        expRemDoms = map scaledThing expRemArrows
    guard (length remDeclDoms == length expRemDoms)
    matchedSubst <-
        tcMatchTys
            (givenDeclDoms ++ remDeclDoms ++ [substRes])
            (actualDomains ++ expRemDoms ++ [expFinalRes])
    let lookupTv tv = do
            step1 <- TySubst.lookupTyVar initSubst tv
            let step2 = TySubst.substTy matchedSubst step1
            guard (noFreeVarsOfType step2)
            pure step2
    instArgs <- forM invisBndrs $ \case
        Named (Bndr tv _) -> Type <$> lookupTv tv
        Anon predScaled _ -> do
            let predTy = TySubst.substTy matchedSubst (TySubst.substTy initSubst (scaledThing predScaled))
            resolveClassDict cenv emptyTypeMap instEnvs predTy
    pure (mkCoreApps (Var fun) (instArgs ++ valExprs))

-- ---------------------------------------------------------------------------
-- Executing Batched Core IO Strings in hscInterp (with Cached LetRec & ITbls)
-- ---------------------------------------------------------------------------

chainSepIO :: CachedObsEnv -> String -> [CoreExpr] -> TcM CoreExpr
chainSepIO cenv _ [] =
    pure (mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, mkCharListExpr ""])
chainSepIO _ _ [single] = pure single
chainSepIO cenv delimStr (e : rest) = do
    restIO <- chainSepIO cenv delimStr rest
    vHead <- freshLocal "obs_batch_hd" stringTy
    vTail <- freshLocal "obs_batch_tl" stringTy
    let catExpr a b = mkCoreApps (Var (ceAppendStrId cenv)) [a, b]
        joined = Var vHead `catExpr` mkCharListExpr delimStr `catExpr` Var vTail
        pureJoined = mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, joined]
        bindTail = mkCoreApps (Var (ceBindIOId cenv)) [Type stringTy, Type stringTy, restIO, Lam vTail pureJoined]
    pure (mkCoreApps (Var (ceBindIOId cenv)) [Type stringTy, Type stringTy, e, Lam vHead bindTail])

splitOnChar :: Char -> String -> [String]
splitOnChar delim s =
    case break (== delim) s of
        (chunk, []) -> [chunk]
        (chunk, _ : rest) -> chunk : splitOnChar delim rest

runCoreIOStringBatch ::
    PluginState ->
    CachedObsEnv ->
    EvBindsVar ->
    SrcSpan ->
    Bool ->
    [CoreExpr] ->
    TcM (Maybe [String])
runCoreIOStringBatch _ _ _ _ _ [] = pure (Just [])
runCoreIOStringBatch st cenv evBindsVar locSpan recordSideEffects ioExprs = do
    hscEnv0 <- getTopEnv
    case hsc_interp hscEnv0 of
        Nothing -> pure Nothing
        Just _ -> do
            let hscEnv = hscEnv0{hsc_dflags = gopt_unset (hsc_dflags hscEnv0) Opt_OmitYields}
                interp = hscInterp hscEnv
            ioStrExpr <- chainSepIO cenv "\x1e" ioExprs
            gblEnv <- getGblEnv
            instEnvs <- tcGetInstEnvs
            locals0 <- collectLocalDefinitions st evBindsVar gblEnv ioStrExpr
            expr0 <- resolveFreeLocalDicts cenv locals0 ioStrExpr
            locals1 <- resolveLocalEnvDicts cenv locals0 expr0
            locals <- repairUnfinishedObsGenLocals cenv instEnvs locals1
            let (localNames, fullExpr) = inlineLocalLetRec locals expr0
            if not (null (exprSomeFreeVarsList isLocalVar fullExpr))
                then fallbackIndividual
                else do
                    let localAlgTcs =
                            [ tc
                            | tc <- tcg_tcs gblEnv
                            , isBoxedDataTyCon tc && not (isTypeDataTyCon tc)
                            ]
                    when (recordSideEffects && not (null localNames)) $
                        updTcRef (tcg_source_check gblEnv) $ \s ->
                            s{scs_evaluated_uses = extendNameSetList (scs_evaluated_uses s) localNames}
                    itblTag <- newUnique
                    compiled <- tryAllM $ liftIO $ do
                        (itblLinks, itblPkgs) <-
                            if null localAlgTcs
                                then pure ([], emptyUDFM)
                                else loadLocalDataConItbls interp hscEnv locSpan itblTag localAlgTcs
                        (hval, links, pkgs) <- hscCompileCoreExpr hscEnv locSpan fullExpr
                        pure (hval, itblLinks ++ links, plusUDFM itblPkgs pkgs)
                    case compiled of
                        Left _ -> fallbackIndividual
                        Right (hval, links, pkgs) -> do
                            when recordSideEffects $
                                recordThNeededRuntimeDeps links pkgs
                            outcome <- tryAllM $ liftIO (evalString interp hval)
                            case outcome of
                                Left _ -> fallbackIndividual
                                Right s -> pure (Just (splitOnChar '\x1e' s))
  where
    fallbackIndividual
        | length ioExprs <= 1 = pure Nothing
        | otherwise = do
            mbSingles <- forM ioExprs $ \oneExpr ->
                runCoreIOStringBatch st cenv evBindsVar locSpan recordSideEffects [oneExpr]
            pure (concat <$> sequence mbSingles)

loadLocalDataConItbls ::
    Interp ->
    HscEnv ->
    SrcSpan ->
    Unique ->
    [TyCon] ->
    IO ([LinkableUsage], PkgsLoaded)
loadLocalDataConItbls interp hscEnv locSpan uniq tycons = do
    initLoaderState interp hscEnv
    pls <- getLoaderState interp
    let bcoSt = maybe emptyBytecodeLoaderState bco_loader_state pls
        missingTyCons =
            [ tc
            | tc <- tycons
            , any
                ( \dc ->
                    isNothing (lookupInfoTableBytecodeState bcoSt (dataConName dc))
                        || isNothing (lookupNameBytecodeState bcoSt (idName (dataConWorkId dc)))
                )
                (tyConDataCons tc)
            ]
    if null missingTyCons
        then pure ([], emptyUDFM)
        else do
            let itblMod = mkInteractiveModule ("ObsEqItbls_" ++ show uniq)
                logger = hsc_logger hscEnv
                dflags = hsc_dflags hscEnv
                icInScope = interactiveInScope (hsc_IC hscEnv)
                dummyLoc =
                    OsPathModLocation
                        { ml_hs_file_ospath = Nothing
                        , ml_hi_file_ospath = error "ObsEqItbls:ml_hi_file_ospath"
                        , ml_obj_file_ospath = error "ObsEqItbls:ml_obj_file_ospath"
                        , ml_dyn_obj_file_ospath = error "ObsEqItbls:ml_dyn_obj_file_ospath"
                        , ml_dyn_hi_file_ospath = error "ObsEqItbls:ml_dyn_hi_file_ospath"
                        , ml_hie_file_ospath = error "ObsEqItbls:ml_hie_file_ospath"
                        , ml_bytecode_file_ospath = error "ObsEqItbls:ml_bytecode_file_ospath"
                        }
                cpPgmCfg = initCorePrepPgmConfig dflags icInScope
            cpCfg <- initCorePrepConfig hscEnv
            implicitCore <- addImplicitBinds cpPgmCfg dummyLoc missingTyCons []
            prepdBinds <- corePrepPgm logger cpCfg cpPgmCfg itblMod implicitCore
            (stgBinds0, _, _) <- coreToStg (initCoreToStgOpts dflags) itblMod dummyLoc prepdBinds
            (stgBindsWithFvs, _) <- stg2stg logger icInScope (initStgPipelineOpts dflags True) itblMod stgBinds0
            bcos <- byteCodeGen hscEnv itblMod (map fst stgBindsWithFvs) missingTyCons Nothing [] Strict.Nothing
            bcoTime <- getCurrentTime
            mbc <- ByteCode.mkModuleByteCode itblMod bcos []
            loadDecls interp hscEnv locSpan (Linkable bcoTime itblMod (NE.singleton (DotGBC mbc)))

resolveFreeLocalDicts :: CachedObsEnv -> NameEnv (Id, CoreExpr) -> CoreExpr -> TcM CoreExpr
resolveFreeLocalDicts cenv locals expr = do
    let isFreeLocalDict x =
            isId x
                && isLocalVar x
                && not (isCoVar x)
                && not (isDataConWorkId x || isDataConWrapId x)
                && isNothing (lookupNameEnv locals (idName x))
        freeLocals = exprSomeFreeVarsList isFreeLocalDict expr
    if null freeLocals
        then pure expr
        else do
            famEnvs <- tcGetFamInstEnvs
            instEnvs <- tcGetInstEnvs
            pairs <- fmap catMaybes $ forM freeLocals $ \v -> do
                zTy <- liftZonkM (zonkTcType (idType v))
                pure $ case resolveClassDictNorm cenv emptyTypeMap famEnvs instEnvs zTy of
                    Just dictExpr -> Just (v, dictExpr)
                    Nothing -> Nothing
            if null pairs
                then pure expr
                else do
                    let allFvs =
                            exprSomeFreeVarsList (const True) expr
                                ++ concatMap (exprSomeFreeVarsList (const True) . snd) pairs
                        inScope = mkInScopeSet (mkVarSet (allFvs ++ map fst pairs))
                        subst = CoreSubst.extendIdSubstList (CoreSubst.mkEmptySubst inScope) pairs
                    pure (CoreSubst.substExpr subst expr)

resolveLocalEnvDicts ::
    CachedObsEnv ->
    NameEnv (Id, CoreExpr) ->
    CoreExpr ->
    TcM (NameEnv (Id, CoreExpr))
resolveLocalEnvDicts cenv locals0 rootExpr
    | isEmptyNameEnv locals0 = pure locals0
    | otherwise = step emptyNameSet [idName v | v <- exprSomeFreeVarsList isId rootExpr, isJust (lookupNameEnv locals0 (idName v))] locals0
  where
    step _ [] acc = pure acc
    step seen (nm : rest) acc
        | nm `elemNameSet` seen = step seen rest acc
        | Just (owner, rhs0) <- lookupNameEnv acc nm = do
            rhs1 <- resolveFreeLocalDicts cenv acc rhs0
            let acc' = extendNameEnv acc nm (owner, rhs1)
                deps = [idName v | v <- exprSomeFreeVarsList isId rhs1, isJust (lookupNameEnv acc' (idName v))]
            step (extendNameSet seen nm) (deps ++ rest) acc'
        | otherwise = step seen rest acc

repairUnfinishedObsGenLocals ::
    CachedObsEnv ->
    InstEnvs ->
    NameEnv (Id, CoreExpr) ->
    TcM (NameEnv (Id, CoreExpr))
repairUnfinishedObsGenLocals cenv instEnvs locals0 = do
    let candidateObsGenIds =
            [ (idName owner, owner, domTy)
            | (owner, _) <- nonDetEltsUFM locals0
            , Just (cls, [domTy]) <- [getClassPredTys_maybe (idType owner)]
            , cls == ceObsGenCls cenv
            ]
    foldM repairOne locals0 candidateObsGenIds
  where
    repairOne curLocals (nm, owner, domTy) = do
        let (_, testExpr) = inlineLocalLetRec curLocals (Var owner)
            needsRepair = not (null (exprSomeFreeVarsList isLocalVar testExpr))
        if not needsRepair
            then pure curLocals
            else do
                freshCache <- liftIO (newIORef emptyTypeMap)
                mbSynth <- synthesizeAdtDomainOps cenv freshCache instEnvs domTy
                pure $ case mbSynth of
                    Nothing -> curLocals
                    Just synthOps -> extendNameEnv curLocals nm (owner, doDict synthOps)

{- Note [Binding top-level and derived evidence in interactive BCOs]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When a module defines a datatype with @deriving Generic@ and @instance ObsGen@
alongside 'checkObsEq':

1. Class and @deriving@ instances in @tcg_binds@ use @AbsBinds { abs_exports = [] }@.
   Filtering @tcg_binds@ with @collectHsBindBinders CollNoDictBinders@ drops
   every instance binding (@$fGeneric...@, @$fShow...@, @$fObsGen...@) while
   leaving DFun unfoldings that reference those local @TcId@s, causing Core Lint
   to fail in 'hscCompileCoreExpr'. 'desugarFromTcBinds' therefore desugars all
   of @tcg_binds@ together with both @tcg_ev_binds@ and the active 'EvBindsVar'.
2. User value implications run before @deriving Generic@ implications in
   'simplifyTop', so @$cfrom@ and @$cto@ can still carry unsolved metavariables
   when 'solveObsEq' executes. 'repairUnfinishedObsGenLocals' replaces any local
   'ObsGen' dictionary whose closure still contains unsolved local variables
   with a Core-Lint-clean 'AdtObsDict' synthesized directly from data
   constructors, and 'loadLocalDataConItbls' compiles implicit constructor
   worker/wrapper bindings via 'addImplicitBinds' so nullary and curried
   same-module constructors link in the bytecode interpreter without an object
   file on disk.
3. Recursive instances form cycles across value bindings and evidence bindings,
   while coercion and unlifted bindings cannot appear in @Rec@ groups.
   'inlineLocalLetRec' partitions reachable bindings into strongly connected
   components ('Graph.stronglyConnComp') so acyclic bindings emit 'NonRec' in
   dependency order and mutual cycles emit 'Rec'.
-}

collectLocalDefinitions :: PluginState -> EvBindsVar -> TcGblEnv -> CoreExpr -> TcM (NameEnv (Id, CoreExpr))
collectLocalDefinitions st evBindsVar gblEnv expr = do
    let semMod = tcg_semantic_mod gblEnv
        needsLocal v =
            isId v
                && not (isDataConWorkId v || isDataConWrapId v)
                && (nameIsLocalOrFrom semMod (idName v) || isLocalVar v)
        localRoots = [idName v | v <- exprSomeFreeVarsList needsLocal expr]
    if null localRoots
        then pure emptyNameEnv
        else getCachedModuleDefs st evBindsVar gblEnv

getCachedModuleDefs :: PluginState -> EvBindsVar -> TcGblEnv -> TcM (NameEnv (Id, CoreExpr))
getCachedModuleDefs st evBindsVar gblEnv = do
    evMap <- getTcEvBindsMap evBindsVar
    let semMod = tcg_semantic_mod gblEnv
        baseDefs = tcg_local_open_defs gblEnv
        allEvBinds = tcg_ev_binds gblEnv `unionBags` evBindMapBinds evMap
        bindCount = length (tcg_binds gblEnv)
        evCount = lengthBag allEvBinds
    mbCached <- liftIO (readIORef (psDesugarCache st))
    extraDefs <-
        case mbCached of
            Just (cachedMod, cachedCount, cachedEvCount, cachedEnv)
                | cachedMod == semMod && cachedCount == bindCount && cachedEvCount == evCount ->
                    pure cachedEnv
            _ -> do
                env <- desugarFromTcBinds allEvBinds gblEnv
                liftIO (writeIORef (psDesugarCache st) (Just (semMod, bindCount, evCount, env)))
                pure env
    pure (baseDefs `plusNameEnv` extraDefs)

desugarFromTcBinds :: Bag EvBind -> TcGblEnv -> TcM (NameEnv (Id, CoreExpr))
desugarFromTcBinds allEvBinds gblEnv = do
    let binds = tcg_binds gblEnv
    if null binds && lengthBag allEvBinds == 0
        then pure emptyNameEnv
        else do
            res <- tryAllM $ do
                (_, zonkedEvBinds, zonkedBinds, _, _, _, _) <-
                    zonkTopDecls allEvBinds binds [] [] [] []
                (_, mbCorePairs) <- initDsTc $
                    dsEvBinds zonkedEvBinds $ \evCoreBinds -> do
                        corePairsOL <- dsTopLHsBinds zonkedBinds
                        pure (flattenBinds evCoreBinds ++ fromOL corePairsOL)
                pure $ case mbCorePairs of
                    Nothing -> emptyNameEnv
                    Just pairs ->
                        mkNameEnv [(idName b, (b, rhs)) | (b, rhs) <- pairs]
            pure $ case res of
                Left _ -> emptyNameEnv
                Right env -> env

inlineLocalLetRec ::
    NameEnv (Id, CoreExpr) ->
    CoreExpr ->
    ([Name], CoreExpr)
inlineLocalLetRec locals expr
    | isEmptyNameEnv locals = ([], expr)
    | null roots = ([], expr)
    | otherwise = (localNames, foldr Let (rewriteExpr expr) sccBinds)
  where
    roots =
        [ idName v
        | v <- exprSomeFreeVarsList isId expr
        , isJust (lookupNameEnv locals (idName v))
        ]

    closure :: NameSet -> [Name] -> [Name]
    closure _ [] = []
    closure seen (n : ns)
        | n `elemNameSet` seen = closure seen ns
        | Just (_, rhs) <- lookupNameEnv locals n =
            let deps =
                    [ idName v
                    | v <- exprSomeFreeVarsList isId rhs
                    , isJust (lookupNameEnv locals (idName v))
                    ]
             in n : closure (extendNameSet seen n) (deps ++ ns)
        | otherwise = closure seen ns

    needed = closure emptyNameSet roots

    entries =
        [ (owner, rhs)
        | nm <- needed
        , Just (owner, rhs) <- [lookupNameEnv locals nm]
        ]

    mkLetBndr :: Id -> Id
    mkLetBndr owner
        | isCoVar owner = mkCoVar (idName owner) (idType owner)
        | otherwise =
            mkSysLocal (occNameFS (nameOccName (idName owner))) (idUnique owner) ManyTy (idType owner)

    valPairs = [(owner, Var (mkLetBndr owner)) | (owner, _) <- entries, not (isCoVar owner)]
    coPairs = [(owner, mkCoVarCo (mkLetBndr owner)) | (owner, _) <- entries, isCoVar owner]
    allBndrs = [mkLetBndr owner | (owner, _) <- entries]

    rewriteExpr :: CoreExpr -> CoreExpr
    rewriteExpr e =
        let fvs = exprSomeFreeVarsList (const True) e
            inScope = mkInScopeSet (mkVarSet (fvs ++ map fst entries ++ allBndrs))
            sub0 = CoreSubst.extendIdSubstList (CoreSubst.mkEmptySubst inScope) valPairs
            sub1 = foldl (\s (cv, co) -> CoreSubst.extendCvSubst s cv co) sub0 coPairs
         in CoreSubst.substExpr sub1 e

    localNames = [idName owner | (owner, _) <- entries]

    rewrittenNodes =
        let keySet = Set.fromList [getKey (getUnique b) | b <- allBndrs]
         in [ ( (letBndr, rhs')
              , getKey (getUnique letBndr)
              , [ getKey (getUnique v)
                | v <- exprSomeFreeVarsList isId rhs'
                , getKey (getUnique v) `Set.member` keySet
                ]
              )
            | (owner, rhs) <- entries
            , let letBndr = mkLetBndr owner
                  rhs' = rewriteExpr rhs
            ]

    sccBinds =
        [ case scc of
            Graph.AcyclicSCC (b, r) -> NonRec b r
            Graph.CyclicSCC prs -> Rec [(b, r) | (b, r) <- prs, not (isCoVar b)]
        | scc <- Graph.stronglyConnComp rewrittenNodes
        ]
