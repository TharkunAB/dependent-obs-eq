{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : Dependent.Plugin.ObsEq
-- Description : Observational-equivalence TcPlugin for Dependent Haskell
-- License     : BSD-3-Clause
-- Maintainer  : mpg@mpg.is
--
-- GHC typechecker plugin that tests open type-level equalities via bounded
-- Kleene approximation ('ObsTree') over total and partial ('ObsBottom')
-- inputs, refutes false equalities with shrunk counterexamples, and discharges
-- explicit observational equality constraints ('ObsEq', 'ObsEqWith',
-- 'ObsEqGen').
--
-- Credit: Based on the observational-equivalence / QuickCheck @TcPlugin@ idea
-- proposed by Jules (\@analytichegel).
module Dependent.Plugin.ObsEq
  ( plugin
  , DischargePolicy (..)
  , PluginOpts (..)
  , parsePluginOpts
  ) where

import Control.Monad ( foldM, forM, guard, when, zipWithM )
import Data.Char ( isSpace )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import Data.List ( isPrefixOf, nubBy )
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import Data.Maybe ( catMaybes, isJust, isNothing, mapMaybe )
import qualified Data.Set as Set
import Data.Time.Clock ( getCurrentTime )
import Data.Word ( Word64 )
import Numeric.Natural ( Natural )
import Text.Read ( readMaybe )

import Dependent.ObsEq
  ( InconclusiveReason (..)
  , ObsConfig (..)
  , defaultObsConfig
  , renderInconclusiveReason
  )
import Dependent.Plugin.ObsEq.Rewrite
  ( KBEnv
  , buildKBEnv
  , normalizeTypeKB
  , proveGoalConstructively
  )

import GHC.Builtin.Modules ( mkInteractiveModule )
import qualified GHC.ByteCode.Serialize as ByteCode
import GHC.Core.Class ( Class, classMethods, classTyCon )
import GHC.Core.Coercion.Axiom
  ( closedTyFamCoAxiom_maybe
  , coAxBranchLHS
  , coAxBranchRHS
  , coAxBranchTyVars
  , coAxiomBranches
  , fromBranches
  )
import GHC.Core.InstEnv ( InstEnvs, instanceDFunId, lookupUniqueInstEnv )
import GHC.Core.Map.Type
  ( TypeMap
  , emptyCME
  , emptyTypeMap
  , extendCMEs
  , extendTypeMap
  , extendTypeMapWithScope
  , lookupTypeMap
  , lookupTypeMapWithScope
  )
import GHC.Core.Multiplicity ( scaledThing )
import GHC.Core.Predicate
  ( EqRel (NomEq)
  , Pred (ClassPred, EqPred)
  , classifyPredType
  , getClassPredTys_maybe
  , mkClassPred
  )
import qualified GHC.Core.Subst as CoreSubst
import GHC.Core.TyCo.FVs ( mkUnivCoDeps, tyCoVarsOfTypeList )
import GHC.Core.TyCo.Rep ( TyLit (..), Type (..), UnivCoProvenance (..) )
import qualified GHC.Core.TyCo.Subst as TySubst
import GHC.Core.Unify ( tcMatchTys )
import GHC.Data.OrdList ( fromOL )
import qualified GHC.Data.Strict as Strict
import GHC.Driver.Main ( hscCompileCoreExpr )
import GHC.Hs ( CollectFlag (CollNoDictBinders), GhcTc, LHsBind, collectHsBindBinders )
import GHC.HsToCore.Binds ( dsEvBinds, dsTopLHsBinds )
import GHC.HsToCore.Monad ( initDsTc )
import GHC.Iface.Env ( lookupOrig )
import GHC.Linker.Loader ( getLoaderState, initLoaderState, loadDecls )
import GHC.Linker.Types
  ( LinkablePart (DotGBC)
  , LinkableUsage
  , LinkableWith (..)
  , PkgsLoaded
  , bco_loader_state
  , emptyBytecodeLoaderState
  , lookupInfoTableBytecodeState
  )
import GHC.Plugins hiding ( TcPlugin, (<>) )
import GHC.Runtime.Interpreter ( Interp, evalString )
import GHC.StgToByteCode ( byteCodeGen )
import GHC.Tc.Errors.Types ( TcRnMessage (TcRnUnknownMessage) )
import GHC.Tc.Plugin ( findImportedModule, tcPluginIO, tcPluginTrace )
import GHC.Tc.Types
  ( SourceCheckState (..)
  , TcGblEnv (..)
  , TcM
  , TcPlugin (..)
  , TcPluginM
  , TcPluginSolveResult (..)
  , unsafeTcPluginTcM
  )
import GHC.Tc.Types.Constraint
  ( Ct
  , ctLoc
  , ctPred
  , insolubleCt
  )
import GHC.Tc.Types.CtLoc ( ctLocOrigin, ctLocSpan )
import GHC.Tc.Types.Evidence ( EvBindsVar, EvTerm (EvExpr), evCoercion )
import GHC.Tc.Types.Origin ( CtOrigin (ExprHoleOrigin) )
import GHC.Tc.Utils.Env
  ( tcGetInstEnvs
  , tcLookupClass
  , tcLookupDataCon
  , tcLookupId
  , tcLookupIdMaybe
  , tcLookupTyCon
  )
import GHC.Tc.Utils.Monad
  ( addErrAt
  , getGblEnv
  , getTopEnv
  , liftZonkM
  , newUnique
  , recordThNeededRuntimeDeps
  , tryAllM
  , updTcRef
  )
import GHC.Tc.Utils.TcType ( isMetaTyVar, isTyFamFree, tcEqType )
import GHC.Tc.Zonk.TcType ( zonkTcType )
import GHC.Tc.Zonk.Type ( zonkTopDecls )
import GHC.Types.Error ( mkPlainError, mkSimpleUnknownDiagnostic, noHints )
import GHC.Types.Unique.DFM ( emptyUDFM, plusUDFM )
import qualified GHC.Unit.Finder as Finder

{- Note [Implicit solver discharge vs explicit obsEq]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Credit: Jules (@analytichegel) proposed using randomized property testing inside
a GHC `TcPlugin` to test observational equalities on open terms in Dependent
Haskell.

This plugin supports two discharge policies (`DischargePolicy`):

1. `ExplicitOnly` (default, `-fplugin-opt=Dependent.Plugin.ObsEq:policy=explicit`):
   * Explicit observational constraints (`ObsEq`, `ObsEqWith`, `ObsEqGen`) run
     bounded Kleene-approximation testing. When all configured samples agree,
     the plugin constructs dictionary evidence backed by
     `UnivCo (PluginProv "dependent-obs-eq")` with complete `UnivCoDeps`.
   * Bare Wanted nominal equalities (`[W] lhs ~# rhs`, such as bare `Refl`)
     still run bounded observational testing for *refutation*: if a total or
     partial (`ObsBottom`) sample distinguishes `lhs` and `rhs`, the plugin
     shrinks the sample and reports the minimal counterexample immediately. If
     all samples agree, the plugin leaves `[W] lhs ~# rhs` unsolved so `Refl`
     requires a deductive proof or an explicit `obsEq` call.

   `ExplicitOnly` is the default because randomized testing over `N` finite and
   partial samples does not establish universal equality across uninspected
   inputs (for example, laws that fail only above `max-size`). Requiring
   `obsEq` marks probabilistic assumptions explicitly in source code while
   giving automatic counterexample diagnostics everywhere.

2. `ImplicitAssume` (`-fplugin-opt=Dependent.Plugin.ObsEq:policy=assume`):
   * Keeps counterexample refutation active on all testable nominal equalities.
   * When a stuck Wanted nominal equality `[W] lhs ~# rhs` has no touchable
     metavariables or coercion holes and passes all `N > 0` observational
     samples, the plugin discharges `ct` directly with `evCoercion` and records
     an informational solver trace via `tcPluginTrace` (plus a diagnostic note
     when `warn-assume` is enabled).
-}

{- Note [Bytecode observational harness in TcPluginSolve]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For each candidate constraint over `(lhs :: R)` and `(rhs :: R)`, the plugin:

1. Applies in-scope Given nominal equalities `[G] v ~# expr` to `(lhs, rhs)`,
   recording used Given `Coercion`s for `mkUnivCoAddTypeDeps`.
2. Collects free runtime indices (`TermVarTy x_i`) and free value-kinded skolem
   type variables (`TyVarTy tv_i`), and instantiates polymorphic `Type`-kinded
   skolem parameters to `Int` inside the ephemeral test expression.
3. Resolves an `ObsGen D_i` dictionary for each domain `D_i` and for the result
   type `R`: first from `InstEnvs` (`lookupUniqueInstEnv`), and otherwise by
   synthesizing an `AdtObsDict` for vanilla boxed algebraic datatypes (such as
   `HaskLib.Nat.Nat` or user ADTs).
4. Reifies `lhs` and `rhs` (translating promoted constructors, literals,
   certified `T:f` source families, and uninterpreted `U:f` families back to
   Core expressions) and builds a single `IO String` invocation of
   `Dependent.ObsEq.runObsTestLoop`.
5. Wraps referenced same-module bindings (from `tcg_local_open_defs` or
   desugared on demand from `tcg_binds`) in a local `Let (Rec ...)` block,
   registers local datatype info tables via `byteCodeGen` and `loadDecls`, and
   executes the harness once in bytecode via `hscCompileCoreExpr` (with
   `Opt_OmitYields` cleared) and `evalString`. Precompiled external native
   modules that contain zero-allocation infinite loops should be compiled with
   `-fno-omit-yields` so `System.Timeout.timeout` can interrupt them at safe
   points.
-}

-- | Policy controlling whether observational verification emits no coercions
-- ('RefuteOnly'), discharges only explicit goals ('ExplicitOnly'), or also
-- discharges bare nominal equalities ('ImplicitAssume').
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
          Right st {poPolicy = RefuteOnly}
      | opt == "explicit" || opt == "policy=explicit" =
          Right st {poPolicy = ExplicitOnly}
      | opt == "assume" || opt == "policy=assume" =
          Right st {poPolicy = ImplicitAssume}
      | opt == "warn-assume" =
          Right st {poWarnAssume = True}
      | Just v <- stripKey "tests=" opt = do
          n <- readNatOpt "tests" v
          Right st {poConfig = (poConfig st) {obsTests = max 1 n}}
      | Just v <- stripKey "max-size=" opt = do
          n <- readNatOpt "max-size" v
          Right st {poConfig = (poConfig st) {obsMaxSize = n}}
      | Just v <- stripKey "approx-depth=" opt = do
          n <- readNatOpt "approx-depth" v
          Right st {poConfig = (poConfig st) {obsApproxDepth = max 1 n}}
      | Just v <- stripKey "partial-pct=" opt = do
          n <- readNatOpt "partial-pct" v
          Right st {poConfig = (poConfig st) {obsPartialPct = min 100 n}}
      | Just v <- stripKey "timeout-us=" opt = do
          n <- readNatOpt "timeout-us" v
          Right st {poConfig = (poConfig st) {obsTimeoutUs = max 1 n}}
      | Just v <- stripKey "seed=" opt = do
          n <- readNatOpt "seed" v
          Right st {poConfig = (poConfig st) {obsSeed = n}}
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

type VerdictCacheKey = (ObsConfig, Bool)

data PluginState = PluginState
  { psOpts :: !PluginOpts
  , psOptErr :: !(Maybe String)
  , psCachedEnv :: !(IORef (Maybe CachedObsEnv))
  , psReportedSpans :: !(IORef (Set.Set (String, String)))
  , psDesugarCache :: !(IORef (Maybe (Module, Int, NameEnv (Id, CoreExpr))))
  , psVerdictCache :: !(IORef (Map.Map VerdictCacheKey (TypeMap (TypeMap ObsCheckOutcome))))
  , psSideCache :: !(IORef (Map.Map ObsConfig (TypeMap [Word64])))
  }

data CachedObsEnv = CachedObsEnv
  { ceObsEqCls :: !Class
  , ceObsEqWithCls :: !Class
  , ceObsEqGenCls :: !Class
  , ceObsGenCls :: !Class
  , ceTyEqTc :: !TyCon
  , ceReflDc :: !DataCon
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
  , ceMkAdtDictId :: !Id
  , ceAdtGenId :: !Id
  , ceAdtGenPartialId :: !Id
  , ceAdtShrinkId :: !Id
  , ceAdtApproxId :: !Id
  , ceAdtShowId :: !Id
  , ceRunLoopId :: !Id
  , ceEvalSideFpId :: !Id
  , cePureGenId :: !Id
  , ceApGenId :: !Id
  , cePureIOId :: !Id
  , ceBindIOId :: !Id
  , ceAppendStrId :: !Id
  , cePairGenId :: !Id
  , cePairShrinkId :: !Id
  , cePairShowId :: !Id
  , ceNamedShowId :: !Id
  , ceSplitPairGenId :: !Id
  , ceSplitTripleGenId :: !Id
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
          let eqMod = mkModule (stringToUnit "ghc-internal") (mkModuleName "GHC.Internal.Data.Type.Equality")
              typesMod = mkModule (stringToUnit "ghc-internal") (mkModuleName "GHC.Internal.Types")
          env <- unsafeTcPluginTcM $ do
            obsEqCls <- lookupOrig obsMod (mkTcOcc "ObsEq") >>= tcLookupClass
            obsEqWithCls <- lookupOrig obsMod (mkTcOcc "ObsEqWith") >>= tcLookupClass
            obsEqGenCls <- lookupOrig obsMod (mkTcOcc "ObsEqGen") >>= tcLookupClass
            obsGenCls <- lookupOrig obsMod (mkTcOcc "ObsGen") >>= tcLookupClass
            tyEqTc <- lookupOrig eqMod (mkTcOcc ":~:") >>= tcLookupTyCon
            reflDc <- lookupOrig eqMod (mkDataOcc "Refl") >>= tcLookupDataCon
            orderingTc <- lookupOrig typesMod (mkTcOcc "Ordering") >>= tcLookupTyCon
            obsConfigTc <- lookupOrig obsMod (mkTcOcc "ObsConfig") >>= tcLookupTyCon
            obsConfigDc <- lookupOrig obsMod (mkDataOcc "ObsConfig") >>= tcLookupDataCon
            obsTreeTc <- lookupOrig obsMod (mkTcOcc "ObsTree") >>= tcLookupTyCon
            obsConDc <- lookupOrig obsMod (mkDataOcc "ObsCon") >>= tcLookupDataCon
            genTc <- lookupOrig obsMod (mkTcOcc "Gen") >>= tcLookupTyCon
            obsGenId <- lookupOrig obsMod (mkVarOcc "obsGen") >>= tcLookupId
            obsGenPartialId <- lookupOrig obsMod (mkVarOcc "obsGenPartial") >>= tcLookupId
            obsShrinkId <- lookupOrig obsMod (mkVarOcc "obsShrink") >>= tcLookupId
            obsApproxId <- lookupOrig obsMod (mkVarOcc "obsApprox") >>= tcLookupId
            obsShowId <- lookupOrig obsMod (mkVarOcc "obsShow") >>= tcLookupId
            mkAdtDictId <- lookupOrig obsMod (mkVarOcc "mkAdtObsDict") >>= tcLookupId
            adtGenId <- lookupOrig obsMod (mkVarOcc "adtGen") >>= tcLookupId
            adtGenPartialId <- lookupOrig obsMod (mkVarOcc "adtGenPartial") >>= tcLookupId
            adtShrinkId <- lookupOrig obsMod (mkVarOcc "adtShrink") >>= tcLookupId
            adtApproxId <- lookupOrig obsMod (mkVarOcc "adtApprox") >>= tcLookupId
            adtShowId <- lookupOrig obsMod (mkVarOcc "adtShow") >>= tcLookupId
            runLoopId <- lookupOrig obsMod (mkVarOcc "runObsTestLoop") >>= tcLookupId
            evalSideFpId <- lookupOrig obsMod (mkVarOcc "evalSideFingerprints") >>= tcLookupId
            pureGenId <- lookupOrig obsMod (mkVarOcc "obsPureGen") >>= tcLookupId
            apGenId <- lookupOrig obsMod (mkVarOcc "obsApGen") >>= tcLookupId
            pureIOId <- lookupOrig obsMod (mkVarOcc "obsPureIO") >>= tcLookupId
            bindIOId <- lookupOrig obsMod (mkVarOcc "obsBindIO") >>= tcLookupId
            appendStrId <- lookupOrig obsMod (mkVarOcc "obsAppendStr") >>= tcLookupId
            pairGenId <- lookupOrig obsMod (mkVarOcc "obsPairGen") >>= tcLookupId
            pairShrinkId <- lookupOrig obsMod (mkVarOcc "obsPairShrink") >>= tcLookupId
            pairShowId <- lookupOrig obsMod (mkVarOcc "obsPairShow") >>= tcLookupId
            namedShowId <- lookupOrig obsMod (mkVarOcc "obsNamedShow") >>= tcLookupId
            splitPairGenId <- lookupOrig obsMod (mkVarOcc "obsSplitPairGen") >>= tcLookupId
            splitTripleGenId <- lookupOrig obsMod (mkVarOcc "obsSplitTripleGen") >>= tcLookupId
            pure
              CachedObsEnv
                { ceObsEqCls = obsEqCls
                , ceObsEqWithCls = obsEqWithCls
                , ceObsEqGenCls = obsEqGenCls
                , ceObsGenCls = obsGenCls
                , ceTyEqTc = tyEqTc
                , ceReflDc = reflDc
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
                , ceMkAdtDictId = mkAdtDictId
                , ceAdtGenId = adtGenId
                , ceAdtGenPartialId = adtGenPartialId
                , ceAdtShrinkId = adtShrinkId
                , ceAdtApproxId = adtApproxId
                , ceAdtShowId = adtShowId
                , ceRunLoopId = runLoopId
                , ceEvalSideFpId = evalSideFpId
                , cePureGenId = pureGenId
                , ceApGenId = apGenId
                , cePureIOId = pureIOId
                , ceBindIOId = bindIOId
                , ceAppendStrId = appendStrId
                , cePairGenId = pairGenId
                , cePairShrinkId = pairShrinkId
                , cePairShowId = pairShowId
                , ceNamedShowId = namedShowId
                , ceSplitPairGenId = splitPairGenId
                , ceSplitTripleGenId = splitTripleGenId
                }
          tcPluginIO (writeIORef (psCachedEnv st) (Just env))
          pure (Just env)
        _ -> pure Nothing

data CandidateGoal
  = ExplicitDictGoal
      { cgCt :: !Ct
      , cgClass :: !Class
      , cgClassArgs :: ![Type]
      , cgKind :: !Kind
      , cgOrigLhs :: !Type
      , cgOrigRhs :: !Type
      , cgCfgTy :: !(Maybe Type)
      , cgGenTy :: !(Maybe (Kind, Type))
      }
  | BareNominalGoal
      { cgCt :: !Ct
      , cgKind :: !Kind
      , cgOrigLhs :: !Type
      , cgOrigRhs :: !Type
      }

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
     the plugin runs 'runObservationalCheck' without mutating 'psReportedSpans',
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

isSpeculativeHoleCt :: Ct -> Bool
isSpeculativeHoleCt ct =
  case ctLocOrigin (ctLoc ct) of
    ExprHoleOrigin _ -> True
    _ -> False

solveObsEq :: PluginState -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solveObsEq st _evBinds givens wanteds
  | null wanteds = pure (TcPluginOk [] [])
  | Just errMsg <- psOptErr st = do
      case wanteds of
        ct : _ ->
          unsafeTcPluginTcM $
            addErrAt (RealSrcSpan (ctLocSpan (ctLoc ct)) Strict.Nothing) $
              TcRnUnknownMessage (mkSimpleUnknownDiagnostic (mkPlainError noHints (text errMsg)))
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
              let goalTys = concat [[cgOrigLhs g, cgOrigRhs g] | g <- candidates]
                  kbEnv = buildKBEnv givens goalTys
              adtCacheRef <- tcPluginIO (newIORef emptyTypeMap)
              prepared <- forM candidates (prepareGoal st cenv kbEnv adtCacheRef)
              let tasks = [t | PreparedTask t <- prepared]
              batchOuts <-
                case tasks of
                  [] -> pure (Just [])
                  t0 : _ ->
                    let locSpan = pbtLocSpan t0
                        anyReal = any (not . pbtSpeculative) tasks
                     in unsafeTcPluginTcM $
                          runCoreIOStringBatch st cenv locSpan anyReal (map pbtBatchIo tasks)
              outcomes <- finalizePreparedGoals st cenv prepared batchOuts
              let bads = [ct | Left ct <- outcomes]
                  solved = [pair | Right (Just pair) <- outcomes]
              if not (null bads)
                then pure (TcPluginContradiction bads)
                else pure (TcPluginOk solved [])

classifyWanted :: CachedObsEnv -> Ct -> Maybe CandidateGoal
classifyWanted cenv ct
  | insolubleCt ct = Nothing
  | hasCoercionHole predTy = Nothing
  | any isMetaTyVar (tyCoVarsOfTypeList predTy) = Nothing
  | otherwise =
      case classifyPredType predTy of
        ClassPred cls args
          | cls == ceObsEqCls cenv
          , [k, lhs, rhs] <- args
          , validPromotedKind k ->
              Just
                ExplicitDictGoal
                  { cgCt = ct
                  , cgClass = cls
                  , cgClassArgs = args
                  , cgKind = k
                  , cgOrigLhs = lhs
                  , cgOrigRhs = rhs
                  , cgCfgTy = Nothing
                  , cgGenTy = Nothing
                  }
          | cls == ceObsEqWithCls cenv
          , [k, cfgTy, lhs, rhs] <- args
          , validPromotedKind k ->
              Just
                ExplicitDictGoal
                  { cgCt = ct
                  , cgClass = cls
                  , cgClassArgs = args
                  , cgKind = k
                  , cgOrigLhs = lhs
                  , cgOrigRhs = rhs
                  , cgCfgTy = Just cfgTy
                  , cgGenTy = Nothing
                  }
          | cls == ceObsEqGenCls cenv
          , [ga, k, genTy, lhs, rhs] <- args
          , validPromotedKind k ->
              Just
                ExplicitDictGoal
                  { cgCt = ct
                  , cgClass = cls
                  , cgClassArgs = args
                  , cgKind = k
                  , cgOrigLhs = lhs
                  , cgOrigRhs = rhs
                  , cgCfgTy = Nothing
                  , cgGenTy = Just (ga, genTy)
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

collectFreeTermAndTyVars :: [Type] -> [Var]
collectFreeTermAndTyVars tys =
  nubBy (\a b -> getUnique a == getUnique b) (concatMap walk tys)
  where
    walk ty =
      case coreFullView ty of
        TermVarTy v -> walk (varType v) ++ [v]
        TermAppTy f arg -> walk (varType f) ++ [f] ++ walk arg
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

-- ---------------------------------------------------------------------------
-- Preparing, Caching, and Finalizing Candidate Goals
-- ---------------------------------------------------------------------------

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

prepareGoal
  :: PluginState
  -> CachedObsEnv
  -> KBEnv
  -> IORef AdtCache
  -> CandidateGoal
  -> TcPluginM PreparedGoal
prepareGoal st cenv kbEnv adtCacheRef goal = do
  let ct = cgCt goal
      speculative = isSpeculativeHoleCt ct
      locSpan = RealSrcSpan (ctLocSpan (ctLoc ct)) Strict.Nothing
      origLhs = cgOrigLhs goal
      origRhs = cgOrigRhs goal

  -- Step 1: Zero-UnivCo constructive KBO check (valid under all policies!)
  case proveGoalConstructively kbEnv origLhs origRhs of
    Just constructiveCo -> do
      case goal of
        ExplicitDictGoal {cgClass = cls, cgClassArgs = clsArgs, cgKind = k} -> do
          let ev = mkExplicitDictEv cenv cls clsArgs k origLhs origRhs constructiveCo
          pure (PreparedDone (Right (Just (ev, ct))))
        BareNominalGoal {} ->
          pure (PreparedDone (Right (Just (evCoercion constructiveCo, ct))))
    Nothing -> do
      -- Step 2: Speculative ExprHoleOrigin fast skip on BareNominalGoal
      case (speculative, goal, poPolicy (psOpts st)) of
        (True, BareNominalGoal {}, RefuteOnly) -> pure (PreparedDone (Right Nothing))
        (True, BareNominalGoal {}, ExplicitOnly) -> pure (PreparedDone (Right Nothing))
        _ -> do
          let (lhsSub, _, cosL) = normalizeTypeKB kbEnv origLhs
              (rhsSub, _, cosR) = normalizeTypeKB kbEnv origRhs
              usedGivenCos = cosL ++ cosR

          mbCfg <- case cgCfgGoal goal of
            Nothing -> pure (Just (poConfig (psOpts st)))
            Just cfgTy -> unsafeTcPluginTcM (evalObsConfigType st cenv locSpan speculative cfgTy)
          case mbCfg of
            Nothing -> pure (PreparedDone (Right Nothing))
            Just cfg -> do
              let mbGen = cgGenGoal goal
                  canonVars = collectValueVars [lhsSub, rhsSub]
                  cacheKey = (cfg, isJust mbGen)
                  canCache = isNothing mbGen
              mbCached <-
                if canCache
                  then lookupCachedVerdict st cacheKey canonVars lhsSub rhsSub
                  else pure Nothing
              case mbCached of
                Just cachedOutcome -> do
                  res <- applyVerdictToGoal st cenv goal locSpan speculative usedGivenCos cachedOutcome
                  pure (PreparedDone res)
                Nothing -> do
                  mbBuilt <- unsafeTcPluginTcM $
                    buildGoalBcoTask st cenv adtCacheRef cfg mbGen (cgKind goal) lhsSub rhsSub
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
    cgCfgGoal ExplicitDictGoal {cgCfgTy = c} = c
    cgCfgGoal BareNominalGoal {} = Nothing

    cgGenGoal ExplicitDictGoal {cgGenTy = g} = g
    cgGenGoal BareNominalGoal {} = Nothing

collectValueVars :: [Type] -> [Var]
collectValueVars tys =
  [ v
  | v <- collectFreeTermAndTyVars tys
  , let vk = if isTyVar v then tyVarKind v else varType v
  , not (tcIsLiftedTypeKind vk)
  , tcIsLiftedTypeKind (typeKind vk)
  ]

lookupCachedVerdict
  :: PluginState
  -> VerdictCacheKey
  -> [Var]
  -> Type
  -> Type
  -> TcPluginM (Maybe ObsCheckOutcome)
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

storeCachedVerdict
  :: PluginState
  -> VerdictCacheKey
  -> [Var]
  -> Type
  -> Type
  -> ObsCheckOutcome
  -> TcPluginM ()
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

finalizePreparedGoals
  :: PluginState
  -> CachedObsEnv
  -> [PreparedGoal]
  -> Maybe [String]
  -> TcPluginM [Either Ct (Maybe (EvTerm, Ct))]
finalizePreparedGoals st cenv prepared mbStrings = go prepared (fromMaybeList mbStrings)
  where
    fromMaybeList Nothing = Nothing
    fromMaybeList (Just xs) = Just xs

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

    isExplicitGoal ExplicitDictGoal {} = True
    isExplicitGoal BareNominalGoal {} = False

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

storeSideFingerprints
  :: PluginState
  -> ObsConfig
  -> [Var]
  -> Type
  -> Type
  -> [Word64]
  -> [Word64]
  -> TcPluginM ()
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

applyVerdictToGoal
  :: PluginState
  -> CachedObsEnv
  -> CandidateGoal
  -> SrcSpan
  -> Bool
  -> [Coercion]
  -> ObsCheckOutcome
  -> TcPluginM (Either Ct (Maybe (EvTerm, Ct)))
applyVerdictToGoal st cenv goal locSpan speculative usedGivenCos outcome = do
  let ct = cgCt goal
      origLhs = cgOrigLhs goal
      origRhs = cgOrigRhs goal
  case outcome of
    ObsCheckRefuted counterexample -> do
      when (not speculative) $
        emitCounterexampleOnce st locSpan origLhs origRhs counterexample
      pure (Left ct)
    ObsCheckInconclusive reason ->
      case (speculative, poPolicy (psOpts st), goal) of
        (True, _, ExplicitDictGoal {}) -> pure (Left ct)
        (True, _, BareNominalGoal {}) -> pure (Right Nothing)
        (_, RefuteOnly, _) -> pure (Right Nothing)
        (_, _, ExplicitDictGoal {}) -> do
          emitInconclusiveOnce st locSpan origLhs origRhs (renderInconclusiveReason reason)
          pure (Right Nothing)
        (_, _, BareNominalGoal {}) -> pure (Right Nothing)
    ObsCheckVerified ->
      case poPolicy (psOpts st) of
        RefuteOnly ->
          case (speculative, goal) of
            (True, ExplicitDictGoal {}) -> pure (Left ct)
            _ -> pure (Right Nothing)
        ExplicitOnly ->
          case goal of
            ExplicitDictGoal {cgClass = cls, cgClassArgs = clsArgs, cgKind = k} -> do
              when (not speculative) $
                tcPluginTrace "dependent-obs-eq: discharged explicit goal" (ppr (ctPred ct))
              let co = mkPluginUnivCo usedGivenCos origLhs origRhs
                  ev = mkExplicitDictEv cenv cls clsArgs k origLhs origRhs co
              pure (Right (Just (ev, ct)))
            BareNominalGoal {} -> pure (Right Nothing)
        ImplicitAssume -> do
          let co = mkPluginUnivCo usedGivenCos origLhs origRhs
          case goal of
            ExplicitDictGoal {cgClass = cls, cgClassArgs = clsArgs, cgKind = k} -> do
              when (not speculative) $
                tcPluginTrace "dependent-obs-eq: discharged explicit goal" (ppr (ctPred ct))
              let ev = mkExplicitDictEv cenv cls clsArgs k origLhs origRhs co
              pure (Right (Just (ev, ct)))
            BareNominalGoal {} -> do
              when (not speculative) $ do
                tcPluginTrace "dependent-obs-eq: implicitly assumed nominal equality" (ppr (ctPred ct))
                when (poWarnAssume (psOpts st)) $
                  emitCounterexampleOnce st locSpan origLhs origRhs
                    "Note: assumed via policy=assume"
              pure (Right (Just (evCoercion co, ct)))

mkPluginUnivCo :: [Coercion] -> Type -> Type -> Coercion
mkPluginUnivCo usedGivenCos lhs rhs =
  mkUnivCoAddTypeDeps
    (PluginProv "dependent-obs-eq")
    (mkUnivCoDeps usedGivenCos)
    Nominal
    lhs
    rhs

mkExplicitDictEv
  :: CachedObsEnv
  -> Class
  -> [Type]
  -> Kind
  -> Type
  -> Type
  -> Coercion
  -> EvTerm
mkExplicitDictEv cenv cls clsArgs k lhs _rhs co =
  let reflBase = mkCoreApps (Var (dataConWrapId (ceReflDc cenv))) [Type k, Type lhs]
      tyEqCo = mkSubCo (mkTyConAppCo Nominal (ceTyEqTc cenv) [mkNomReflCo k, mkNomReflCo lhs, co])
      proofExpr = mkCast reflBase tyEqCo
      clsDc = tyConSingleDataCon (classTyCon cls)
      dictExpr = mkCoreApps (Var (dataConWrapId clsDc)) (map Type clsArgs ++ [proofExpr])
   in EvExpr dictExpr

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
      when (not (gopt Opt_DeferTypeErrors dflags)) $
        addErrAt sp $
          TcRnUnknownMessage (mkSimpleUnknownDiagnostic (mkPlainError noHints detailsDoc))

-- ---------------------------------------------------------------------------
-- Evaluating Promoted ObsConfig
-- ---------------------------------------------------------------------------

evalObsConfigType :: PluginState -> CachedObsEnv -> SrcSpan -> Bool -> Type -> TcM (Maybe ObsConfig)
evalObsConfigType st cenv locSpan speculative cfgTy =
  case decodePromotedObsConfig cfgTy of
    Just cfg -> pure (Just cfg)
    Nothing -> do
      gblEnv <- getGblEnv
      localDefs <- getCachedModuleDefs st gblEnv
      case peelScalarObsConfig localDefs (poConfig (psOpts st)) 16 cfgTy of
        Just cfg -> pure (Just cfg)
        Nothing -> do
          mbCore <- reifyTypeToCore cenv emptyUFM cfgTy
          case mbCore of
            Nothing -> pure Nothing
            Just cfgExpr
              | not (exprType cfgExpr `tcEqType` mkTyConApp (ceObsConfigTc cenv) []) ->
                  pure Nothing
              | Just cfg <- peelScalarObsConfigCore localDefs (poConfig (psOpts st)) 16 cfgExpr ->
                  pure (Just cfg)
              | otherwise -> do
                  showCls <- lookupOrig (moduleNameToGhcInternal "GHC.Internal.Show") (mkTcOcc "Show") >>= tcLookupClass
                  instEnvs <- tcGetInstEnvs
                  case resolveClassDict cenv emptyTypeMap instEnvs (mkClassPred showCls [mkTyConApp (ceObsConfigTc cenv) []]) of
                    Nothing -> pure Nothing
                    Just showDict ->
                      case classMethods showCls of
                        (_ : showId : _) -> evaluateShowableCfg showId showDict cfgExpr
                        (showId : _) -> evaluateShowableCfg showId showDict cfgExpr
                        [] -> pure Nothing
  where
    moduleNameToGhcInternal str =
      mkModule (stringToUnit "ghc-internal") (mkModuleName str)

    evaluateShowableCfg showId showDict cfgExpr = do
      let cfgKind = mkTyConApp (ceObsConfigTc cenv) []
          strExpr = mkCoreApps (Var showId) [Type cfgKind, showDict, cfgExpr]
          ioExpr = mkCoreApps (Var (cePureIOId cenv)) [Type stringTy, strExpr]
      mbOuts <- runCoreIOStringBatch st cenv locSpan (not speculative) [ioExpr]
      pure $ case mbOuts of
        Just [s] -> parseShownObsConfig s
        _ -> Nothing

peelScalarObsConfig :: NameEnv (Id, CoreExpr) -> ObsConfig -> Int -> Type -> Maybe ObsConfig
peelScalarObsConfig localDefs baseCfg = go
  where
    go 0 _ = Nothing
    go fuel ty0 =
      case coreFullView ty0 of
        _ | Just cfg <- decodePromotedObsConfig ty0 -> Just cfg
        TermVarTy v -> peelVar (fuel - 1) v
        TyConApp tc args ->
          let occ = getOccString (tyConName tc)
              cleanOcc
                | "U:@" `isPrefixOf` occ = reverse (takeWhile (/= ':') (reverse occ))
                | "U:" `isPrefixOf` occ = drop 2 occ
                | "T:" `isPrefixOf` occ = drop 2 occ
                | otherwise = occ
           in case (cleanOcc, args) of
                ("defaultObsConfig", []) -> Just baseCfg
                ("totalObsConfig", []) -> Just baseCfg {obsPartialPct = 0}
                (fn, [nTy, inner])
                  | Just n <- isNumLitTy (coreFullView nTy) -> do
                      cfg <- go (fuel - 1) inner
                      applyScalarMod fn (fromInteger (max 0 n)) cfg
                (fn, []) -> peelByOcc localDefs baseCfg (fuel - 1) fn
                _ -> Nothing
        _ -> Nothing

    peelVar fuel v
      | getOccString v == "defaultObsConfig" = Just baseCfg
      | getOccString v == "totalObsConfig" = Just baseCfg {obsPartialPct = 0}
      | Just (_, rhs) <- lookupNameEnv localDefs (idName v) =
          peelScalarObsConfigCore localDefs baseCfg fuel rhs
      | CoreUnfolding {uf_tmpl = rhs} <- realIdUnfolding v =
          peelScalarObsConfigCore localDefs baseCfg fuel rhs
      | otherwise = Nothing

peelByOcc :: NameEnv (Id, CoreExpr) -> ObsConfig -> Int -> String -> Maybe ObsConfig
peelByOcc localDefs baseCfg fuel occ =
  case [rhs | (fnId, rhs) <- nonDetEltsUFM localDefs, getOccString fnId == occ] of
    rhs : _ -> peelScalarObsConfigCore localDefs baseCfg fuel rhs
    [] -> Nothing

peelScalarObsConfigCore :: NameEnv (Id, CoreExpr) -> ObsConfig -> Int -> CoreExpr -> Maybe ObsConfig
peelScalarObsConfigCore localDefs baseCfg = go
  where
    go 0 _ = Nothing
    go fuel expr =
      let (hd, args) = collectArgs ( stripTicks expr )
          valArgs = [a | a <- args, not (isTypeArg a)]
       in case hd of
            Var fn
              | getOccString fn == "ObsConfig"
              , [a, b, c, d, e, f] <- valArgs -> do
                  n1 <- extractNatCore (fuel - 1) a
                  n2 <- extractNatCore (fuel - 1) b
                  n3 <- extractNatCore (fuel - 1) c
                  n4 <- extractNatCore (fuel - 1) d
                  n5 <- extractNatCore (fuel - 1) e
                  n6 <- extractNatCore (fuel - 1) f
                  Just
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
                  Just baseCfg
              | getOccString fn == "totalObsConfig"
              , null valArgs ->
                  Just baseCfg {obsPartialPct = 0}
              | [nExpr, innerExpr] <- valArgs
              , Just n <- extractNatCore (fuel - 1) nExpr
              , Just innerCfg <- go (fuel - 1) innerExpr
              , Just cfg' <- applyScalarMod (getOccString fn) n innerCfg ->
                  Just cfg'
              | null valArgs ->
                  case lookupNameEnv localDefs (idName fn) of
                    Just (_, rhs) -> go (fuel - 1) rhs
                    Nothing ->
                      case realIdUnfolding fn of
                        CoreUnfolding {uf_tmpl = rhs} -> go (fuel - 1) rhs
                        _ -> Nothing
            _ -> Nothing

    stripTicks (Tick _ e) = stripTicks e
    stripTicks (Cast e _) = stripTicks e
    stripTicks e = e

    extractNatCore _ (Lit (LitNumber _ n))
      | n >= 0 = Just (fromInteger n)
    extractNatCore fuel e =
      case collectArgs (stripTicks e) of
        (Var fn, args)
          | getOccString fn `elem` ["NS", "fromInteger", "naturalFromInteger"]
          , a : _ <- [x | x <- args, not (isTypeArg x)] ->
              extractNatCore fuel a
          | (fnId, rhs) : _ <- [(b, r) | (b, r) <- nonDetEltsUFM localDefs, idName b == idName fn]
          , null [x | x <- args, not (isTypeArg x)] ->
              let _ = fnId in extractNatCore (fuel - 1) rhs
        _ -> Nothing

applyScalarMod :: String -> Natural -> ObsConfig -> Maybe ObsConfig
applyScalarMod fn n cfg =
  case fn of
    "withTests" -> Just cfg {obsTests = max 1 n}
    "setTests" -> Just cfg {obsTests = max 1 n}
    "withMaxSize" -> Just cfg {obsMaxSize = n}
    "setMaxSize" -> Just cfg {obsMaxSize = n}
    "withApproxDepth" -> Just cfg {obsApproxDepth = max 1 n}
    "setApproxDepth" -> Just cfg {obsApproxDepth = max 1 n}
    "withPartialPct" -> Just cfg {obsPartialPct = min 100 n}
    "setPartialPct" -> Just cfg {obsPartialPct = min 100 n}
    "withTimeoutUs" -> Just cfg {obsTimeoutUs = max 1 n}
    "setTimeoutUs" -> Just cfg {obsTimeoutUs = max 1 n}
    "withSeed" -> Just cfg {obsSeed = n}
    "setSeed" -> Just cfg {obsSeed = n}
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
-- Building and Executing the Bytecode Test Harness
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

data ObsCheckOutcome
  = ObsCheckVerified
  | ObsCheckRefuted !String
  | ObsCheckInconclusive !InconclusiveReason

buildGoalBcoTask
  :: PluginState
  -> CachedObsEnv
  -> IORef AdtCache
  -> ObsConfig
  -> Maybe (Kind, Type)
  -> Kind
  -> Type
  -> Type
  -> TcM (Maybe (CoreExpr, Maybe String, Bool))
buildGoalBcoTask st cenv adtCacheRef cfg mbCustomGen resKind0 lhs0 rhs0 = do
  instEnvs <- tcGetInstEnvs
  let rawFree = collectFreeTermAndTyVars [resKind0, lhs0, rhs0]
      typeSkolems = [tv | tv <- rawFree, isTyVar tv, tcIsLiftedTypeKind (tyVarKind tv)]
      hkSkolems = [tv | tv <- rawFree, isTyVar tv, isUnaryTypeConKind (tyVarKind tv)]
      allPolySet = mkVarSet (typeSkolems ++ hkSkolems)
      orderingCarrier = mkTyConTy (ceOrderingTc cenv)
  (mbPolyClass, needsIntFallback) <-
    detectPolyClassConstraint instEnvs orderingCarrier allPolySet [resKind0, lhs0, rhs0]
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
      resKind = substPoly resKind0
      lhs = substPoly lhs0
      rhs = substPoly rhs0
      valVars =
        [ (v, vk)
        | v <- collectFreeTermAndTyVars [lhs, rhs]
        , let vk = substPoly (if isTyVar v then tyVarKind v else varType v)
        , not (tcIsLiftedTypeKind vk)
        , tcIsLiftedTypeKind (typeKind vk)
        ]

  if not (noFreeVarsOfType resKind && isTyFamFree resKind && all (noFreeVarsOfType . snd) valVars && all (isTyFamFree . snd) valVars)
    then pure Nothing
    else do
      mbResOps <- resolveDomainOps cenv adtCacheRef instEnvs resKind
      mbVarOps <- traverse (resolveDomainOps cenv adtCacheRef instEnvs . snd) valVars
      case (mbResOps, sequence mbVarOps) of
        (Just resOps, Just varOpsList) -> do
          paramIds <- forM (zip ([1 :: Int ..]) valVars) $ \(idx, (v, domTy)) -> do
            u <- newUnique
            let occ = mkVarOcc ("obs_arg_" ++ show idx ++ "_" ++ getOccString v)
            pure (v, mkSysLocal (fsLit (occNameString occ)) u ManyTy domTy)
          let varEnv = listToUFM [(origV, pid) | (origV, pid) <- paramIds]
          mbLhsCore <- reifyTypeToCore cenv varEnv lhs
          mbRhsCore <- reifyTypeToCore cenv varEnv rhs
          mbEnvBundle <- buildEnvBundle cenv varEnv mbCustomGen (zip (map fst valVars) (zip (map snd paramIds) varOpsList))
          case (mbLhsCore, mbRhsCore, mbEnvBundle) of
            (Just lhsCore, Just rhsCore, Just (envTy, envGenExpr, envShrinkExpr, envShowExpr, bindEnvVars)) ->
              if not (exprType lhsCore `tcEqType` resKind && exprType rhsCore `tcEqType` resKind)
                then pure Nothing
                else do
                  cfgExpr <- buildObsConfigCore cenv cfg
                  envArgL <- freshLocal "obs_env_l" envTy
                  envArgR <- freshLocal "obs_env_r" envTy
                  let evalLhsFn = Lam envArgL (bindEnvVars (Var envArgL) lhsCore)
                      evalRhsFn = Lam envArgR (bindEnvVars (Var envArgR) rhsCore)
                      loopCall =
                        mkCoreApps
                          (Var (ceRunLoopId cenv))
                          [ Type envTy
                          , Type resKind
                          , cfgExpr
                          , envGenExpr
                          , envShrinkExpr
                          , envShowExpr
                          , doApprox resOps
                          , evalLhsFn
                          , evalRhsFn
                          ]
                  -- Attach 8-probe side fingerprints on standard uncustomized goals (<= 3 vars)
                  scMap <- liftIO (readIORef (psSideCache st))
                  let cmEnv = extendCMEs emptyCME (map fst valVars)
                      sideMap = Map.findWithDefault emptyTypeMap cfg scMap
                      hasCachedFp =
                        isJust (lookupTypeMapWithScope sideMap cmEnv lhs0)
                          && isJust (lookupTypeMapWithScope sideMap cmEnv rhs0)
                      wantFp = isNothing mbCustomGen && isNothing hasPolyDict && length valVars <= 3 && not hasCachedFp
                  if not wantFp
                    then pure (Just (loopCall, hasPolyDict, False))
                    else do
                      let fpLCall =
                            mkCoreApps
                              (Var (ceEvalSideFpId cenv))
                              [Type envTy, Type resKind, cfgExpr, envGenExpr, doApprox resOps, evalLhsFn]
                          fpRCall =
                            mkCoreApps
                              (Var (ceEvalSideFpId cenv))
                              [Type envTy, Type resKind, cfgExpr, envGenExpr, doApprox resOps, evalRhsFn]
                      combined <- chainSepIO cenv "\x1f" [loopCall, fpLCall, fpRCall]
                      pure (Just (combined, hasPolyDict, True))
            _ -> pure Nothing
        _ -> pure Nothing

isUnaryTypeConKind :: Kind -> Bool
isUnaryTypeConKind k =
  case splitFunTy_maybe (coreFullView k) of
    Just (_, _, _, dom, res) -> tcIsLiftedTypeKind dom && tcIsLiftedTypeKind res
    Nothing -> False

detectPolyClassConstraint
  :: InstEnvs
  -> Type
  -> VarSet
  -> [Type]
  -> TcM (Maybe String, Bool)
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

buildEnvBundle
  :: CachedObsEnv
  -> UniqFM Var Id
  -> Maybe (Kind, Type)
  -> [(Var, (Id, DomainOps))]
  -> TcM (Maybe (Type, CoreExpr, CoreExpr, CoreExpr, CoreExpr -> CoreExpr -> CoreExpr))
buildEnvBundle cenv varEnv mbCustomGen vars = do
  let defaultComponents =
        [ ( doType ops
          , doGenPartial ops
          , doShrink ops
          , mkCoreApps (Var (ceNamedShowId cenv)) [ Type (doType ops), mkCharListExpr (getOccString origV), doShow ops ]
          , pid
          )
        | (origV, (pid, ops)) <- vars
        ]
  (envTy, defGen, defShrink, defShow, unpacker) <- foldEnvComponents cenv defaultComponents
  case mbCustomGen of
    Nothing -> pure (Just (envTy, defGen, defShrink, defShow, unpacker))
    Just (_, genTy) -> do
      mbGenExpr <- reifyTypeToCore cenv varEnv genTy
      case mbGenExpr of
        Nothing -> pure Nothing
        Just genExpr -> do
          mbAdapted <- adaptCustomGen cenv envTy (map (doType . snd . snd) vars) genExpr
          pure $ case mbAdapted of
            Nothing -> Nothing
            Just customGenFn -> Just (envTy, customGenFn, defShrink, defShow, unpacker)

adaptCustomGen :: CachedObsEnv -> Type -> [Type] -> CoreExpr -> TcM (Maybe CoreExpr)
adaptCustomGen cenv envTy domTys genExpr = do
  let expectedDirect = mkTyConApp (ceGenTc cenv) [envTy]
      gTy = exprType genExpr
  if gTy `tcEqType` expectedDirect
    then do
      pctArg <- freshLocal "obs_pct" intTy
      pure (Just (Lam pctArg genExpr))
    else case domTys of
      [t1, t2]
        | gTy `tcEqType` mkTupleTy Boxed [mkTyConApp (ceGenTc cenv) [t1], mkTyConApp (ceGenTc cenv) [t2]] ->
            pure (Just (mkCoreApps (Var (ceSplitPairGenId cenv)) [Type t1, Type t2, genExpr]))
      [t1, t2, t3]
        | gTy `tcEqType` mkTupleTy Boxed [mkTyConApp (ceGenTc cenv) [t1], mkTyConApp (ceGenTc cenv) [t2], mkTyConApp (ceGenTc cenv) [t3]] ->
            pure (Just (mkCoreApps (Var (ceSplitTripleGenId cenv)) [Type t1, Type t2, Type t3, genExpr]))
      _ -> pure Nothing

foldEnvComponents
  :: CachedObsEnv
  -> [(Type, CoreExpr, CoreExpr, CoreExpr, Id)]
  -> TcM (Type, CoreExpr, CoreExpr, CoreExpr, CoreExpr -> CoreExpr -> CoreExpr)
foldEnvComponents cenv [] = do
  pctVar <- freshLocal "obs_pct0" intTy
  uVar1 <- freshLocal "obs_u1" unitTy
  uVar2 <- freshLocal "obs_u2" unitTy
  let genUnit = Lam pctVar (mkCoreApps (Var (cePureGenId cenv)) [Type unitTy, Var unitDataConId])
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
-- Resolving and Synthesizing ObsGen Dictionaries
-- ---------------------------------------------------------------------------

type AdtCache = TypeMap DomainOps

resolveDomainOps
  :: CachedObsEnv
  -> IORef AdtCache
  -> InstEnvs
  -> Type
  -> TcM (Maybe DomainOps)
resolveDomainOps cenv cacheRef instEnvs domTy = do
  cached <- liftIO (readIORef cacheRef)
  case lookupTypeMap cached domTy of
    Just ops -> pure (Just ops)
    Nothing -> do
      let predTy = mkClassPred (ceObsGenCls cenv) [domTy]
      case resolveClassDictWithAdt cenv cached instEnvs predTy of
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
resolveClassDict = resolveClassDictWithAdt

resolveClassDictWithAdt :: CachedObsEnv -> AdtCache -> InstEnvs -> PredType -> Maybe CoreExpr
resolveClassDictWithAdt cenv adtCache instEnvs predTy = do
  (cls, clsArgs) <- getClassPredTys_maybe predTy
  case lookupUniqueInstEnv instEnvs cls clsArgs of
    Right (clsInst, instTys) -> do
      let dfun = instanceDFunId clsInst
          (maTvs, rho) = splitForAllTyCoVars (idType dfun)
          tvs = map snd maTvs
          (_, scaledTheta, _) = splitFunTys rho
          subst = TySubst.extendTvSubstList (TySubst.mkEmptySubst (mkInScopeSet (mkVarSet tvs))) (zip tvs instTys)
          subPreds = [TySubst.substTy subst (scaledThing sc) | sc <- scaledTheta]
      subDicts <- traverse (resolveClassDictWithAdt cenv adtCache instEnvs) subPreds
      pure (mkCoreApps (Var dfun) (map Type instTys ++ subDicts))
    Left _
      | cls == ceObsGenCls cenv
      , [argTy] <- clsArgs ->
          doDict <$> lookupTypeMap adtCache argTy
      | otherwise -> Nothing

synthesizeAdtDomainOps
  :: CachedObsEnv
  -> IORef AdtCache
  -> InstEnvs
  -> Type
  -> TcM (Maybe DomainOps)
synthesizeAdtDomainOps cenv cacheRef instEnvs domTy
  | Just (tc, tcArgs) <- splitTyConApp_maybe (coreFullView domTy)
  , isVanillaAlgTyCon tc
  , isBoxedDataTyCon tc
  , let dcs = tyConDataCons tc
  , not (null dcs)
  , all isVanillaDataCon dcs = do
      let adtBundleTy = mkTyConApp (idResultTyCon (ceMkAdtDictId cenv)) [domTy]
      recBundleId <- freshLocal ("adt_bundle_" ++ getOccString (tyConName tc)) adtBundleTy
      let placeholderOps =
            mkPlaceholderOps cenv domTy (Var recBundleId)
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

buildMkAdtDictCall
  :: CachedObsEnv
  -> Type
  -> [DataCon]
  -> [Type]
  -> (Type -> Maybe DomainOps)
  -> TcM (Maybe CoreExpr)
buildMkAdtDictCall cenv domTy dcs tcArgs lookupOps = do
  let genDomTy = mkTyConApp (ceGenTc cenv) [domTy]
      nullaryDcs = [dc | dc <- dcs, dataConSourceArity dc == 0]
      baseGenExprs =
        [ mkCoreApps (Var (cePureGenId cenv)) [Type domTy, mkCoreApps (Var (dataConWorkId dc)) (map Type tcArgs)]
        | dc <- nullaryDcs
        ]

  mbTotalCons <- traverse buildTotalCon dcs
  mbPartCons <- traverse buildPartialCon dcs
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
      case traverse lookupOps fTys of
        Nothing -> pure Nothing
        Just fOps -> do
          conHead <- mkEtaConExpr dc fTys
          let pureHead = mkCoreApps (Var (cePureGenId cenv)) [Type (exprType conHead), conHead]
              step acc ops =
                let curArrow = exprType acc
                    (_, resTy) = case splitFunTy_maybe ( extractGenElem curArrow ) of
                      Just (_, _, _, _, r) -> ((), r)
                      Nothing -> error "Dependent.Plugin.ObsEq: expected FunTy in constructor"
                 in mkCoreApps (Var (ceApGenId cenv)) [Type (doType ops), Type resTy, acc, doGenTotal ops]
              body = foldl step pureHead fOps
          pure (Just (Lam szId body))

    buildPartialCon dc = do
      pctId <- freshLocal "adt_pct" intTy
      szId <- freshLocal "adt_szp" intTy
      let fTys = fieldTypes dc
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
                 in mkCoreApps (Var (ceApGenId cenv)) [Type (doType ops), Type resTy, acc, partField]
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
      mbAlts <- forM dcs $ \dc -> do
        let fTys = fieldTypes dc
        fIds <- zipWithM (\i ft -> freshLocal ("sh_f" ++ show i) ft) [1 :: Int ..] fTys
        case traverse lookupOps fTys of
          Nothing -> pure Nothing
          Just _ -> do
            let directRec = [Var fid | (fid, ft) <- zip fIds fTys, ft `tcEqType` domTy]
                initials = if null fIds then [] else directRec ++ baseShrinks
                rhs = mkListExpr domTy initials
            pure (Just (Alt (DataAlt dc) fIds rhs))
      pure $ do
        alts <- sequence mbAlts
        pure (Lam scrutId (Case (Var scrutId) caseBndr listDomTy alts))

    buildApproxFn = do
      depthId <- freshLocal "adt_ap_d" intTy
      scrutId <- freshLocal "adt_ap_x" domTy
      caseBndr <- freshLocal "adt_ap_bndr" domTy
      let treeTy = mkTyConApp (ceObsTreeTc cenv) []
          listTreeTy = mkListTy treeTy
          ioTreeTy = exprType (mkCoreApps (Var (cePureIOId cenv)) [Type treeTy, mkCoreApps (Var (dataConWrapId (ceObsConDc cenv))) [mkCharListExpr "?", mkListExpr treeTy []]])
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
                _ = listTreeTy
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
        else if "U:" `isPrefixOf` occStr
          then do
            let varStr = drop 2 occStr
            nm <- lookupOrig (nameModule tcNm) (mkVarOcc varStr)
            lookupTermId nm
          else if "T:field:" `isPrefixOf` occStr
            then pure Nothing
            else if "T:" `isPrefixOf` occStr
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

reifySingleBranchLambdaFamily
  :: CachedObsEnv
  -> UniqFM Var Id
  -> TyCon
  -> [Type]
  -> Kind
  -> TcM (Maybe CoreExpr)
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

instantiateAndApply
  :: CachedObsEnv
  -> Id
  -> [Type]
  -> Kind
  -> (Type -> TcM (Maybe CoreExpr))
  -> TcM (Maybe CoreExpr)
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

buildSpecialisedCall
  :: CachedObsEnv
  -> InstEnvs
  -> Id
  -> [PiTyBinder]
  -> [Type]
  -> Type
  -> [Type]
  -> Type
  -> [CoreExpr]
  -> Maybe CoreExpr
buildSpecialisedCall cenv instEnvs fun invisBndrs declDomains rho0 actualDomains expectedRes valExprs = do
  let (_, _, declRes) = splitFunTys rho0
      namedTvs = [tv | Named (Bndr tv _) <- invisBndrs]
      initSubst =
        foldl
          ( \s tv ->
              let ki = TySubst.substTy s (tyVarKind tv)
               in if ki `tcEqType` runtimeRepTy
                    then TySubst.extendTvSubstAndInScope s tv liftedRepTy
                    else if ki `tcEqType` levityTy
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

runCoreIOStringBatch
  :: PluginState
  -> CachedObsEnv
  -> SrcSpan
  -> Bool
  -> [CoreExpr]
  -> TcM (Maybe [String])
runCoreIOStringBatch _ _ _ _ [] = pure (Just [])
runCoreIOStringBatch st cenv locSpan recordSideEffects ioExprs = do
  hscEnv0 <- getTopEnv
  case hsc_interp hscEnv0 of
    Nothing -> pure Nothing
    Just _ -> do
      let hscEnv = hscEnv0 {hsc_dflags = gopt_unset (hsc_dflags hscEnv0) Opt_OmitYields}
          interp = hscInterp hscEnv
      ioStrExpr <- chainSepIO cenv "\x1e" ioExprs
      gblEnv <- getGblEnv
      locals <- collectLocalDefinitions st gblEnv ioStrExpr
      let (localNames, expr1) = inlineLocalLetRec locals ioStrExpr
      fullExpr <- resolveFreeLocalDicts cenv expr1
      let localAlgTcs =
            [ tc
            | tc <- tcg_tcs gblEnv
            , isBoxedDataTyCon tc && not (isTypeDataTyCon tc)
            ]
      when (recordSideEffects && not (null localNames)) $
        updTcRef (tcg_source_check gblEnv) $ \s ->
          s { scs_evaluated_uses = extendNameSetList (scs_evaluated_uses s) localNames }
      itblTag <- newUnique
      compiled <- tryAllM $ liftIO $ do
        (itblLinks, itblPkgs) <-
          if null localAlgTcs
            then pure ([], emptyUDFM)
            else loadLocalDataConItbls interp hscEnv locSpan itblTag localAlgTcs
        (hval, links, pkgs) <- hscCompileCoreExpr hscEnv locSpan fullExpr
        pure (hval, itblLinks ++ links, plusUDFM itblPkgs pkgs)
      case compiled of
        Left _ -> pure Nothing
        Right (hval, links, pkgs) -> do
          when recordSideEffects $
            recordThNeededRuntimeDeps links pkgs
          outcome <- tryAllM $ liftIO (evalString interp hval)
          pure $ case outcome of
            Left _ -> Nothing
            Right s -> Just (splitOnChar '\x1e' s)

loadLocalDataConItbls
  :: Interp
  -> HscEnv
  -> SrcSpan
  -> Unique
  -> [TyCon]
  -> IO ([LinkableUsage], PkgsLoaded)
loadLocalDataConItbls interp hscEnv locSpan uniq tycons = do
  initLoaderState interp hscEnv
  pls <- getLoaderState interp
  let bcoSt = maybe emptyBytecodeLoaderState bco_loader_state pls
      missingTyCons =
        [ tc
        | tc <- tycons
        , any (\dc -> isNothing (lookupInfoTableBytecodeState bcoSt (dataConName dc))) (tyConDataCons tc)
        ]
  if null missingTyCons
    then pure ([], emptyUDFM)
    else do
      let itblMod = mkInteractiveModule ("ObsEqItbls_" ++ show uniq)
      bcos <- byteCodeGen hscEnv itblMod [] missingTyCons Nothing [] Strict.Nothing
      bcoTime <- getCurrentTime
      mbc <- ByteCode.mkModuleByteCode itblMod bcos []
      loadDecls interp hscEnv locSpan (Linkable bcoTime itblMod (NE.singleton (DotGBC mbc)))

resolveFreeLocalDicts :: CachedObsEnv -> CoreExpr -> TcM CoreExpr
resolveFreeLocalDicts cenv expr = do
  let isFreeLocalDict x =
        isId x
          && isLocalVar x
          && not (isDataConWorkId x || isDataConWrapId x)
      freeLocals = exprSomeFreeVarsList isFreeLocalDict expr
  if null freeLocals
    then pure expr
    else do
      instEnvs <- tcGetInstEnvs
      pairs <- fmap catMaybes $ forM freeLocals $ \v -> do
        zTy <- liftZonkM (zonkTcType (idType v))
        pure $ case resolveClassDict cenv emptyTypeMap instEnvs zTy of
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

collectLocalDefinitions :: PluginState -> TcGblEnv -> CoreExpr -> TcM (NameEnv (Id, CoreExpr))
collectLocalDefinitions st gblEnv expr = do
  let semMod = tcg_semantic_mod gblEnv
      needsLocal v =
        isId v
          && not (isDataConWorkId v || isDataConWrapId v)
          && (nameIsLocalOrFrom semMod (idName v) || isLocalVar v)
      localRoots = [idName v | v <- exprSomeFreeVarsList needsLocal expr]
  if null localRoots
    then pure emptyNameEnv
    else getCachedModuleDefs st gblEnv

getCachedModuleDefs :: PluginState -> TcGblEnv -> TcM (NameEnv (Id, CoreExpr))
getCachedModuleDefs st gblEnv = do
  let semMod = tcg_semantic_mod gblEnv
      baseDefs = tcg_local_open_defs gblEnv
      bindCount = length (tcg_binds gblEnv)
  mbCached <- liftIO (readIORef (psDesugarCache st))
  extraDefs <-
    case mbCached of
      Just (cachedMod, cachedCount, cachedEnv)
        | cachedMod == semMod && cachedCount == bindCount ->
            pure cachedEnv
      _ -> do
        env <- desugarFromTcBinds gblEnv
        liftIO (writeIORef (psDesugarCache st) (Just (semMod, bindCount, env)))
        pure env
  pure (baseDefs `plusNameEnv` extraDefs)

desugarFromTcBinds :: TcGblEnv -> TcM (NameEnv (Id, CoreExpr))
desugarFromTcBinds gblEnv = do
  let binds :: [LHsBind GhcTc]
      binds = tcg_binds gblEnv
      hasBinders b = not (null (collectHsBindBinders CollNoDictBinders (unLoc b)))
      relevant = filter hasBinders binds
  if null relevant
    then pure emptyNameEnv
    else do
      res <- tryAllM $ do
        (_, zonkedEvBinds, zonkedBinds, _, _, _, _) <-
          zonkTopDecls (tcg_ev_binds gblEnv) relevant [] [] [] []
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

inlineLocalLetRec
  :: NameEnv (Id, CoreExpr)
  -> CoreExpr
  -> ([Name], CoreExpr)
inlineLocalLetRec locals expr
  | isEmptyNameEnv locals = ([], expr)
  | null roots = ([], expr)
  | otherwise = (localNames, Let (Rec rewrittenBinds) (rewriteExpr expr))
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

    mkLetId :: Id -> Id
    mkLetId owner =
      mkSysLocal (occNameFS (nameOccName (idName owner))) (idUnique owner) ManyTy (idType owner)

    substPairs =
      [ (owner, Var (mkLetId owner))
      | nm <- needed
      , Just (owner, _) <- [lookupNameEnv locals nm]
      ]

    rewriteExpr :: CoreExpr -> CoreExpr
    rewriteExpr e =
      let fvs = exprSomeFreeVarsList (const True) e
          inScope = mkInScopeSet (mkVarSet (fvs ++ map fst substPairs ++ map (mkLetId . fst) substPairs))
          subst = CoreSubst.extendIdSubstList (CoreSubst.mkEmptySubst inScope) substPairs
       in CoreSubst.substExpr subst e

    localNames =
      [ idName owner
      | nm <- needed
      , Just (owner, _) <- [lookupNameEnv locals nm]
      ]

    rewrittenBinds =
      [ (mkLetId owner, rewriteExpr rhs)
      | nm <- needed
      , Just (owner, rhs) <- [lookupNameEnv locals nm]
      ]
