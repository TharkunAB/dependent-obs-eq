{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module Main (main, evenRoundtrip) where

import Control.Exception ( TypeError (..), evaluate, try )
import Data.List ( isInfixOf, isPrefixOf )
import Data.Type.Equality ( (:~:) (Refl) )
import GHC.Generics ( Generic )
import Dependent.ObsEq
  ( DefaultObsConfig
  , Gen
  , GuardResult (..)
  , InconclusiveReason (..)
  , ObsCmp (..)
  , ObsConfig (..)
  , ObsDomain
  , ObsEquivBy (..)
  , ObsEquivOn (..)
  , ObsGen (..)
  , ObsTree (..)
  , castEq
  , castEqOn
  , checkObsEq
  , checkObsEqBy
  , checkObsEqOn
  , compareObsTree
  , defaultObsConfig
  , domainVia
  , evalObsSample
  , forType
  , forVar
  , freshBottom
  , liftObsEqOn
  , obsEq
  , obsEqBy
  , obsEqOn
  , reflObsOn
  , runGenAt
  , runObsByLoop
  , runObsOnLoop
  , runObsTestLoop
  , setApproxDepth
  , setPartialPct
  , setTests
  , symObsOn
  , totalObsConfig
  , transObsOn
  , usingEq
  )
import Dependent.Plugin.ObsEq
  ( DischargePolicy (..)
  , PluginOpts (..)
  , parsePluginOpts
  )

import DeferredNegatives
  ( badDepthCutoff
  , badEvenCallOdd
  , badFalsePlusSwap
  , badImpossibleGuard
  , badLoopTimeout
  , badNearMissInt15
  , badNearMissNat15
  , badNearMissNat6
  , badNonSymRel
  , badParametricListRefuted
  , badRootKeyCanon
  , badStrictByPartial
  , badUnguardedSubset
  )
import DeferredRefuteOnly
  ( badExplicitUnderRefuteOnly
  , constructiveUnderRefuteOnly
  )
import Defs
  ( Nat (..)
  , RBTree (..)
  , TaggedNat (..)
  , Vec (..)
  , accPlus
  , collatz
  , deepNat12
  , emptyRB
  , eqMod2Nat
  , evenIntDomain
  , evenNatDomain
  , fromListRB
  , insertRB
  , isEvenInt
  , isEvenNat
  , isValidBST
  , leNat
  , nearMissInt15
  , nearMissNat15
  , nearMissNat6
  , plus
  , rbDomain
  , rootKey
  , sameTagPair
  , sizeRB
  , spinAlloc
  , toListRB
  , twiceHalfEven
  , twiceHalfNat
  , unfoldPlus
  , vToList
  )

-- ---------------------------------------------------------------------------
-- 1. Pillar 1: Value Witnesses & Zero-Annotation Eliminators (castEq / usingEq)
-- ---------------------------------------------------------------------------

totalCfg :: ObsConfig
totalCfg = setTests 80 totalObsConfig

-- | Default 'obsEq' verifies lazy equivalence (including partial 'ObsBottom' spines).
unfoldPlusCorrect :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusCorrect _m _n = obsEq

-- | Explicit witness call using re-exported 'DefaultObsConfig'.
explicitDefaultCfgLaw :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
explicitDefaultCfgLaw _m _n = checkObsEq DefaultObsConfig

-- | Multiple independent explicit goals in one module to exercise per-module
-- desugar caching, De Bruijn GoalVerdictCache, and batched BCO evaluation.
batchLaw1, batchLaw2 :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
batchLaw1 _m _n = obsEq
batchLaw2 _m _n = obsEq

batchLaw3 :: foreach (m :: Nat) -> accPlus m Zero :~: m
batchLaw3 _m = checkObsEq totalCfg
accPlusCorrect :: foreach (m :: Nat) (n :: Nat) -> accPlus m n :~: plus m n
accPlusCorrect _m _n = checkObsEq totalCfg

plusComm :: foreach (m :: Nat) (n :: Nat) -> plus m n :~: plus n m
plusComm _m _n = checkObsEq totalCfg

collatzConverges :: foreach (n :: Nat) -> collatz n :~: Succ Zero
collatzConverges _n = checkObsEq totalCfg

-- | Zero-annotation indexed transport via 'castEq' + 'obsEq'.
toUnfoldVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (unfoldPlus m n)
toUnfoldVec _m _n v = castEq obsEq v

fromUnfoldVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (unfoldPlus m n) -> Vec Int (plus m n)
fromUnfoldVec m n v = castEq (unfoldPlusCorrect m n) v

-- | Zero-annotation indexed transport via 'castEq' + 'checkObsEq'.
toAccVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (accPlus m n)
toAccVec _m _n v = castEq (checkObsEq totalCfg) v

-- | Scope eliminator 'usingEq'.
fromAccVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (accPlus m n) -> Vec Int (plus m n)
fromAccVec m n v = usingEq (accPlusCorrect m n) v

-- ---------------------------------------------------------------------------
-- 2. Constructive Zero-UnivCo Knuth-Bendix Proofs on Bare 'Refl'
-- ---------------------------------------------------------------------------

-- | Discharged constructively by 'Dependent.Plugin.ObsEq.Rewrite' under
-- ExplicitOnly without 'obsEq' and without BCO compilation!
kboCongSwap
  :: foreach (m :: Nat) (n :: Nat)
  -> (accPlus m n ~ plus m n)
  => Succ (accPlus m n) :~: plus (Succ m) n
kboCongSwap _m _n = Refl

-- | Unfailing KB chain: @a ~ b@ and @b ~ c@ oriented by KBO discharge @f a ~ f c@
-- on bare 'Refl'.
kboTransChain
  :: foreach (x :: Nat) (y :: Nat) (z :: Nat)
  -> (unfoldPlus x y ~ accPlus x y, plus x y ~ accPlus x y)
  => Succ (unfoldPlus x y) :~: Succ (plus x y)
kboTransChain _x _y _z = Refl

-- ---------------------------------------------------------------------------
-- 3. Pillar 3: Guarded Preconditions + forVar / forType ObsDomain Overrides
-- ---------------------------------------------------------------------------

evenRoundtrip :: foreach (n :: Int) -> (isEvenInt n ~ True) => twiceHalfEven n :~: n
evenRoundtrip n = checkObsEq (forVar n evenIntDomain totalObsConfig)

evenNatRoundtrip :: foreach (n :: Nat) -> (isEvenNat n ~ True) => twiceHalfNat n :~: n
evenNatRoundtrip n = checkObsEq (forVar n evenNatDomain totalObsConfig)

-- Same-module datatype with 'deriving Generic' + 'instance ObsGen' + local functions
-- and same-module 'ObsConfig' bindings inside 'forVar' and 'forType'.
data LocalNat = LZero | LSucc LocalNat
  deriving (Eq, Ord, Show, Generic)

instance ObsGen LocalNat

localIdNat :: LocalNat -> LocalNat
localIdNat LZero = LZero
localIdNat (LSucc n) = LSucc (localIdNat n)

localDouble :: LocalNat -> LocalNat
localDouble LZero = LZero
localDouble (LSucc n) = LSucc (LSucc (localDouble n))

localHalf :: LocalNat -> LocalNat
localHalf LZero = LZero
localHalf (LSucc LZero) = LZero
localHalf (LSucc (LSucc n)) = LSucc (localHalf n)

localIsEven :: LocalNat -> Bool
localIsEven LZero = True
localIsEven (LSucc n) = not (localIsEven n)

localEvenDom :: ObsDomain LocalNat
localEvenDom = domainVia localDouble localHalf

localCfg40 :: ObsConfig
localCfg40 = setTests 40 totalObsConfig

localComputedCfg :: ObsConfig
localComputedCfg = setTests (20 + 20) totalObsConfig

sameModGenericId :: foreach (n :: LocalNat) -> localIdNat n :~: n
sameModGenericId _n = checkObsEq totalObsConfig

sameModForVarCfg :: foreach (n :: LocalNat) -> (localIsEven n ~ True) => localDouble (localHalf n) :~: n
sameModForVarCfg n = checkObsEq (forVar n localEvenDom localCfg40)

sameModForTypeCfg :: foreach (n :: LocalNat) -> (localIsEven n ~ True) => localDouble (localHalf n) :~: n
sameModForTypeCfg _n = checkObsEq (forType localEvenDom localCfg40)

sameModForVarComputedCfg :: foreach (n :: LocalNat) -> (localIsEven n ~ True) => localDouble (localHalf n) :~: n
sameModForVarComputedCfg n = checkObsEq (forVar n localEvenDom localComputedCfg)

validEmptyBST :: foreach (t :: RBTree Nat) -> (t ~ E) => isValidBST t :~: True
validEmptyBST _t = checkObsEq totalObsConfig

runRBSuite :: Nat -> Nat -> IO ()
runRBSuite x y =
  case validEmptyBST E of
    Refl -> do
      () <- case projectEq (insertComm x y E) of Refl -> pure ()
      () <- case sizeInsertComm x y E of Refl -> pure ()
      let AscTag tagVal = castProjectedTag x y E (AscTag 99)
      assert "castEqOn preserves payload" (tagVal == 99)

-- ---------------------------------------------------------------------------
-- 4. Pillar 2: Sound Projections (ObsEquivOn / liftObsEqOn) & Relations (ObsEquivBy)
-- ---------------------------------------------------------------------------

insertPreservesBST
  :: foreach (x :: Nat) (t :: RBTree Nat)
  -> (isValidBST t ~ True)
  => isValidBST (insertRB x t) :~: True
insertPreservesBST _x t = checkObsEq (forVar t rbDomain (setTests 60 totalObsConfig))

sizeCanon
  :: foreach (t :: RBTree Nat)
  -> (isValidBST t ~ True)
  => sizeRB (fromListRB (toListRB t)) :~: sizeRB t
sizeCanon t = checkObsEq (forVar t rbDomain (setTests 60 totalObsConfig))

-- | Commutativity of BST insertion up to 'toListRB' using 'forType'.
insertComm
  :: foreach (x :: Nat) (y :: Nat) (t :: RBTree Nat)
  -> (isValidBST t ~ True)
  => ObsEquivOn toListRB (insertRB x (insertRB y t)) (insertRB y (insertRB x t))
insertComm _x _y _t = checkObsEqOn (forType rbDomain (setTests 60 totalObsConfig)) toListRB

-- | Lazy default 'obsEqOn' on structural parity projection.
unfoldIdObsOn
  :: foreach (m :: Nat) (n :: Nat)
  -> ObsEquivOn isEvenNat (unfoldPlus m n) (plus m n)
unfoldIdObsOn _m _n = obsEqOn isEvenNat

reflParityZero :: ObsEquivOn isEvenNat Zero Zero
reflParityZero = reflObsOn

-- | Quotient lifting via 'liftObsEqOn': lifts 'insertComm' through 'sizeRB'
-- using verified canonicalization witnesses without forging @t1 :~: t2@!
sizeInsertComm
  :: foreach (x :: Nat) (y :: Nat) (t :: RBTree Nat)
  -> (isValidBST t ~ True)
  => sizeRB (insertRB x (insertRB y t)) :~: sizeRB (insertRB y (insertRB x t))
sizeInsertComm x y t =
  case insertPreservesBST y t of
    Refl -> case insertPreservesBST x (insertRB y t) of
      Refl -> case insertPreservesBST x t of
        Refl -> case insertPreservesBST y (insertRB x t) of
          Refl ->
            liftObsEqOn
              fromListRB
              sizeRB
              (sizeCanon (insertRB x (insertRB y t)))
              (sizeCanon (insertRB y (insertRB x t)))
              (insertComm x y t)

newtype AscTag (xs :: [Nat]) = AscTag Int

castProjectedTag
  :: foreach (x :: Nat) (y :: Nat) (t :: RBTree Nat)
  -> (isValidBST t ~ True)
  => AscTag (toListRB (insertRB x (insertRB y t)))
  -> AscTag (toListRB (insertRB y (insertRB x t)))
castProjectedTag x y t tag =
  let eq1 = insertComm x y t
   in castEqOn (transObsOn eq1 (transObsOn (symObsOn eq1) eq1)) tag

-- | Equivalence-relation witnesses ('checkObsEqBy' and 'obsEqBy').
mod2DoubleZero :: foreach (n :: Nat) -> ObsEquivBy eqMod2Nat (plus n n) Zero
mod2DoubleZero _n = checkObsEqBy totalCfg eqMod2Nat

tagUnfoldObsBy
  :: foreach (m :: Nat) (n :: Nat)
  -> ObsEquivBy sameTagPair (MkTaggedNat True (unfoldPlus m n)) (MkTaggedNat True (plus m n))
tagUnfoldObsBy _m _n = obsEqBy sameTagPair

-- ---------------------------------------------------------------------------
-- Runtime Verification Helpers
-- ---------------------------------------------------------------------------

assert :: String -> Bool -> IO ()
assert label ok
  | ok = pure ()
  | otherwise = error ("Assertion failed: " ++ label)

assertDeferredTypeError :: String -> a -> IO ()
assertDeferredTypeError label thunk = do
  res <- try @TypeError (evaluate thunk)
  case res of
    Left (TypeError msg) ->
      assert (label ++ " non-empty message") (not (null msg))
    Right _ ->
      error ("Expected deferred TypeError for '" ++ label ++ "', but evaluation succeeded!")

oneNat :: Nat
oneNat = Succ Zero

twoNat :: Nat
twoNat = Succ (Succ Zero)

vecSampleA :: Vec Int (Succ (Succ (Succ Zero)))
vecSampleA = VCons 1 (VCons 2 (VCons 3 VNil))

vecSampleB :: Vec Int (Succ (Succ (Succ Zero)))
vecSampleB = VCons 10 (VCons 20 (VCons 30 VNil))

main :: IO ()
main = do
  -- 1. Transported vectors (castEq + obsEq / checkObsEq + usingEq)
  assert
    "roundtripUnfoldVec"
    ( vToList
        ( fromUnfoldVec
            (Succ (Succ Zero))
            (Succ Zero)
            (toUnfoldVec (Succ (Succ Zero)) (Succ Zero) vecSampleA)
        )
        == [1, 2, 3]
    )
  assert
    "roundtripAccVec"
    ( vToList
        ( fromAccVec
            (Succ (Succ Zero))
            (Succ Zero)
            (toAccVec (Succ (Succ Zero)) (Succ Zero) vecSampleB)
        )
        == [10, 20, 30]
    )

  -- 1b. Batched BCO & GoalVerdictCache witnesses
  () <- case (batchLaw1 twoNat oneNat, batchLaw2 oneNat twoNat, batchLaw3 twoNat) of
    (Refl, Refl, Refl) -> pure ()
  () <- case explicitDefaultCfgLaw twoNat oneNat of Refl -> pure ()

  -- 2. Collatz, guarded evenRoundtrip, and same-module Generic/forVar/forType regressions
  () <- case collatzConverges twoNat of Refl -> pure ()
  () <- case evenNatRoundtrip (Succ (Succ Zero)) of Refl -> pure ()
  let twoLocal = LSucc (LSucc LZero)
  () <- case sameModGenericId twoLocal of Refl -> pure ()
  () <- case sameModForVarCfg twoLocal of Refl -> pure ()
  () <- case sameModForTypeCfg twoLocal of Refl -> pure ()
  () <- case sameModForVarComputedCfg twoLocal of Refl -> pure ()

  -- 3. Constructive KBO proofs (both ExplicitOnly and RefuteOnly!)
  () <- case accPlusCorrect twoNat oneNat of
    Refl -> case kboCongSwap twoNat oneNat of Refl -> pure ()
  () <- case plusComm twoNat oneNat of
    Refl -> case constructiveUnderRefuteOnly twoNat oneNat of Refl -> pure ()
  () <- case (unfoldPlusCorrect twoNat oneNat, accPlusCorrect twoNat oneNat) of
    (Refl, Refl) -> case kboTransChain twoNat oneNat Zero of Refl -> pure ()

  -- 4. Colored BST ObsEquivOn, castEqOn, and liftObsEqOn
  assert
    "distinct internal rootKeys"
    ( rootKey (insertRB oneNat (insertRB twoNat emptyRB))
        /= rootKey (insertRB twoNat (insertRB oneNat emptyRB))
        && toListRB (insertRB oneNat (insertRB twoNat emptyRB))
          == toListRB (insertRB twoNat (insertRB oneNat emptyRB))
        && sizeRB (insertRB twoNat (insertRB oneNat emptyRB)) == twoNat
    )
  () <- case projectEq (unfoldIdObsOn twoNat oneNat) of Refl -> pure ()
  () <- case projectEq reflParityZero of Refl -> pure ()
  runRBSuite twoNat oneNat

  -- 5. Equivalence relation ObsEquivBy
  () <- case relEqTrue (mod2DoubleZero twoNat) of Refl -> pure ()
  () <- case relEqTrue (tagUnfoldObsBy twoNat oneNat) of Refl -> pure ()

  -- 6. Compile-time negative tests (via -fdefer-type-errors) MUST all raise TypeError!
  assertDeferredTypeError "badRootKeyCanon" badRootKeyCanon
  assertDeferredTypeError "badEvenCallOdd" badEvenCallOdd
  assertDeferredTypeError "badUnguardedSubset" (badUnguardedSubset 1)
  assertDeferredTypeError "badNonSymRel" badNonSymRel
  assertDeferredTypeError "badStrictByPartial" badStrictByPartial
  assertDeferredTypeError "badLoopTimeout" badLoopTimeout
  assertDeferredTypeError "badDepthCutoff" badDepthCutoff
  assertDeferredTypeError "badImpossibleGuard" badImpossibleGuard
  assertDeferredTypeError "badParametricListRefuted" badParametricListRefuted
  assertDeferredTypeError "badFalsePlusSwap" badFalsePlusSwap
  assertDeferredTypeError "badNearMissNat6" badNearMissNat6
  assertDeferredTypeError "badNearMissNat15" badNearMissNat15
  assertDeferredTypeError "badNearMissInt15" (badNearMissInt15 0)
  assertDeferredTypeError "badExplicitUnderRefuteOnly" badExplicitUnderRefuteOnly

  -- 6b. Verify near-miss laws are genuinely REFUTED ("FAIL:") with counterexamples, not Inconclusive
  nat6Out <-
    runObsTestLoop
      totalObsConfig
      Nothing
      (const (pure GuardHolds))
      obsGenPartial
      obsShrink
      (\n -> "n = " ++ obsShow n)
      obsApprox
      nearMissNat6
      id
  assert ("nearMissNat6 refuted, got: " ++ nat6Out) ("FAIL:" `isPrefixOf` nat6Out)

  nat15Out <-
    runObsTestLoop
      totalObsConfig
      Nothing
      (const (pure GuardHolds))
      obsGenPartial
      obsShrink
      (\n -> "n = " ++ obsShow n)
      obsApprox
      nearMissNat15
      id
  assert ("nearMissNat15 refuted, got: " ++ nat15Out) ("FAIL:" `isPrefixOf` nat15Out)

  int15Out <-
    runObsTestLoop
      totalObsConfig
      Nothing
      (const (pure GuardHolds))
      obsGenPartial
      obsShrink
      (\n -> "n = " ++ obsShow n)
      obsApprox
      nearMissInt15
      id
  assert
    ("nearMissInt15 refuted and shrunk to +-15, got: " ++ int15Out)
    ("FAIL:" `isPrefixOf` int15Out && ("n = 15 " `isInfixOf` int15Out || "n = -15 " `isInfixOf` int15Out))

  -- 7. Direct runtime verification of Kleene lattice, coupled shrinking, and diagnostics
  assert
    "compareObsTree Kleene lattice"
    ( compareObsTree 8 1500 ObsCutoff ObsCutoff == ObsUnknown (DepthCutoffReached 8)
        && compareObsTree 8 1500 ObsTimedOut ObsTimedOut == ObsUnknown (TimeoutReached 1500)
        && compareObsTree 8 1500 ObsRaisedSyncError ObsRaisedSyncError == ObsUnknown SyncExceptionRaised
        && compareObsTree 8 1500 (ObsRaisedBottom 7) (ObsRaisedBottom 7) == ObsEqual
        && compareObsTree 8 1500 (ObsRaisedBottom 7) (ObsRaisedBottom 8) == ObsApart
        && compareObsTree 8 1500 (ObsCon "(,)" [ObsCon "Zero" [], ObsCutoff]) (ObsCon "(,)" [ObsCon "Succ" [ObsCutoff], ObsCutoff]) == ObsApart
    )

  -- Coupled 4x4 diagonal shrinking: guard x == y with failure at x >= 2 && y >= 2
  -- Axis-only shrinks break x == y; 4x4 diagonal shrinks (10, 10) down to (2, 2)!
  coupledOut <-
    runObsTestLoop
      (setTests 60 totalObsConfig)
      Nothing
      (\(x, y) -> pure (if x == y then GuardHolds else GuardFails))
      (\_ -> (\k -> (k, k)) <$> obsGen)
      (\(x, y) ->
        let xs = obsShrink (x :: Int)
            ys = obsShrink (y :: Int)
         in [(x', y) | x' <- xs]
              ++ [(x, y') | y' <- ys]
              ++ [(x', y') | x' <- take 4 xs, y' <- take 4 ys]
      )
      (\(x, y) -> "x = " ++ show x ++ ", y = " ++ show y)
      obsApprox
      (\(x, y) -> x >= 2 && y >= 2)
      (const False)
  assert
    ("coupled shrink reaches (2, 2), got: " ++ coupledOut)
    ("x = 2, y = 2" `isInfixOf` coupledOut)

  -- InsufficientPreconditionHits when guard never holds
  insuffOut <-
    runObsTestLoop
      (setTests 5 totalObsConfig)
      Nothing
      (const (pure GuardFails))
      (\_ -> obsGen :: Gen Int)
      obsShrink
      show
      obsApprox
      id
      id
  assert
    ("insufficient precondition hits, got: " ++ insuffOut)
    (insuffOut == "INCONCLUSIVE:InsufficientPreconditionHits 0 5")

  -- Depth cutoff in runObsTestLoop
  cutoffOut <-
    runObsTestLoop
      (setTests 4 (setApproxDepth 8 totalObsConfig))
      Nothing
      (const (pure GuardHolds))
      (\_ -> pure Zero)
      (const [])
      show
      (\d n ->
        let walk 0 _ = pure ObsCutoff
            walk _ Zero = pure (ObsCon "Zero" [])
            walk k (Succ m) = (\t -> ObsCon "Succ" [t]) <$> walk (k - 1) m
         in walk d n
      )
      deepNat12
      (deepNat12 . Succ)
  assert
    ("depth cutoff inconclusive, got: " ++ cutoffOut)
    (cutoffOut == "INCONCLUSIVE:DepthCutoffReached 8")

  -- Projection counterexample format ("proj lhs = ..., proj rhs = ...")
  projFailOut <-
    runObsOnLoop
      (setTests 20 totalObsConfig)
      Nothing
      (const (pure GuardHolds))
      (\_ -> obsGen)
      obsShrink
      (\n -> "n = " ++ show n)
      obsApprox
      (`mod` (2 :: Int))
      id
      (+ 1)
  assert
    ("proj counterexample diagnostic, got: " ++ projFailOut)
    ("FAIL:" `isPrefixOf` projFailOut && "proj lhs =" `isInfixOf` projFailOut)

  -- Relation symmetry failure format ("failed symmetry")
  bySymOut <-
    runObsByLoop
      (setTests 10 totalObsConfig)
      Nothing
      (const (pure GuardHolds))
      (\_ -> pure Zero)
      (const [])
      (\n -> "n = " ++ show n)
      "leNat"
      leNat
      (const Zero)
      Succ
  assert
    ("by symmetry diagnostic, got: " ++ bySymOut)
    ("FAIL:relation 'leNat' failed symmetry" `isPrefixOf` bySymOut)

  -- Partial demand probe & native timeout checks
  tBottom <- evalObsSample 5000 obsApprox 4 ([1 :: Int, runGenAt 7 1 10 freshBottom] :: [Int])
  case tBottom of
    ObsCon ":" [ObsCon "1" [], ObsCon ":" [ObsRaisedBottom _, ObsCon "[]" []]] -> pure ()
    other -> error ("unexpected partial tree: " ++ show other)

  tTimeout <-
    evalObsSample
      1500
      (\d x -> if d <= 0 then pure ObsCutoff else evaluate x >> pure (ObsCon "Zero" []))
      4
      (spinAlloc 0)
  assert ("expected ObsTimedOut, got: " ++ show tTimeout) (tTimeout == ObsTimedOut)

  -- Plugin CLI option parser check (including policy=refute-only and default depth 100)
  assert
    "parsePluginOpts policy=refute-only"
    ( parsePluginOpts ["policy=refute-only,tests=42"]
        == Right
          PluginOpts
            { poConfig = (setTests 42 defaultObsConfig)
            , poPolicy = RefuteOnly
            , poWarnAssume = False
            }
        && obsApproxDepth defaultObsConfig == 100
        && obsPartialPct (setPartialPct 0 defaultObsConfig) == obsPartialPct totalObsConfig
    )

  putStrLn "dependent-obs-eq-test: OK"
