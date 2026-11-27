{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module DeferredNegatives (
    badRootKeyCanon,
    badEvenCallOdd,
    badUnguardedSubset,
    badNonSymRel,
    badStrictByPartial,
    badLoopTimeout,
    badDepthCutoff,
    badImpossibleGuard,
    badParametricListRefuted,
    badFalsePlusSwap,
    badNearMissNat6,
    badNearMissNat15,
    badNearMissInt15,
) where

import Data.Type.Equality ((:~:) (Refl))
import Defs (
    Nat (..),
    RBTree (..),
    deepNat12,
    eqMod2Nat,
    evenIntDomain,
    evenNatDomain,
    fromListRB,
    isEvenInt,
    isEvenNat,
    isValidBST,
    leNat,
    loopNat,
    nearMissInt15,
    nearMissNat15,
    nearMissNat6,
    plus,
    rbDomain,
    rootKey,
    toListRB,
    twiceHalfNat,
    unfoldPlus,
 )
import Dependent.ObsEq (
    ObsEquivBy (..),
    checkObsEq,
    checkObsEqBy,
    defaultObsConfig,
    forVar,
    obsEqBy,
    setApproxDepth,
    setTests,
    setTimeoutUs,
    totalObsConfig,
 )

-- 1. Non-respectful observer 'rootKey' fails canonicalization even on valid BSTs.
badRootKeyProof ::
    foreach (t :: RBTree Nat) ->
    (isValidBST t ~ True) =>
    rootKey (fromListRB (toListRB t)) :~: rootKey t
badRootKeyProof t = checkObsEq (forVar t rbDomain (setTests 40 totalObsConfig))

badRootKeyCanon :: rootKey (fromListRB (toListRB E)) :~: rootKey E
badRootKeyCanon = badRootKeyProof E

-- 2. Guarded law rejects invalid odd call site statically (False ~ True)!
guardedEvenNatLaw :: foreach (n :: Nat) -> (isEvenNat n ~ True) => twiceHalfNat n :~: n
guardedEvenNatLaw n = checkObsEq (forVar n evenNatDomain totalObsConfig)

badEvenCallOdd :: twiceHalfNat (Succ Zero) :~: Succ Zero
badEvenCallOdd = guardedEvenNatLaw (Succ Zero)

-- 3. Unguarded subset override on Int is caught by baseline boundary sweep!
badUnguardedEven :: foreach (n :: Int) -> isEvenInt n :~: True
badUnguardedEven n = checkObsEq (forVar n evenIntDomain (setTests 25 totalObsConfig))

badUnguardedSubset :: Int -> ()
badUnguardedSubset n = case badUnguardedEven n of Refl -> ()

-- 4. Non-symmetric relation 'leNat' is rejected by checkObsEqBy symmetry check!
badLeSymProof :: foreach (n :: Nat) -> ObsEquivBy leNat Zero (Succ n)
badLeSymProof _n = checkObsEqBy (setTests 20 totalObsConfig) leNat

badNonSymRel :: ObsEquivBy leNat Zero (Succ Zero)
badNonSymRel = badLeSymProof Zero

-- 4b. Strict relation 'eqMod2Nat' under default partial config is refuted cleanly
-- (with safe shrinking over ObsBottom inputs)!
badPartialMod2Proof :: foreach (m :: Nat) (n :: Nat) -> ObsEquivBy eqMod2Nat (unfoldPlus m n) (plus m n)
badPartialMod2Proof _m _n = obsEqBy eqMod2Nat

badStrictByPartial :: ()
badStrictByPartial = case relEqTrue (badPartialMod2Proof Zero Zero) of Refl -> ()

-- 5. Diverging loop hits per-sample timeout -> Inconclusive (left unsolved!).
badLoopProof :: foreach (n :: Nat) -> loopNat n :~: loopNat (Succ n)
badLoopProof _n = checkObsEq (setTests 3 (setTimeoutUs 1500 defaultObsConfig))

badLoopTimeout :: ()
badLoopTimeout = case badLoopProof Zero of Refl -> ()

-- 6. Deep finite term hits approximation depth cutoff -> Inconclusive (left unsolved!).
badCutoffProof :: deepNat12 Zero :~: deepNat12 (Succ Zero)
badCutoffProof = checkObsEq (setTests 4 (setApproxDepth 8 totalObsConfig))

badDepthCutoff :: deepNat12 Zero :~: deepNat12 (Succ Zero)
badDepthCutoff = badCutoffProof

-- 7. Unsatisfiable Given guard (2*n ~ 1) hits InsufficientPreconditionHits -> Inconclusive!
badInsuffProof ::
    foreach (n :: Nat) ->
    (plus n n ~ Succ Zero) =>
    unfoldPlus n Zero :~: n
badInsuffProof _n = checkObsEq (setTests 6 totalObsConfig)

badImpossibleGuard :: ()
badImpossibleGuard = case badInsuffProof Zero of Refl -> ()

-- 8. Unconstrained parametric polymorphism specializes to @Ordering and refutes!
badParametricConsProof :: forall a. foreach (x :: a) (xs :: [a]) -> (x : xs) :~: xs
badParametricConsProof _x _xs = checkObsEq (setTests 20 totalObsConfig)

badParametricListRefuted :: (Zero : '[]) :~: ('[] :: [Nat])
badParametricListRefuted = badParametricConsProof Zero []

-- 9. False bare nominal equality on Nat is refuted.
badFalsePlusProof :: foreach (m :: Nat) -> plus m (Succ Zero) :~: m
badFalsePlusProof _m = Refl

badFalsePlusSwap :: plus Zero (Succ Zero) :~: Zero
badFalsePlusSwap = badFalsePlusProof Zero

-- 10. Near-miss Peano and Int equations at depths 6 and 15 are refuted under totalObsConfig.
badNearMissNat6Proof :: foreach (n :: Nat) -> nearMissNat6 n :~: n
badNearMissNat6Proof _n = checkObsEq totalObsConfig

badNearMissNat6 :: nearMissNat6 Zero :~: Zero
badNearMissNat6 = badNearMissNat6Proof Zero

badNearMissNat15Proof :: foreach (n :: Nat) -> nearMissNat15 n :~: n
badNearMissNat15Proof _n = checkObsEq totalObsConfig

badNearMissNat15 :: nearMissNat15 Zero :~: Zero
badNearMissNat15 = badNearMissNat15Proof Zero

badNearMissInt15Proof :: foreach (n :: Int) -> nearMissInt15 n :~: n
badNearMissInt15Proof _n = checkObsEq totalObsConfig

badNearMissInt15 :: Int -> ()
badNearMissInt15 n = case badNearMissInt15Proof n of Refl -> ()
