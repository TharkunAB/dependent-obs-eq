{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module Main (main) where

import Control.Exception ( evaluate )
import Data.Type.Equality ( (:~:) (Refl), gcastWith, sym )
import Dependent.ObsEq
  ( Gen
  , ObsConfig (..)
  , ObsGen (..)
  , ObsTree (..)
  , chooseInt
  , defaultObsConfig
  , evalObsSample
  , freshBottom
  , obsEq
  , obsEqGen
  , obsEqWith
  , runGenAt
  , withObsEq
  , withObsEqWith
  , withPartialPct
  , withTests
  , withTimeoutUs
  )

data Nat = Zero | Succ Nat
  deriving (Eq, Show)

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

-- Non-structural unfold addition (lazy-equivalent to plus on partial spines).
unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc = acc
    step (Just Zero) acc = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- Non-structural accumulator addition (total-domain equivalent to plus).
accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc = acc
    go (Succ k) acc = go k (Succ acc)

-- Non-structural fuel-free Collatz convergence on total Nats.
collatz :: Nat -> Nat
collatz Zero = Succ Zero
collatz (Succ Zero) = Succ Zero
collatz n
  | isEvenNat n = collatz (halfNat n)
  | otherwise = collatz (Succ (tripleNat n))

isEvenNat :: Nat -> Bool
isEvenNat Zero = True
isEvenNat (Succ Zero) = False
isEvenNat (Succ (Succ n)) = isEvenNat n

halfNat :: Nat -> Nat
halfNat Zero = Zero
halfNat (Succ Zero) = Zero
halfNat (Succ (Succ n)) = Succ (halfNat n)

tripleNat :: Nat -> Nat
tripleNat Zero = Zero
tripleNat (Succ n) = Succ (Succ (Succ (tripleNat n)))

-- Domain-restricted function: identity on even Ints, fails on odd Ints.
twiceHalfEven :: Int -> Int
twiceHalfEven n
  | even n = (n `quot` 2) * 2
  | otherwise = error "twiceHalfEven: odd input"

genEvenInt :: Gen Int
genEvenInt = (* 2) <$> chooseInt (-50, 50)

-- Diverging function for compile-time bytecode timeout testing.
loopNat :: Nat -> Nat
loopNat n = loopNat (Succ n)

-- Allocating diverging function for native -O2 runtime evalObsSample testing
-- (native -O2 compiles non-allocating loops without heap checks unless -fno-omit-yields is set).
spinAlloc :: Integer -> Nat
spinAlloc k
  | k < 0 = Zero
  | otherwise = spinAlloc (k + 1)

totalCfg :: ObsConfig
totalCfg = withPartialPct 0 (withTests 80 defaultObsConfig)

-- 1. Non-structural unfold proved equal to structural spec via default obsEq (including partial spines).
unfoldPlusCorrect :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusCorrect m n = obsEq

-- 2. Non-structural accumulator & Collatz proved on total Nats via obsEqWith.
accPlusCorrect :: foreach (m :: Nat) (n :: Nat) -> accPlus m n :~: plus m n
accPlusCorrect m n = obsEqWith totalCfg

collatzConverges :: foreach (n :: Nat) -> collatz n :~: Succ Zero
collatzConverges n = obsEqWith totalCfg

-- 3. Custom generator combinator obsEqGen on even Ints.
evenRoundtrip :: foreach (n :: Int) -> twiceHalfEven n :~: n
evenRoundtrip n = obsEqGen genEvenInt

-- 4. Bounded divergence agreement up to micro-timeout.
loopShiftCfg :: ObsConfig
loopShiftCfg = withTests 6 (withTimeoutUs 1500 defaultObsConfig)

loopShiftObs :: foreach (n :: Nat) -> loopNat n :~: loopNat (Succ n)
loopShiftObs n = obsEqWith loopShiftCfg

-- Length-indexed vector to test runtime transport via withObsEq and withObsEqWith.
data Vec a (n :: Nat) where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

vToList :: Vec a n -> [a]
vToList VNil = []
vToList (VCons x xs) = x : vToList xs

toUnfoldVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (unfoldPlus m n)
toUnfoldVec m n v = withObsEq @(plus m n) @(unfoldPlus m n) @(Vec Int (unfoldPlus m n)) v

fromUnfoldVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (unfoldPlus m n) -> Vec Int (plus m n)
fromUnfoldVec m n v = case sym (unfoldPlusCorrect m n) of
  Refl -> v

roundtripUnfoldVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (plus m n)
roundtripUnfoldVec m n v = fromUnfoldVec m n (toUnfoldVec m n v)

toAccVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (accPlus m n)
toAccVec m n v = gcastWith (obsEqWith totalCfg :: plus m n :~: accPlus m n) v

fromAccVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (accPlus m n) -> Vec Int (plus m n)
fromAccVec m n v = withObsEqWith totalCfg @(accPlus m n) @(plus m n) @(Vec Int (plus m n)) v

roundtripAccVec :: foreach (m :: Nat) (n :: Nat) -> Vec Int (plus m n) -> Vec Int (plus m n)
roundtripAccVec m n v = fromAccVec m n (toAccVec m n v)

runIntCheck :: Int -> IO ()
runIntCheck e =
  case evenRoundtrip e of
    Refl -> pure ()

main :: IO ()
main = do
  let two = Succ (Succ Zero)
      one = Succ Zero
      vecA :: Vec Int (Succ (Succ (Succ Zero)))
      vecA = VCons 1 (VCons 2 (VCons 3 VNil))
      vecB :: Vec Int (Succ (Succ (Succ Zero)))
      vecB = VCons 10 (VCons 20 (VCons 30 VNil))

  if vToList (roundtripUnfoldVec (Succ (Succ Zero)) (Succ Zero) vecA) /= [1, 2, 3]
    || vToList (roundtripAccVec (Succ (Succ Zero)) (Succ Zero) vecB) /= [10, 20, 30]
    then error "transportVec failed"
    else pure ()

  runIntCheck 42

  () <- case (collatzConverges two, loopShiftObs one) of
    (Refl, Refl) -> pure ()

  -- Direct library checks: ObsBottom & timeout behavior
  tBottom <- evalObsSample 5000 obsApprox 4 ([1 :: Int, runGenAt 7 1 10 freshBottom] :: [Int])
  case tBottom of
    ObsCon ":" [ObsCon "1" [], ObsCon ":" [ObsRaisedBottom _, ObsCon "[]" []]] -> pure ()
    other -> error ("unexpected partial tree: " ++ show other)

  tTimeout <- evalObsSample 1500 (\d x -> if d <= 0 then pure ObsCutoff else evaluate x >> pure (ObsCon "Zero" [])) 4 (spinAlloc 0)
  if tTimeout /= ObsTimedOut
    then error ("expected ObsTimedOut, got: " ++ show tTimeout)
    else putStrLn "dependent-obs-eq-test: OK"
