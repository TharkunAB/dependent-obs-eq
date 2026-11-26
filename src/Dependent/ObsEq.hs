{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE ListTuplePuns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Dependent.ObsEq
-- Description : Explicit observational-equivalence combinators and generators
-- License     : BSD-3-Clause
-- Maintainer  : mpg@mpg.is
--
-- User-facing combinators, configuration, deterministic value generators,
-- shrinking, and bounded Kleene approximation trees for observational
-- type-equality testing under @-fplugin=Dependent.Plugin.ObsEq@.
--
-- Credit: Based on the observational-equivalence / QuickCheck @TcPlugin@ idea
-- proposed by Jules (\@analytichegel).
module Dependent.ObsEq
  ( -- * Observational equality witnesses
    ObsEq (..)
  , obsEq
  , withObsEq
  , ObsEqWith (..)
  , obsEqWith
  , withObsEqWith
  , ObsEqGen (..)
  , obsEqGen
  , withObsEqGen

    -- * Configuration
  , ObsConfig (..)
  , defaultObsConfig
  , withTests
  , withMaxSize
  , withApproxDepth
  , withPartialPct
  , withTimeoutUs
  , withSeed

    -- * Deterministic PRNG and generators
  , Seed (..)
  , mkSeed
  , stepSeed
  , splitSeed
  , Gen (..)
  , runGenAt
  , sized
  , resize
  , chooseWord64
  , chooseInt
  , chooseInteger
  , elements
  , oneof
  , frequency
  , listOf

    -- * Partial inputs and bounded observation
  , ObsBottom (..)
  , obsBottom
  , freshBottom
  , mixPartial
  , ObsTree (..)
  , InconclusiveReason (..)
  , ObsCmp (..)
  , ObsVerdict (..)
  , compareObsTree
  , evalObsSample
  , renderObsTree
  , ObsGen (..)

    -- * Plugin runtime harness helpers
  , AdtObsDict (..)
  , adtGen
  , adtGenPartial
  , adtShrink
  , adtApprox
  , adtShow
  , mkAdtObsDict
  , evalObsVerdict
  , renderInconclusiveReason
  , runObsTestLoop
  , obsPureGen
  , obsApGen
  , obsPureIO
  , obsBindIO
  , obsAppendStr
  , obsAppendList
  , obsPairGen
  , obsPairShrink
  , obsPairShow
  , obsNamedShow
  , obsSplitPairGen
  , obsSplitTripleGen
  ) where

import Control.Exception
  ( AllocationLimitExceeded (..)
  , Exception (..)
  , SomeAsyncException
  , SomeException
  , bracket
  , catch
  , evaluate
  , throw
  , throwIO
  )
import Data.Bits ( shiftR, xor, (.&.) )
import Data.Char ( chr, ord )
import Data.Type.Equality ( (:~:) (Refl) )
import Data.Word ( Word64 )
import GHC.Generics
  ( C
  , Constructor
  , D
  , Generic (..)
  , K1 (..)
  , M1 (..)
  , U1 (..)
  , conName
  , (:*:) (..)
  , (:+:) (..)
  )
import Numeric.Natural ( Natural )
import qualified System.IO.Unsafe
import System.Mem
  ( disableAllocationLimit
  , enableAllocationLimit
  , getAllocationCounter
  , setAllocationCounter
  )
import System.Timeout ( timeout )

{- Note [Observational equivalence combinators]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Credit: Jules (@analytichegel) proposed using a randomized property-testing
`TcPlugin` to test and discharge observational type equalities on open terms in
Dependent Haskell.

`Dependent.ObsEq` separates explicit observational evidence from structural
definitional equality:

1. `obsEq` requests a proof of `lhs :~: rhs` using module/CLI plugin settings.
2. `obsEqWith` supplies a per-call `ObsConfig` via visible dependent
   quantification.
3. `obsEqGen` supplies a custom top-level `Gen` value (or tuple of `Gen` values
   matching the free domain variables left-to-right) for domain-restricted laws.

When `-fplugin=Dependent.Plugin.ObsEq` is active, the solver plugin runs
bounded Kleene approximation tests (`evalObsSample`) over both total and
partial (`ObsBottom`) inputs before constructing dictionary evidence.
-}

-- | Configuration for bounded observational-equivalence testing.
data ObsConfig = ObsConfig
  { obsTests :: Natural
  -- ^ Number of test samples to run (default: @100@).
  , obsMaxSize :: Natural
  -- ^ Maximum generator size parameter (default: @20@).
  , obsApproxDepth :: Natural
  -- ^ Maximum constructor-tree approximation depth (default: @100@).
  , obsPartialPct :: Natural
  -- ^ Percentage @[0..100]@ of samples that inject 'ObsBottom' thunks (default: @25@).
  , obsTimeoutUs :: Natural
  -- ^ Per-side evaluation timeout in microseconds (default: @10000@).
  , obsSeed :: Natural
  -- ^ Deterministic starting PRNG seed (default: @0@).
  }
  deriving (Eq, Ord, Show)

-- | Default observational-equivalence test parameters.
defaultObsConfig :: ObsConfig
defaultObsConfig =
  ObsConfig
    { obsTests = 100
    , obsMaxSize = 20
    , obsApproxDepth = 100
    , obsPartialPct = 25
    , obsTimeoutUs = 10000
    , obsSeed = 0
    }

-- | Set 'obsTests' on an 'ObsConfig'.
withTests :: Natural -> ObsConfig -> ObsConfig
withTests n cfg = cfg {obsTests = n}

-- | Set 'obsMaxSize' on an 'ObsConfig'.
withMaxSize :: Natural -> ObsConfig -> ObsConfig
withMaxSize n cfg = cfg {obsMaxSize = n}

-- | Set 'obsApproxDepth' on an 'ObsConfig'.
withApproxDepth :: Natural -> ObsConfig -> ObsConfig
withApproxDepth n cfg = cfg {obsApproxDepth = n}

-- | Set 'obsPartialPct' on an 'ObsConfig'.
withPartialPct :: Natural -> ObsConfig -> ObsConfig
withPartialPct n cfg = cfg {obsPartialPct = n}

-- | Set 'obsTimeoutUs' on an 'ObsConfig'.
withTimeoutUs :: Natural -> ObsConfig -> ObsConfig
withTimeoutUs n cfg = cfg {obsTimeoutUs = n}

-- | Set 'obsSeed' on an 'ObsConfig'.
withSeed :: Natural -> ObsConfig -> ObsConfig
withSeed n cfg = cfg {obsSeed = n}

-- | Explicit observational-equivalence constraint discharged by
-- @Dependent.Plugin.ObsEq@.
class ObsEq (lhs :: k) (rhs :: k) where
  -- | Witness method supplied by @Dependent.Plugin.ObsEq@.
  obsEqProof :: lhs :~: rhs

-- | Obtain a propositional equality witness @lhs :~: rhs@ by observational
-- testing under the active plugin configuration.
obsEq :: forall {k} (lhs :: k) (rhs :: k). ObsEq lhs rhs => lhs :~: rhs
obsEq = obsEqProof

-- | Bring the nominal equality @lhs ~ rhs@ into scope for a continuation @r@
-- after observational verification.
withObsEq :: forall {k} (lhs :: k) (rhs :: k) r. ObsEq lhs rhs => ((lhs ~ rhs) => r) -> r
withObsEq k = case obsEqProof @k @lhs @rhs of
  Refl -> k

-- | Explicit observational-equivalence constraint parameterized by a call-site
-- 'ObsConfig'.
class ObsEqWith (cfg :: ObsConfig) (lhs :: k) (rhs :: k) where
  -- | Witness method supplied by @Dependent.Plugin.ObsEq@.
  obsEqWithProof :: lhs :~: rhs

-- | Obtain a propositional equality witness @lhs :~: rhs@ using @cfg@.
obsEqWith :: forall {k}. forall (cfg :: ObsConfig) -> forall (lhs :: k) (rhs :: k). ObsEqWith cfg lhs rhs => lhs :~: rhs
obsEqWith (type cfg) @lhs @rhs = obsEqWithProof @k @cfg @lhs @rhs

-- | Bring @lhs ~ rhs@ into scope using @cfg@.
withObsEqWith :: forall {k}. forall (cfg :: ObsConfig) -> forall (lhs :: k) (rhs :: k) r. ObsEqWith cfg lhs rhs => ((lhs ~ rhs) => r) -> r
withObsEqWith (type cfg) @lhs @rhs cont = case obsEqWithProof @k @cfg @lhs @rhs of
  Refl -> cont

-- | Explicit observational-equivalence constraint parameterized by a custom
-- generator binding @gen@.
class ObsEqGen (gen :: ga) (lhs :: k) (rhs :: k) where
  -- | Witness method supplied by @Dependent.Plugin.ObsEq@.
  obsEqGenProof :: lhs :~: rhs

-- | Obtain @lhs :~: rhs@ by testing over inputs drawn from @gen@.
obsEqGen :: forall {ga} {k}. forall (gen :: ga) -> forall (lhs :: k) (rhs :: k). ObsEqGen gen lhs rhs => lhs :~: rhs
obsEqGen (type gen) @lhs @rhs = obsEqGenProof @ga @k @gen @lhs @rhs

-- | Bring @lhs ~ rhs@ into scope by testing over inputs drawn from @gen@.
withObsEqGen :: forall {ga} {k}. forall (gen :: ga) -> forall (lhs :: k) (rhs :: k) r. ObsEqGen gen lhs rhs => ((lhs ~ rhs) => r) -> r
withObsEqGen (type gen) @lhs @rhs cont = case obsEqGenProof @ga @k @gen @lhs @rhs of
  Refl -> cont

-- | Deterministic 64-bit PRNG state.
data Seed = Seed !Word64 !Word64
  deriving (Eq, Ord, Show)

-- | Build a deterministic 'Seed' from a 64-bit integer.
mkSeed :: Word64 -> Seed
mkSeed s = Seed (mix64 (s + 0x9e3779b97f4a7c15)) 0xda3e39cb94b95bdb

mix64 :: Word64 -> Word64
mix64 z0 =
  let z1 = (z0 `xor` (z0 `shiftR` 31)) * 0x7fb5d329728ea185
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x81dadef4bc2dd44d
   in z2 `xor` (z2 `shiftR` 33)

-- | Advance the PRNG and produce one 64-bit word.
stepSeed :: Seed -> (Word64, Seed)
stepSeed (Seed st inc) =
  let st' = st * 6364136223846793005 + (inc + 1)
   in (mix64 st', Seed st' inc)

-- | Split a 'Seed' into two independent streams.
splitSeed :: Seed -> (Seed, Seed)
splitSeed s0 =
  let (w1, s1) = stepSeed s0
      (w2, s2) = stepSeed s1
   in (Seed w1 ((w2 .&. 0xfffffffffffffffe) + 1), s2)

-- | Sized deterministic value generator.
newtype Gen a = Gen {unGen :: Seed -> Int -> a}

instance Functor Gen where
  fmap f (Gen g) = Gen (\s sz -> f (g s sz))

instance Applicative Gen where
  pure x = Gen (\_ _ -> x)
  Gen gf <*> Gen gx = Gen $ \s sz ->
    let (s1, s2) = splitSeed s
     in gf s1 sz (gx s2 sz)

instance Monad Gen where
  Gen gx >>= k = Gen $ \s sz ->
    let (s1, s2) = splitSeed s
     in unGen (k (gx s1 sz)) s2 sz

-- | Evaluate a generator at an explicit seed index and size.
runGenAt :: Word64 -> Int -> Int -> Gen a -> a
runGenAt baseSeed sampleIdx sz (Gen g) =
  let s = mkSeed (baseSeed + fromIntegral sampleIdx * 0x517cc1b727220a95)
   in g s (max 0 sz)

-- | Read the active size parameter.
sized :: (Int -> Gen a) -> Gen a
sized f = Gen (\s sz -> unGen (f sz) s sz)

-- | Override the size parameter inside a sub-generator.
resize :: Int -> Gen a -> Gen a
resize sz' (Gen g) = Gen (\s _ -> g s (max 0 sz'))

-- | Draw a uniform 64-bit word in @[lo, hi]@.
chooseWord64 :: (Word64, Word64) -> Gen Word64
chooseWord64 (lo0, hi0) = Gen $ \s _ ->
  let lo = min lo0 hi0
      hi = max lo0 hi0
      (w, _) = stepSeed s
      spanW = hi - lo
   in if spanW == maxBound
        then w
        else lo + (w `rem` (spanW + 1))

-- | Draw an 'Int' in @[lo, hi]@.
chooseInt :: (Int, Int) -> Gen Int
chooseInt (lo0, hi0) = do
  let lo = fromIntegral (min lo0 hi0) :: Integer
      hi = fromIntegral (max lo0 hi0) :: Integer
  fromIntegral <$> chooseInteger (lo, hi)

-- | Draw an 'Integer' in @[lo, hi]@.
chooseInteger :: (Integer, Integer) -> Gen Integer
chooseInteger (lo0, hi0) = Gen $ \s _ ->
  let lo = min lo0 hi0
      hi = max lo0 hi0
      range = hi - lo + 1
      (w1, s1) = stepSeed s
      (w2, _) = stepSeed s1
      big = (fromIntegral w1 * (fromIntegral (maxBound :: Word64) + 1)) + fromIntegral w2
   in lo + (big `mod` range)

-- | Pick uniformly from a non-empty list.
elements :: [a] -> Gen a
elements [] = error "Dependent.ObsEq.elements: empty list"
elements xs = do
  idx <- chooseInt (0, length xs - 1)
  pure (xs !! idx)

-- | Pick uniformly from a non-empty list of generators.
oneof :: [Gen a] -> Gen a
oneof [] = error "Dependent.ObsEq.oneof: empty list"
oneof gs = do
  idx <- chooseInt (0, length gs - 1)
  gs !! idx

-- | Pick from weighted generators.
frequency :: [(Int, Gen a)] -> Gen a
frequency pairs =
  let pos = [(w, g) | (w, g) <- pairs, w > 0]
      total = sum (map fst pos)
   in if total <= 0
        then error "Dependent.ObsEq.frequency: no positive weights"
        else do
          pick <- chooseInt (1, total)
          let go _ [(_, g)] = g
              go k ((w, g) : rest)
                | k <= w = g
                | otherwise = go (k - w) rest
              go _ [] = error "Dependent.ObsEq.frequency: unreachable"
          go pick pos

-- | Generate a list whose length scales up to the active size.
listOf :: Gen a -> Gen [a]
listOf g = sized $ \sz -> do
  len <- chooseInt (0, sz)
  let build 0 = pure []
      build k = (:) <$> resize (sz `quot` 2) g <*> build (k - 1)
  build len

-- | Tagged exception used to probe demand and laziness on partial inputs.
newtype ObsBottom = ObsBottom Int
  deriving (Eq, Ord, Show)

instance Exception ObsBottom

-- | Raise a tagged observational bottom when forced.
obsBottom :: Int -> a
obsBottom tag = throw (ObsBottom tag)

-- | Generate a lazy bottom thunk with a deterministic tag derived from the PRNG.
freshBottom :: Gen a
freshBottom = Gen $ \s _ ->
  let (w, _) = stepSeed s
      tag = fromIntegral (w .&. 0x3fffffff) + 1
   in obsBottom tag

-- | Inject 'freshBottom' with probability @pct@ percent, otherwise run @g@.
mixPartial :: Int -> Gen a -> Gen a
mixPartial pct g
  | pct <= 0 = g
  | pct >= 100 = freshBottom
  | otherwise = frequency [(pct, freshBottom), (100 - pct, g)]

-- | Bounded Kleene approximation of a Haskell value.
-- See Note [Three-valued Kleene observation lattice].
data ObsTree
  = ObsCon !String ![ObsTree]
  | ObsCutoff
  | ObsRaisedBottom !Int
  | ObsRaisedSyncError
  | ObsTimedOut
  deriving (Eq, Ord, Show)

{- Note [Three-valued Kleene observation lattice]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Bounded evaluation of open terms produces constructor spines, synthetic demand
probes ('ObsRaisedBottom'), resource limits ('ObsCutoff' and 'ObsTimedOut'), or
synchronous runtime errors ('ObsRaisedSyncError').

Treating 'ObsTree' equality via derived 'Eq' is unsound:
1. 'ObsCutoff' == 'ObsCutoff' equates distinct finite values that agree up to
   'obsApproxDepth' (such as @Succ^100 Zero@ and @Succ^100 (Succ Zero)@).
2. 'ObsTimedOut' == 'ObsTimedOut' equates distinct slow or diverging terms and
   makes typechecking depend on wall-clock scheduling.
3. 'ObsRaisedSyncError' == 'ObsRaisedSyncError' equates distinct runtime
   exceptions.

Function 'compareObsTree' evaluates a strong three-valued Kleene lattice
('ObsCmp'):
* Two 'ObsCon' nodes with different constructor names or arities are
  'ObsApart'. Matching constructors combine child results with Kleene
  conjunction: any 'ObsApart' child yields 'ObsApart' immediately (for example,
  @(Zero, loop)@ vs @(Succ Zero, loop)@ is 'ObsApart' at 'fst'), else any
  'ObsUnknown' child yields 'ObsUnknown', else 'ObsEqual'.
* 'ObsRaisedBottom' carries the deterministic PRNG tag of an injected partial
  input thunk. Raising the same tag on both sides proves identical first-demand
  laziness ('ObsEqual'); raising different tags or matching a value against
  'ObsRaisedBottom' proves a strictness mismatch ('ObsApart').
* Resource limits ('ObsCutoff', 'ObsTimedOut') and double 'ObsRaisedSyncError'
  always yield 'ObsUnknown', which aggregates to 'Inconclusive' and never emits
  a nominal coercion.
-}

-- | Reason why bounded testing returned 'Inconclusive'.
-- See Note [Three-valued Kleene observation lattice].
data InconclusiveReason
  = DepthCutoffReached !Natural
  | TimeoutReached !Natural
  | SyncExceptionRaised
  | InsufficientPreconditionHits !Natural !Natural
  | PolymorphicClassConstraint !String
  deriving (Eq, Ord, Show, Read)

-- | Per-sample three-valued strong Kleene observation result.
-- See Note [Three-valued Kleene observation lattice].
data ObsCmp
  = ObsEqual
  -- ^ Both trees are finite constructor spines with identical constructors and
  -- leaves, or both raised the same injected 'ObsBottom' tag.
  | ObsApart
  -- ^ Definite mismatch at a finite constructor path or demand probe.
  | ObsUnknown !InconclusiveReason
  -- ^ At least one side hit a resource cutoff, timeout, or synchronous error,
  -- and no finite branch was 'ObsApart'.
  deriving (Eq, Show)

-- | Aggregate verdict of bounded observational testing across all samples.
data ObsVerdict env
  = Verified
  | Refuted !Int !Int !env !ObsTree !ObsTree
  | Inconclusive !InconclusiveReason
  deriving (Eq, Show)

-- | Compare two 'ObsTree' observations in the strong Kleene lattice.
-- See Note [Three-valued Kleene observation lattice].
compareObsTree :: Natural -> Natural -> ObsTree -> ObsTree -> ObsCmp
compareObsTree depth timeoutUs t1 t2 =
  case (t1, t2) of
    (ObsCon c1 as1, ObsCon c2 as2)
      | c1 /= c2 || length as1 /= length as2 -> ObsApart
      | otherwise -> foldKleene (zipWith (compareObsTree depth timeoutUs) as1 as2)
    (ObsRaisedBottom b1, ObsRaisedBottom b2)
      | b1 == b2 -> ObsEqual
      | otherwise -> ObsApart
    (ObsCon _ _, ObsRaisedBottom _) -> ObsApart
    (ObsRaisedBottom _, ObsCon _ _) -> ObsApart
    (ObsCon _ _, ObsRaisedSyncError) -> ObsApart
    (ObsRaisedSyncError, ObsCon _ _) -> ObsApart
    (ObsRaisedBottom _, ObsRaisedSyncError) -> ObsApart
    (ObsRaisedSyncError, ObsRaisedBottom _) -> ObsApart
    (ObsTimedOut, _) -> ObsUnknown (TimeoutReached timeoutUs)
    (_, ObsTimedOut) -> ObsUnknown (TimeoutReached timeoutUs)
    (ObsCutoff, _) -> ObsUnknown (DepthCutoffReached depth)
    (_, ObsCutoff) -> ObsUnknown (DepthCutoffReached depth)
    (ObsRaisedSyncError, ObsRaisedSyncError) -> ObsUnknown SyncExceptionRaised
  where
    foldKleene :: [ObsCmp] -> ObsCmp
    foldKleene [] = ObsEqual
    foldKleene (ObsApart : _) = ObsApart
    foldKleene (ObsEqual : rest) = foldKleene rest
    foldKleene (ObsUnknown r : rest) =
      case foldKleene rest of
        ObsApart -> ObsApart
        _ -> ObsUnknown r

-- | Render an 'InconclusiveReason' as an actionable diagnostic message.
renderInconclusiveReason :: InconclusiveReason -> String
renderInconclusiveReason (DepthCutoffReached d) =
  "approximation depth cutoff ("
    ++ show d
    ++ ") reached; increase setApproxDepth or project a finite prefix with obsEqOn"
renderInconclusiveReason (TimeoutReached us) =
  "per-sample timeout ("
    ++ show us
    ++ " us) or allocation limit reached; increase setTimeoutUs or restrict non-terminating inputs"
renderInconclusiveReason SyncExceptionRaised =
  "both sides raised synchronous runtime exceptions; restrict partial inputs with a Given guard and forVar/forType"
renderInconclusiveReason (InsufficientPreconditionHits passed needed) =
  "precondition guard matched only "
    ++ show passed
    ++ " of "
    ++ show needed
    ++ " required sample(s); supply a matching ObsDomain via forVar or forType"
renderInconclusiveReason (PolymorphicClassConstraint predStr) =
  "polymorphic class constraint ("
    ++ predStr
    ++ ") cannot be discharged soundly by monomorphic specialization"

-- | Render an 'ObsTree' concisely for counterexample diagnostics.
renderObsTree :: ObsTree -> String
renderObsTree (ObsCon c []) = c
renderObsTree (ObsCon c args) =
  "(" ++ c ++ concatMap ((' ' :) . renderObsTree) args ++ ")"
renderObsTree ObsCutoff = "<cutoff>"
renderObsTree (ObsRaisedBottom tag) = "<bottom#" ++ show tag ++ ">"
renderObsTree ObsRaisedSyncError = "<exception>"
renderObsTree ObsTimedOut = "<timeout>"

-- | Evaluate one bounded observation under a microsecond timeout and a 64 MiB
-- per-sample allocation guard, catching 'ObsBottom' and synchronous exceptions
-- while rethrowing external asynchronous exceptions.
evalObsSample :: Int -> (Int -> a -> IO ObsTree) -> Int -> a -> IO ObsTree
evalObsSample timeoutUs approxFn depth val = do
  mb <- timeout (max 1 timeoutUs) (catchObs (withAllocGuard (approxFn depth val)))
  pure $ case mb of
    Nothing -> ObsTimedOut
    Just tree -> tree
  where
    withAllocGuard :: IO ObsTree -> IO ObsTree
    withAllocGuard act =
      bracket
        ( do
            prev <- getAllocationCounter
            setAllocationCounter (64 * 1024 * 1024)
            enableAllocationLimit
            pure prev
        )
        (\prev -> disableAllocationLimit >> setAllocationCounter prev)
        (\_ -> act)

catchObs :: IO ObsTree -> IO ObsTree
catchObs act =
  act `catch` \(exn :: SomeException) ->
    case fromException exn :: Maybe AllocationLimitExceeded of
      Just AllocationLimitExceeded -> pure ObsTimedOut
      Nothing ->
        case fromException exn :: Maybe SomeAsyncException of
          Just asyncExn -> throwIO asyncExn
          Nothing ->
            case fromException exn :: Maybe ObsBottom of
              Just (ObsBottom tag) -> pure (ObsRaisedBottom tag)
              Nothing -> pure ObsRaisedSyncError

-- | Domain types with total generation, partial demand generation, shrinking,
-- bounded Kleene approximation, and counterexample rendering.
class ObsGen a where
  obsGen :: Gen a
  default obsGen :: (Generic a, GObsGen (Rep a)) => Gen a
  obsGen = to <$> gObsGen

  obsGenPartial :: Int -> Gen a
  default obsGenPartial :: (Generic a, GObsGen (Rep a)) => Int -> Gen a
  obsGenPartial pct = mixPartial pct (to <$> gObsGenPartial pct)

  obsShrink :: a -> [a]
  default obsShrink :: (Generic a, GObsShrink (Rep a)) => a -> [a]
  obsShrink x = map to (gObsShrink (from x))

  obsApprox :: Int -> a -> IO ObsTree
  default obsApprox :: (Generic a, GObsApprox (Rep a)) => Int -> a -> IO ObsTree
  obsApprox depth x
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        whnf <- evaluate x
        gObsApprox depth (from whnf)

  obsShow :: a -> String
  default obsShow :: Show a => a -> String
  obsShow x = renderSafe (show x)

renderSafe :: String -> String
renderSafe str = renderList 0 str
  where
    renderList :: Int -> String -> String
    renderList n s
      | n >= 64 = "..."
      | otherwise =
          case unsafeTryPrefix s of
            Right Nothing -> ""
            Right (Just (c, rest)) -> c : renderList (n + 1) rest
            Left tag -> tag

{-# NOINLINE unsafeTryPrefix #-}
unsafeTryPrefix :: String -> Either String (Maybe (Char, String))
unsafeTryPrefix s =
  System.IO.Unsafe.unsafePerformIO $
    ( do
        xs <- evaluate s
        case xs of
          [] -> pure (Right Nothing)
          c : rest -> do
            c' <- evaluate c
            pure (Right (Just (c', rest)))
    )
      `catch` \(exn :: SomeException) ->
        case fromException exn :: Maybe SomeAsyncException of
          Just asyncExn -> throwIO asyncExn
          Nothing ->
            case fromException exn :: Maybe ObsBottom of
              Just (ObsBottom tag) -> pure (Left ("<bottom#" ++ show tag ++ ">"))
              Nothing -> pure (Left "<exception>")

-- ---------------------------------------------------------------------------
-- Standard ObsGen instances
-- ---------------------------------------------------------------------------

obsScalarApprox :: Show a => Int -> a -> IO ObsTree
obsScalarApprox depth x
  | depth <= 0 = pure ObsCutoff
  | otherwise = catchObs $ do
      v <- evaluate x
      pure (ObsCon (show v) [])

obsSafeShowScalar :: Show a => a -> String
obsSafeShowScalar x =
  System.IO.Unsafe.unsafePerformIO $
    ( do
        v <- evaluate x
        pure (show v)
    )
      `catch` \(exn :: SomeException) ->
        case fromException exn :: Maybe SomeAsyncException of
          Just asyncExn -> throwIO asyncExn
          Nothing ->
            case fromException exn :: Maybe ObsBottom of
              Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
              Nothing -> pure "<exception>"

instance ObsGen () where
  obsGen = pure ()
  obsGenPartial pct = mixPartial pct (pure ())
  obsShrink () = []
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Bool where
  obsGen = elements [False, True]
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink True = [False]
  obsShrink False = []
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Ordering where
  obsGen = elements [LT, EQ, GT]
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink GT = [EQ, LT]
  obsShrink LT = [EQ]
  obsShrink EQ = []
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Char where
  obsGen = sized $ \sz ->
    if sz <= 4
      then elements ['a', 'b', 'c', '0', ' ']
      else chr <$> chooseInt (32, 126)
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink c
    | c == 'a' = []
    | c `elem` ['b', 'c'] = ['a']
    | otherwise = ['a' | ord c > ord 'a']
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

shrinkIntegral :: Integral a => a -> [a]
shrinkIntegral 0 = []
shrinkIntegral n =
  let neg = [abs n | n < 0 && toInteger n /= toInteger (minBound :: Int)]
      halves = 0 : [n - d | d <- drop 1 (takeWhile (/= 0) (iterate (`quot` 2) n))]
   in neg ++ halves

instance ObsGen Int where
  obsGen = sized $ \sz ->
    if sz <= 0
      then pure 0
      else
        if sz <= 4
          then frequency [(1, elements [0, 1, -1, 2, -2]), (3, chooseInt (-sz, sz))]
          else chooseInt (-sz, sz)
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink = shrinkIntegral
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Word where
  obsGen = sized $ \sz -> fromIntegral <$> chooseInt (0, max 0 sz)
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink 0 = []
  obsShrink w = 0 : [w - d | d <- takeWhile (> 0) (iterate (`quot` 2) w), w - d /= w, w - d /= 0]
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Integer where
  obsGen = sized $ \sz -> chooseInteger (negate (fromIntegral sz), fromIntegral sz)
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink = shrinkIntegral
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen Natural where
  obsGen = sized $ \sz -> fromIntegral <$> chooseInt (0, max 0 sz)
  obsGenPartial pct = mixPartial pct obsGen
  obsShrink 0 = []
  obsShrink n = 0 : [n - d | d <- takeWhile (> 0) (iterate (`quot` 2) n), d <= n, n - d /= n, n - d /= 0]
  obsApprox = obsScalarApprox
  obsShow = obsSafeShowScalar

instance ObsGen a => ObsGen (Maybe a) where
  obsGen = sized $ \sz ->
    if sz <= 0
      then pure Nothing
      else frequency [(1, pure Nothing), (3, Just <$> resize (sz - 1) obsGen)]
  obsGenPartial pct =
    mixPartial pct $
      sized $ \sz ->
        if sz <= 0
          then pure Nothing
          else frequency [(1, pure Nothing), (3, Just <$> resize (sz - 1) (obsGenPartial pct))]
  obsShrink Nothing = []
  obsShrink (Just x) = Nothing : map Just (obsShrink x)
  obsApprox depth mx
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        v <- evaluate mx
        case v of
          Nothing -> pure (ObsCon "Nothing" [])
          Just x -> do
            tx <- obsApprox (depth - 1) x
            pure (ObsCon "Just" [tx])
  obsShow mx =
    System.IO.Unsafe.unsafePerformIO $
      ( do
          v <- evaluate mx
          pure $ case v of
            Nothing -> "Nothing"
            Just x -> "(Just " ++ obsShow x ++ ")"
      )
        `catch` \(exn :: SomeException) ->
          case fromException exn :: Maybe SomeAsyncException of
            Just asyncExn -> throwIO asyncExn
            Nothing ->
              case fromException exn :: Maybe ObsBottom of
                Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
                Nothing -> pure "<exception>"

instance (ObsGen a, ObsGen b) => ObsGen (Either a b) where
  obsGen = sized $ \sz ->
    oneof [Left <$> resize (sz `quot` 2) obsGen, Right <$> resize (sz `quot` 2) obsGen]
  obsGenPartial pct =
    mixPartial pct $
      sized $ \sz ->
        oneof
          [ Left <$> resize (sz `quot` 2) (obsGenPartial pct)
          , Right <$> resize (sz `quot` 2) (obsGenPartial pct)
          ]
  obsShrink (Left x) = map Left (obsShrink x)
  obsShrink (Right y) = map Right (obsShrink y)
  obsApprox depth ex
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        v <- evaluate ex
        case v of
          Left x -> ObsCon "Left" . (: []) <$> obsApprox (depth - 1) x
          Right y -> ObsCon "Right" . (: []) <$> obsApprox (depth - 1) y
  obsShow ex =
    System.IO.Unsafe.unsafePerformIO $
      ( do
          v <- evaluate ex
          pure $ case v of
            Left x -> "(Left " ++ obsShow x ++ ")"
            Right y -> "(Right " ++ obsShow y ++ ")"
      )
        `catch` \(exn :: SomeException) ->
          case fromException exn :: Maybe SomeAsyncException of
            Just asyncExn -> throwIO asyncExn
            Nothing ->
              case fromException exn :: Maybe ObsBottom of
                Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
                Nothing -> pure "<exception>"

instance (ObsGen a, ObsGen b) => ObsGen (a, b) where
  obsGen = sized $ \sz ->
    (,) <$> resize (sz `quot` 2) obsGen <*> resize (sz `quot` 2) obsGen
  obsGenPartial pct =
    mixPartial pct $
      sized $ \sz ->
        (,) <$> resize (sz `quot` 2) (obsGenPartial pct) <*> resize (sz `quot` 2) (obsGenPartial pct)
  obsShrink (x, y) =
    [(x', y) | x' <- obsShrink x] ++ [(x, y') | y' <- obsShrink y]
  obsApprox depth pr
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        (x, y) <- evaluate pr
        tx <- obsApprox (depth - 1) x
        ty <- obsApprox (depth - 1) y
        pure (ObsCon "(,)" [tx, ty])
  obsShow pr =
    System.IO.Unsafe.unsafePerformIO $
      ( do
          (x, y) <- evaluate pr
          pure ("(" ++ obsShow x ++ ", " ++ obsShow y ++ ")")
      )
        `catch` \(exn :: SomeException) ->
          case fromException exn :: Maybe SomeAsyncException of
            Just asyncExn -> throwIO asyncExn
            Nothing ->
              case fromException exn :: Maybe ObsBottom of
                Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
                Nothing -> pure "<exception>"

instance (ObsGen a, ObsGen b, ObsGen c) => ObsGen (a, b, c) where
  obsGen = sized $ \sz ->
    (,,)
      <$> resize (sz `quot` 3) obsGen
      <*> resize (sz `quot` 3) obsGen
      <*> resize (sz `quot` 3) obsGen
  obsGenPartial pct =
    mixPartial pct $
      sized $ \sz ->
        (,,)
          <$> resize (sz `quot` 3) (obsGenPartial pct)
          <*> resize (sz `quot` 3) (obsGenPartial pct)
          <*> resize (sz `quot` 3) (obsGenPartial pct)
  obsShrink (x, y, z) =
    [(x', y, z) | x' <- obsShrink x]
      ++ [(x, y', z) | y' <- obsShrink y]
      ++ [(x, y, z') | z' <- obsShrink z]
  obsApprox depth tr
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        (x, y, z) <- evaluate tr
        tx <- obsApprox (depth - 1) x
        ty <- obsApprox (depth - 1) y
        tz <- obsApprox (depth - 1) z
        pure (ObsCon "(,,)" [tx, ty, tz])
  obsShow tr =
    System.IO.Unsafe.unsafePerformIO $
      ( do
          (x, y, z) <- evaluate tr
          pure ("(" ++ obsShow x ++ ", " ++ obsShow y ++ ", " ++ obsShow z ++ ")")
      )
        `catch` \(exn :: SomeException) ->
          case fromException exn :: Maybe SomeAsyncException of
            Just asyncExn -> throwIO asyncExn
            Nothing ->
              case fromException exn :: Maybe ObsBottom of
                Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
                Nothing -> pure "<exception>"

instance ObsGen a => ObsGen [a] where
  obsGen = listOf obsGen
  obsGenPartial pct =
    mixPartial pct $
      sized $ \sz ->
        if sz <= 0
          then pure []
          else
            frequency
              [ (2, pure [])
              , (5, (:) <$> resize (sz `quot` 2) (obsGenPartial pct) <*> resize (sz - 1) (obsGenPartial pct))
              ]
  obsShrink xs =
    case safeUncons xs of
      Just (y, ys) ->
        [ys]
          ++ [y' : ys | y' <- obsShrink y]
          ++ [y : ys' | ys' <- obsShrink ys]
      Nothing -> []
    where
      safeUncons s =
        System.IO.Unsafe.unsafePerformIO $
          ( do
              v <- evaluate s
              pure $ case v of
                [] -> Nothing
                h : t -> Just (h, t)
          )
            `catch` \(_ :: SomeException) -> pure Nothing
  obsApprox depth xs
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        v <- evaluate xs
        case v of
          [] -> pure (ObsCon "[]" [])
          h : t -> do
            th <- obsApprox (depth - 1) h
            tt <- obsApprox (depth - 1) t
            pure (ObsCon ":" [th, tt])
  obsShow xs = "[" ++ go 0 xs
    where
      go :: Int -> [a] -> String
      go n rest
        | n >= 16 = "...]"
        | otherwise =
            System.IO.Unsafe.unsafePerformIO $
              ( do
                  v <- evaluate rest
                  pure $ case v of
                    [] -> "]"
                    h : t ->
                      let sep = if n == 0 then "" else ", "
                       in sep ++ obsShow h ++ go (n + 1) t
              )
                `catch` \(exn :: SomeException) ->
                  case fromException exn :: Maybe SomeAsyncException of
                    Just asyncExn -> throwIO asyncExn
                    Nothing ->
                      let prefix = if n == 0 then "" else " : "
                       in case fromException exn :: Maybe ObsBottom of
                            Just (ObsBottom tag) -> pure (prefix ++ "<bottom#" ++ show tag ++ ">]")
                            Nothing -> pure (prefix ++ "<exception>]")

-- ---------------------------------------------------------------------------
-- Generic derivation helpers for user algebraic datatypes
-- ---------------------------------------------------------------------------

class GObsGen f where
  gObsGen :: Gen (f p)
  gObsGenPartial :: Int -> Gen (f p)
  gNullaryBranches :: [Gen (f p)]

instance GObsGen f => GObsGen (M1 i c f) where
  gObsGen = M1 <$> gObsGen
  gObsGenPartial pct = M1 <$> gObsGenPartial pct
  gNullaryBranches = map (fmap M1) gNullaryBranches

instance GObsGen U1 where
  gObsGen = pure U1
  gObsGenPartial _ = pure U1
  gNullaryBranches = [pure U1]

instance ObsGen c => GObsGen (K1 i c) where
  gObsGen = K1 <$> sized (\sz -> resize (max 0 (sz - 1)) obsGen)
  gObsGenPartial pct = K1 <$> sized (\sz -> resize (max 0 (sz - 1)) (obsGenPartial pct))
  gNullaryBranches = []

instance (GObsGen a, GObsGen b) => GObsGen (a :*: b) where
  gObsGen = sized $ \sz ->
    (:*:) <$> resize (sz `quot` 2) gObsGen <*> resize (sz `quot` 2) gObsGen
  gObsGenPartial pct = sized $ \sz ->
    (:*:) <$> resize (sz `quot` 2) (gObsGenPartial pct) <*> resize (sz `quot` 2) (gObsGenPartial pct)
  gNullaryBranches = []

instance (GObsGen a, GObsGen b) => GObsGen (a :+: b) where
  gObsGen = sized $ \sz ->
    let bases = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches
     in if sz <= 0 && not (null bases)
          then oneof bases
          else oneof [L1 <$> gObsGen, R1 <$> gObsGen]
  gObsGenPartial pct = sized $ \sz ->
    let bases = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches
     in if sz <= 0 && not (null bases)
          then oneof bases
          else oneof [L1 <$> gObsGenPartial pct, R1 <$> gObsGenPartial pct]
  gNullaryBranches = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches

class GObsShrink f where
  gObsShrink :: f p -> [f p]

instance GObsShrink f => GObsShrink (M1 i c f) where
  gObsShrink (M1 x) = map M1 (gObsShrink x)

instance GObsShrink U1 where
  gObsShrink U1 = []

instance ObsGen c => GObsShrink (K1 i c) where
  gObsShrink (K1 x) = map K1 (obsShrink x)

instance (GObsShrink a, GObsShrink b) => GObsShrink (a :*: b) where
  gObsShrink (x :*: y) =
    [x' :*: y | x' <- gObsShrink x] ++ [x :*: y' | y' <- gObsShrink y]

instance (GObsShrink a, GObsShrink b) => GObsShrink (a :+: b) where
  gObsShrink (L1 x) = map L1 (gObsShrink x)
  gObsShrink (R1 y) = map R1 (gObsShrink y)

class GObsApprox f where
  gObsApprox :: Int -> f p -> IO ObsTree

instance GObsApprox f => GObsApprox (M1 D c f) where
  gObsApprox d (M1 x) = gObsApprox d x

instance (Constructor c, GObsFields f) => GObsApprox (M1 C c f) where
  gObsApprox d m@(M1 x) = do
    ts <- gObsFields (d - 1) x
    pure (ObsCon (conName m) ts)

instance (GObsApprox a, GObsApprox b) => GObsApprox (a :+: b) where
  gObsApprox d (L1 x) = gObsApprox d x
  gObsApprox d (R1 y) = gObsApprox d y

class GObsFields f where
  gObsFields :: Int -> f p -> IO [ObsTree]

instance GObsFields f => GObsFields (M1 i c f) where
  gObsFields d (M1 x) = gObsFields d x

instance GObsFields U1 where
  gObsFields _ U1 = pure []

instance ObsGen c => GObsFields (K1 i c) where
  gObsFields d (K1 x) = (: []) <$> obsApprox d x

instance (GObsFields a, GObsFields b) => GObsFields (a :*: b) where
  gObsFields d (x :*: y) = (++) <$> gObsFields d x <*> gObsFields d y

-- ---------------------------------------------------------------------------
-- Plugin runtime harness helpers
-- ---------------------------------------------------------------------------

-- | Method bundle synthesized on the fly by @Dependent.Plugin.ObsEq@ for
-- algebraic datatypes that do not declare an explicit 'ObsGen' instance.
data AdtObsDict a
  = AdtObsDict
      (Gen a)
      (Int -> Gen a)
      (a -> [a])
      (Int -> a -> IO ObsTree)
      (a -> String)

-- | Extract the total generator from an 'AdtObsDict'.
adtGen :: AdtObsDict a -> Gen a
adtGen (AdtObsDict g _ _ _ _) = g

-- | Extract the partial generator from an 'AdtObsDict'.
adtGenPartial :: AdtObsDict a -> Int -> Gen a
adtGenPartial (AdtObsDict _ gp _ _ _) = gp

-- | Extract the shrinker from an 'AdtObsDict'.
adtShrink :: AdtObsDict a -> a -> [a]
adtShrink (AdtObsDict _ _ sh _ _) = sh

-- | Extract the bounded tree approximator from an 'AdtObsDict'.
adtApprox :: AdtObsDict a -> Int -> a -> IO ObsTree
adtApprox (AdtObsDict _ _ _ ap _) = ap

-- | Extract the value printer from an 'AdtObsDict'.
adtShow :: AdtObsDict a -> a -> String
adtShow (AdtObsDict _ _ _ _ sw) = sw

-- | Build an 'AdtObsDict' from constructor generators, a WHNF shrinker, a WHNF
-- tree builder, and a WHNF printer.
mkAdtObsDict
  :: [Gen a]
  -> [Int -> Gen a]
  -> [Int -> Int -> Gen a]
  -> (a -> [a])
  -> (Int -> a -> IO ObsTree)
  -> (a -> IO String)
  -> AdtObsDict a
mkAdtObsDict baseGens totalCons partialCons rawShrink rawApprox rawShow =
  AdtObsDict genTotal genPart safeShrink approxFn showFn
  where
    genTotal = sized $ \sz ->
      if sz <= 0 && not (null baseGens)
        then oneof baseGens
        else
          let stepSz = max 0 (sz - 1)
              allBranches = map (resize stepSz . ($ stepSz)) totalCons
           in if null baseGens
                then oneof allBranches
                else frequency [(1, oneof baseGens), (3, oneof allBranches)]

    genPart pct =
      mixPartial pct $
        sized $ \sz ->
          if sz <= 0 && not (null baseGens)
            then oneof baseGens
            else
              let stepSz = max 0 (sz - 1)
                  allBranches = map (\f -> resize stepSz (f pct stepSz)) partialCons
               in if null baseGens
                    then oneof allBranches
                    else frequency [(1, oneof baseGens), (3, oneof allBranches)]

    safeShrink x =
      System.IO.Unsafe.unsafePerformIO $
        ( do
            v <- evaluate x
            let ys = rawShrink v
            _ <- evaluate (length ys)
            pure ys
        )
          `catch` \(_ :: SomeException) -> pure []

    approxFn depth x
      | depth <= 0 = pure ObsCutoff
      | otherwise = catchObs $ do
          v <- evaluate x
          rawApprox (depth - 1) v

    showFn x =
      renderSafe $
        System.IO.Unsafe.unsafePerformIO $
          ( do
              v <- evaluate x
              rawShow v
          )
            `catch` \(exn :: SomeException) ->
              case fromException exn :: Maybe SomeAsyncException of
                Just asyncExn -> throwIO asyncExn
                Nothing ->
                  case fromException exn :: Maybe ObsBottom of
                    Just (ObsBottom tag) -> pure ("<bottom#" ++ show tag ++ ">")
                    Nothing -> pure "<exception>"

-- | Compute the three-valued 'ObsVerdict' across the configured sample schedule.
evalObsVerdict
  :: forall env r.
     ObsConfig
  -> (Int -> Gen env)
  -> (env -> [env])
  -> (Int -> r -> IO ObsTree)
  -> (env -> r)
  -> (env -> r)
  -> IO (ObsVerdict env)
evalObsVerdict cfg mkEnvGen shrinkEnv approxR evalLhs evalRhs = do
  let nTests = max 1 (fromIntegral (obsTests cfg) :: Int)
      maxSz = max 0 (fromIntegral (obsMaxSize cfg) :: Int)
      depth = max 1 (fromIntegral (obsApproxDepth cfg) :: Int)
      depthNat = obsApproxDepth cfg
      partPct = min 100 (max 0 (fromIntegral (obsPartialPct cfg) :: Int))
      tmoUs = max 1 (fromIntegral (obsTimeoutUs cfg) :: Int)
      tmoNat = obsTimeoutUs cfg
      seed0 = fromIntegral (obsSeed cfg) :: Word64
      totalGen = mkEnvGen 0
      partialGen = mkEnvGen partPct
      shallowTmo = min 500 tmoUs

      testEnv :: env -> IO (ObsCmp, ObsTree, ObsTree)
      testEnv env = do
        let valL = evalLhs env
            valR = evalRhs env
        if depth <= 2
          then do
            tL <- evalObsSample tmoUs approxR depth valL
            tR <- evalObsSample tmoUs approxR depth valR
            pure (compareObsTree (max 1 depthNat) (max 1 tmoNat) tL tR, tL, tR)
          else do
            tL2 <- evalObsSample shallowTmo approxR 2 valL
            tR2 <- evalObsSample shallowTmo approxR 2 valR
            case compareObsTree 2 (fromIntegral (max 1 shallowTmo)) tL2 tR2 of
              ObsEqual -> pure (ObsEqual, tL2, tR2)
              ObsApart -> pure (ObsApart, tL2, tR2)
              ObsUnknown _ -> do
                tL <- evalObsSample tmoUs approxR depth valL
                tR <- evalObsSample tmoUs approxR depth valR
                pure (compareObsTree (max 1 depthNat) (max 1 tmoNat) tL tR, tL, tR)

      shrinkLoop :: Int -> env -> (ObsTree, ObsTree) -> IO (Int, env, (ObsTree, ObsTree))
      shrinkLoop steps cur bestTrees
        | steps >= 64 = pure (steps, cur, bestTrees)
        | otherwise = findSmaller (take 32 (shrinkEnv cur))
        where
          findSmaller [] = pure (steps, cur, bestTrees)
          findSmaller (cand : rest) = do
            (cmp, tL', tR') <- testEnv cand
            case cmp of
              ObsApart -> shrinkLoop (steps + 1) cand (tL', tR')
              _ -> findSmaller rest

      loop :: Int -> Maybe InconclusiveReason -> IO (ObsVerdict env)
      loop idx mbUnknown
        | idx >= nTests =
            pure $ case mbUnknown of
              Nothing -> Verified
              Just reason -> Inconclusive reason
        | otherwise = do
            let sz = sampleScheduleSize idx nTests maxSz
                usePartial = partPct > 0 && idx >= 5 && ((idx * 37 + 13) `rem` 100 < partPct)
                baseGen = if usePartial then partialGen else totalGen
                chosenGen = applyAxisProbe idx sz baseGen
                env = runGenAt seed0 idx sz chosenGen
            (cmp, tL, tR) <- testEnv env
            case cmp of
              ObsEqual -> loop (idx + 1) mbUnknown
              ObsUnknown r ->
                let nextUnknown = case mbUnknown of
                      Nothing -> Just r
                      Just prev -> Just prev
                 in loop (idx + 1) nextUnknown
              ObsApart -> do
                (shrunkSteps, minEnv, (minL, minR)) <- shrinkLoop 0 env (tL, tR)
                pure (Refuted (idx + 1) shrunkSteps minEnv minL minR)

  loop 0 Nothing

sampleScheduleSize :: Int -> Int -> Int -> Int
sampleScheduleSize idx nTests maxSz
  | maxSz <= 0 = 0
  | nTests <= 1 = maxSz
  | idx == 0 = 0
  | idx <= 2 = min maxSz 1
  | idx <= 4 = min maxSz 2
  | idx <= 7 = min maxSz 3
  | idx == nTests - 1 = maxSz
  | otherwise =
      let remN = max 1 (nTests - 8)
          k = idx - 8
          spanCube = toInteger maxSz * toInteger maxSz * toInteger maxSz
          u = (toInteger (remN - 1 - k) * spanCube) `quot` toInteger remN
          r = integerCubeRoot u
       in max 1 (min maxSz (maxSz - fromIntegral r))

integerCubeRoot :: Integer -> Integer
integerCubeRoot n
  | n <= 0 = 0
  | otherwise = go n
  where
    go x =
      let x' = (2 * x + (n `quot` (x * x))) `quot` 3
       in if x' >= x then x else go x'

applyAxisProbe :: Int -> Int -> Gen a -> Gen a
applyAxisProbe idx sz (Gen g)
  | idx >= 1 && idx <= 4 = Gen $ \s _ ->
      let (s1, s2) = splitSeed s
          (w, _) = stepSeed s1
          probeSz = if even idx then max 1 sz else 0
          _ = w
       in g s2 probeSz
  | otherwise = Gen g

-- | Execute the bounded observational test loop for a constraint and return
-- @\"PASS\"@ when all samples agree, @\"FAIL:\"@ followed by a shrunk
-- counterexample summary when falsified, or @\"INCONCLUSIVE:\"@ followed by an
-- encoded 'InconclusiveReason' when resource or exception limits intervene.
runObsTestLoop
  :: forall env r.
     ObsConfig
  -> (Int -> Gen env)
  -- ^ Environment generator parameterized by partiality percentage @[0..100]@.
  -> (env -> [env])
  -- ^ Environment shrinker.
  -> (env -> String)
  -- ^ Environment pretty-printer for counterexample reporting.
  -> (Int -> r -> IO ObsTree)
  -- ^ Bounded Kleene approximation on the result type @r@.
  -> (env -> r)
  -- ^ Left-hand side evaluator.
  -> (env -> r)
  -- ^ Right-hand side evaluator.
  -> IO String
runObsTestLoop cfg mkEnvGen shrinkEnv showEnv approxR evalLhs evalRhs = do
  verdict <- evalObsVerdict cfg mkEnvGen shrinkEnv approxR evalLhs evalRhs
  pure $ case verdict of
    Verified -> "PASS"
    Inconclusive reason -> "INCONCLUSIVE:" ++ show reason
    Refuted sampleNum shrunkSteps minEnv minL minR ->
      let envStr = showEnv minEnv
          bindsPart = if null envStr then "closed sample" else envStr
       in "FAIL:after "
            ++ show sampleNum
            ++ " test(s)"
            ++ (if shrunkSteps > 0 then " and " ++ show shrunkSteps ++ " shrink(s)" else "")
            ++ ": "
            ++ bindsPart
            ++ " gives lhs = "
            ++ renderObsTree minL
            ++ ", rhs = "
            ++ renderObsTree minR

-- | Unconstrained 'pure' for 'Gen', used by plugin Core synthesis.
obsPureGen :: a -> Gen a
obsPureGen = pure

-- | Unconstrained '(<*>)' for 'Gen', used by plugin Core synthesis.
obsApGen :: Gen (a -> b) -> Gen a -> Gen b
obsApGen = (<*>)

-- | Unconstrained 'pure' for 'IO', used by plugin Core synthesis.
obsPureIO :: a -> IO a
obsPureIO = pure

-- | Unconstrained '(>>=)' for 'IO', used by plugin Core synthesis.
obsBindIO :: IO a -> (a -> IO b) -> IO b
obsBindIO = (>>=)

-- | Unconstrained 'String' concatenation, used by plugin Core synthesis.
obsAppendStr :: String -> String -> String
obsAppendStr = (++)

-- | Unconstrained list concatenation, used by plugin Core synthesis.
obsAppendList :: [a] -> [a] -> [a]
obsAppendList = (++)

-- | Combine two partiality-parameterized generators into a pair generator
-- with axis-isolated Tier-0 boundary splits.
obsPairGen :: (Int -> Gen a) -> (Int -> Gen b) -> Int -> Gen (a, b)
obsPairGen ga gb pct = Gen $ \s sz ->
  let (s0, sRest) = splitSeed s
      (s1, s2) = splitSeed sRest
      (w, _) = stepSeed s0
      (szA, szB)
        | sz <= 2 && (w .&. 3 == 1) = (sz, 0)
        | sz <= 2 && (w .&. 3 == 2) = (0, sz)
        | otherwise = (sz `quot` 2, sz `quot` 2)
   in (unGen (ga pct) s1 szA, unGen (gb pct) s2 szB)

-- | Combine two component shrinkers into a pair shrinker.
obsPairShrink :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
obsPairShrink sa sb (x, y) =
  [(x', y) | x' <- sa x] ++ [(x, y') | y' <- sb y]

-- | Combine two component printers into a comma-separated environment string.
obsPairShow :: (a -> String) -> (b -> String) -> (a, b) -> String
obsPairShow pa pb (x, y) = pa x ++ ", " ++ pb y

-- | Prefix a rendered variable value with its source binder name.
obsNamedShow :: String -> (a -> String) -> a -> String
obsNamedShow nm pa x = nm ++ " = " ++ pa x

-- | Lift a pair of user 'Gen' values into a 2-variable environment generator.
obsSplitPairGen :: (Gen a, Gen b) -> Int -> Gen (a, b)
obsSplitPairGen (ga, gb) _ = sized $ \sz ->
  (,) <$> resize (sz `quot` 2) ga <*> resize (sz `quot` 2) gb

-- | Lift a triple of user 'Gen' values into a right-nested 3-variable environment generator.
obsSplitTripleGen :: (Gen a, Gen b, Gen c) -> Int -> Gen (a, (b, c))
obsSplitTripleGen (ga, gb, gc) _ = sized $ \sz ->
  let sub = sz `quot` 3
   in (,) <$> resize sub ga <*> ((,) <$> resize sub gb <*> resize sub gc)



