{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Dependent.ObsEq.Domain
Description : Generators, shrinkers, ObsDomain overrides, and Kleene test loops
License     : BSD-3-Clause
Maintainer  : mpg@mpg.is

Deterministic PRNG, value generators, invariant-preserving 'ObsDomain'
specifications, strong three-valued Kleene tree comparison, and runtime test
loops for @Dependent.ObsEq@ and @Dependent.Plugin.ObsEq@.

This module intentionally omits @-XDependentTypes@ so 'forType' and 'forVar'
remain uninterpreted modifiers (@U:forType@, @U:forVar@) whose domain
arguments stay visible to 'Dependent.Plugin.ObsEq' during type-spine peeling.
-}
module Dependent.ObsEq.Domain (
    -- * Domain overrides
    ObsDomain (..),
    domain,
    domainGen,
    domainVia,
    domainSuchThat,
    forType,
    forVar,
    obsDomGenPartial,
    obsDomShrink,
    obsDomPred,
    obsDomShow,

    -- * Deterministic PRNG and generators
    Seed (..),
    mkSeed,
    stepSeed,
    splitSeed,
    Gen (..),
    runGenAt,
    sized,
    resize,
    chooseWord64,
    chooseInt,
    chooseInteger,
    elements,
    oneof,
    frequency,
    listOf,

    -- * Partial demand probes and Kleene observation verdicts
    ObsBottom (..),
    obsBottom,
    freshBottom,
    mixPartial,
    ObsTree (..),
    InconclusiveReason (..),
    ObsCmp (..),
    ObsVerdict (..),
    GuardResult (..),
    compareObsTree,
    renderInconclusiveReason,
    evalObsSample,
    renderObsTree,
    hashObsTree,
    evalSideFingerprints,
    ObsGen (..),
    obsSafeShowScalar,

    -- * Plugin runtime harness helpers
    AdtObsDict (..),
    adtGen,
    adtGenPartial,
    adtShrink,
    adtApprox,
    adtShow,
    mkAdtObsDict,
    evalObsVerdict,
    runObsTestLoop,
    runObsOnLoop,
    runObsByLoop,
    obsNoBaseline,
    obsJustBaseline,
    obsAlwaysHolds,
    obsPredGuard,
    obsEqGuard,
    obsAndGuard,
    obsPureGen,
    obsApGen,
    obsApHalfGen,
    obsPureIO,
    obsBindIO,
    obsAppendStr,
    obsAppendList,
    obsMapList,
    obsPairGen,
    obsPairShrink,
    obsPairShow,
    obsNamedShow,
) where

import Control.Exception (
    AllocationLimitExceeded (..),
    Exception (..),
    SomeAsyncException,
    SomeException,
    bracket,
    catch,
    evaluate,
    throw,
    throwIO,
 )
import Data.Bits (shiftR, xor, (.&.))
import Data.Char (chr, ord)
import Data.Word (Word64)
import GHC.Generics (
    C,
    Constructor,
    D,
    Generic (..),
    K1 (..),
    M1 (..),
    U1 (..),
    conName,
    (:*:) (..),
    (:+:) (..),
 )
import Numeric.Natural (Natural)
import System.IO.Unsafe qualified
import System.Mem (
    disableAllocationLimit,
    enableAllocationLimit,
    getAllocationCounter,
    setAllocationCounter,
 )
import System.Timeout (timeout)

import Dependent.ObsEq.Internal (ObsConfig (..))

-- ---------------------------------------------------------------------------
-- Deterministic PRNG and Sized Generators
-- ---------------------------------------------------------------------------

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

{- | Generate a list whose length scales up to the active size.
See Note [Linear size stratification and non-geometric constructor choice].
-}
listOf :: Gen a -> Gen [a]
listOf g = sized $ \sz -> do
    len <-
        if sz <= 0
            then pure 0
            else
                frequency
                    [ (1, pure sz)
                    , (2, chooseInt (max 1 (sz `quot` 2), sz))
                    , (1, chooseInt (0, sz))
                    ]
    let build 0 = pure []
        build k = (:) <$> resize (sz `quot` 2) g <*> build (k - 1)
    build len

-- ---------------------------------------------------------------------------
-- Partial Demand Probes and Three-Valued Kleene Observation Lattice
-- ---------------------------------------------------------------------------

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

{- | Bounded Kleene approximation of a Haskell value.
See Note [Three-valued Kleene observation lattice].
-}
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
\* Two 'ObsCon' nodes with different constructor names or arities are
  'ObsApart'. Matching constructors combine child results with Kleene
  conjunction: any 'ObsApart' child yields 'ObsApart' immediately (for example,
  @(Zero, loop)@ vs @(Succ Zero, loop)@ is 'ObsApart' at 'fst'), else any
  'ObsUnknown' child yields 'ObsUnknown', else 'ObsEqual'.
\* 'ObsRaisedBottom' carries the deterministic PRNG tag of an injected partial
  input thunk. Raising the same tag on both sides proves identical first-demand
  laziness ('ObsEqual'); raising different tags or matching a value against
  'ObsRaisedBottom' proves a strictness mismatch ('ObsApart').
\* Resource limits ('ObsCutoff', 'ObsTimedOut') and double 'ObsRaisedSyncError'
  always yield 'ObsUnknown', which aggregates to 'Inconclusive' and never emits
  a nominal coercion.
-}

{- | Reason why bounded testing returned 'Inconclusive'.
See Note [Three-valued Kleene observation lattice].
-}
data InconclusiveReason
    = DepthCutoffReached !Natural
    | TimeoutReached !Natural
    | SyncExceptionRaised
    | InsufficientPreconditionHits !Natural !Natural
    | PolymorphicClassConstraint !String
    deriving (Eq, Ord, Show, Read)

{- | Per-sample three-valued strong Kleene observation result.
See Note [Three-valued Kleene observation lattice].
-}
data ObsCmp
    = {- | Both trees are finite constructor spines with identical constructors and
      leaves, or both raised the same injected 'ObsBottom' tag.
      -}
      ObsEqual
    | -- | Definite mismatch at a finite constructor path or demand probe.
      ObsApart
    | {- | At least one side hit a resource cutoff, timeout, or synchronous error,
      and no finite branch was 'ObsApart'.
      -}
      ObsUnknown !InconclusiveReason
    deriving (Eq, Show)

-- | Aggregate verdict of bounded observational testing across all samples.
data ObsVerdict env
    = Verified
    | Refuted !Int !Int !env !ObsTree !ObsTree
    | Inconclusive !InconclusiveReason
    deriving (Eq, Show)

{- | Outcome of evaluating a Given precondition or custom domain predicate on a
candidate input.
-}
data GuardResult
    = GuardHolds
    | GuardFails
    | GuardUnknown !InconclusiveReason
    deriving (Eq, Show)

{- | Compare two 'ObsTree' observations in the strong Kleene lattice.
See Note [Three-valued Kleene observation lattice].
-}
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

{- | Evaluate one bounded observation under a microsecond timeout and a 64 MiB
per-sample allocation guard, catching 'ObsBottom' and synchronous exceptions
while rethrowing external asynchronous exceptions.
-}
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

{- | Compute a 64-bit FNV-1a fingerprint of a finite 'ObsTree', returning @0@
when any node hits a resource cutoff, timeout, or synchronous exception.
-}
hashObsTree :: ObsTree -> Word64
hashObsTree = go 0xcbf29ce484222325
  where
    step :: Word64 -> Word64 -> Word64
    step h b = (h `xor` b) * 0x100000001b3

    hashBytes :: Word64 -> String -> Word64
    hashBytes = foldl (\h c -> step h (fromIntegral (ord c)))

    go :: Word64 -> ObsTree -> Word64
    go h (ObsCon nm children) =
        let h1 = step (hashBytes (step h 1) nm) (fromIntegral (length children))
         in foldMTree h1 children
    go h (ObsRaisedBottom tag) =
        let r = step (step h 2) (fromIntegral tag)
         in if r == 0 then 1 else r
    go _ ObsCutoff = 0
    go _ ObsTimedOut = 0
    go _ ObsRaisedSyncError = 0

    foldMTree :: Word64 -> [ObsTree] -> Word64
    foldMTree acc [] = if acc == 0 then 1 else acc
    foldMTree acc (t : ts) =
        let h' = go acc t
         in if h' == 0 then 0 else foldMTree h' ts

-- | Evaluate 8 Tier-0 probe fingerprints for an open expression side.
evalSideFingerprints ::
    forall env r.
    ObsConfig ->
    (Int -> Gen env) ->
    (Int -> r -> IO ObsTree) ->
    (env -> r) ->
    IO String
evalSideFingerprints cfg mkEnvGen approxR evalSide = do
    let maxSz = max 0 (fromIntegral (obsMaxSize cfg) :: Int)
        partPct = min 100 (max 0 (fromIntegral (obsPartialPct cfg) :: Int))
        tmoUs = min 1000 (max 1 (fromIntegral (obsTimeoutUs cfg) :: Int))
        seed0 = fromIntegral (obsSeed cfg) :: Word64
        totalGen = mkEnvGen 0
        partialGen = mkEnvGen partPct
        probeOne idx = do
            let sz = sampleScheduleSize idx 8 maxSz
                usePartial = partPct > 0 && idx >= 5 && ((idx * 37 + 13) `rem` 100 < partPct)
                baseGen = if usePartial then partialGen else totalGen
                env = runGenAt seed0 idx sz baseGen
            t <- evalObsSample tmoUs approxR 4 (evalSide env)
            pure (hashObsTree t)
    hashes <- mapM probeOne [0 .. 7]
    pure (unwords (map show hashes))

-- ---------------------------------------------------------------------------
-- ObsGen Type Class, Standard Instances, and ObsDomain Overrides
-- ---------------------------------------------------------------------------

{- | Domain types with total generation, partial demand generation, shrinking,
bounded Kleene approximation, and counterexample rendering.
-}
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
    default obsShow :: (Show a) => a -> String
    obsShow x = renderSafe (show x)

-- | Custom value generator, shrinker, invariant filter, and printer for @a@.
data ObsDomain a = ObsDomain
    { domGen :: Gen a
    -- ^ Total value generator.
    , domGenPartial :: Int -> Gen a
    -- ^ Generator parameterized by partiality percentage @[0..100]@.
    , domShrink :: a -> [a]
    -- ^ Invariant-preserving shrinker.
    , domPred :: Maybe (a -> Bool)
    -- ^ Optional predicate checked on every generated and shrunk candidate.
    , domShow :: a -> String
    -- ^ Safe counterexample renderer.
    }

-- | Pair an explicit generator with an explicit shrinker.
domain :: (Show a) => Gen a -> (a -> [a]) -> ObsDomain a
domain g sh =
    ObsDomain
        { domGen = g
        , domGenPartial = const g
        , domShrink = sh
        , domPred = Nothing
        , domShow = obsSafeShowScalar
        }

-- | Supply a custom generator without shrinking (never falls back to raw 'obsShrink').
domainGen :: (Show a) => Gen a -> ObsDomain a
domainGen g = domain g (const [])

{- | Build and shrink an invariant type @a@ through an 'ObsGen' proxy @p@.
Shrinking projects @a@ to @p@, shrinks @p@, and rebuilds @a@ via @build@,
preserving structural invariants at every shrink step.
-}
domainVia :: (ObsGen p, Show a) => (p -> a) -> (a -> p) -> ObsDomain a
domainVia build unbuild =
    ObsDomain
        { domGen = build <$> obsGen
        , domGenPartial = \pct -> build <$> obsGenPartial pct
        , domShrink = \x -> map build (obsShrink (unbuild x))
        , domPred = Nothing
        , domShow = obsSafeShowScalar
        }

-- | Sample with @g@ and filter 'obsShrink' candidates with invariant @p@.
domainSuchThat :: (ObsGen a) => (a -> Bool) -> Gen a -> ObsDomain a
domainSuchThat p g =
    ObsDomain
        { domGen = g
        , domGenPartial = const g
        , domShrink = filter p . obsShrink
        , domPred = Just p
        , domShow = obsShow
        }

{- | Attach an 'ObsDomain' for every quantified variable of type @a@.
Inspected at compile time by @Dependent.Plugin.ObsEq@ via @U:forType@.
-}
{-# NOINLINE forType #-}
forType :: forall a. ObsDomain a -> ObsConfig -> ObsConfig
forType _ cfg = cfg

{- | Attach an 'ObsDomain' to one specific in-scope @foreach@ binder @v@.
Inspected at compile time by @Dependent.Plugin.ObsEq@ via @U:forVar@.
-}
{-# NOINLINE forVar #-}
forVar :: forall {a}. a -> ObsDomain a -> ObsConfig -> ObsConfig
forVar _ _ cfg = cfg

-- | Extract 'domGenPartial' for plugin Core synthesis.
obsDomGenPartial :: ObsDomain a -> Int -> Gen a
obsDomGenPartial = domGenPartial

-- | Extract 'domShrink' for plugin Core synthesis.
obsDomShrink :: ObsDomain a -> a -> [a]
obsDomShrink = domShrink

-- | Evaluate 'domPred' (defaulting to @True@ when 'Nothing') for plugin Core synthesis.
obsDomPred :: ObsDomain a -> a -> Bool
obsDomPred dom x =
    case domPred dom of
        Nothing -> True
        Just p -> p x

-- | Extract 'domShow' for plugin Core synthesis.
obsDomShow :: ObsDomain a -> a -> String
obsDomShow = domShow

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

obsScalarApprox :: (Show a) => Int -> a -> IO ObsTree
obsScalarApprox depth x
    | depth <= 0 = pure ObsCutoff
    | otherwise = catchObs $ do
        v <- evaluate x
        pure (ObsCon (show v) [])

-- | Render a 'Show' value while catching 'ObsBottom' and synchronous exceptions.
obsSafeShowScalar :: (Show a) => a -> String
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

shrinkIntegral :: (Integral a) => a -> [a]
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
                let half = max 1 (sz `quot` 2)
                 in frequency
                        [ (1, elements [-sz, sz])
                        , (2, oneof [chooseInt (-sz, -half), chooseInt (half, sz)])
                        , (1, chooseInt (-sz, sz))
                        ]
    obsGenPartial pct = mixPartial pct obsGen
    obsShrink = shrinkIntegral
    obsApprox = obsScalarApprox
    obsShow = obsSafeShowScalar

instance ObsGen Word where
    obsGen = sized $ \sz ->
        if sz <= 0
            then pure 0
            else
                let half = max 1 (sz `quot` 2)
                 in frequency
                        [ (1, pure (fromIntegral sz))
                        , (2, fromIntegral <$> chooseInt (half, sz))
                        , (1, fromIntegral <$> chooseInt (0, sz))
                        ]
    obsGenPartial pct = mixPartial pct obsGen
    obsShrink 0 = []
    obsShrink w = 0 : [w - d | d <- takeWhile (> 0) (iterate (`quot` 2) w), w - d /= w, w - d /= 0]
    obsApprox = obsScalarApprox
    obsShow = obsSafeShowScalar

instance ObsGen Integer where
    obsGen = sized $ \sz ->
        if sz <= 0
            then pure 0
            else
                let s = fromIntegral sz :: Integer
                    half = max 1 (s `quot` 2)
                 in frequency
                        [ (1, elements [-s, s])
                        , (2, oneof [chooseInteger (-s, -half), chooseInteger (half, s)])
                        , (1, chooseInteger (-s, s))
                        ]
    obsGenPartial pct = mixPartial pct obsGen
    obsShrink = shrinkIntegral
    obsApprox = obsScalarApprox
    obsShow = obsSafeShowScalar

instance ObsGen Natural where
    obsGen = sized $ \sz ->
        if sz <= 0
            then pure 0
            else
                let half = max 1 (sz `quot` 2)
                 in frequency
                        [ (1, pure (fromIntegral sz))
                        , (2, fromIntegral <$> chooseInt (half, sz))
                        , (1, fromIntegral <$> chooseInt (0, sz))
                        ]
    obsGenPartial pct = mixPartial pct obsGen
    obsShrink 0 = []
    obsShrink n = 0 : [n - d | d <- takeWhile (> 0) (iterate (`quot` 2) n), d <= n, n - d /= n, n - d /= 0]
    obsApprox = obsScalarApprox
    obsShow = obsSafeShowScalar

instance (ObsGen a) => ObsGen (Maybe a) where
    obsGen = sized $ \sz ->
        if sz <= 0
            then pure Nothing
            else frequency [(1, pure Nothing), (max 3 (2 * sz), Just <$> resize (sz - 1) obsGen)]
    obsGenPartial pct =
        mixPartial pct $
            sized $ \sz ->
                if sz <= 0
                    then pure Nothing
                    else frequency [(1, pure Nothing), (max 3 (2 * sz), Just <$> resize (sz - 1) (obsGenPartial pct))]
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
    obsShrink (x, y) = obsPairShrink obsShrink obsShrink (x, y)
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

instance (ObsGen a) => ObsGen [a] where
    obsGen = listOf obsGen
    obsGenPartial pct
        | pct <= 0 = obsGen
        | otherwise =
            mixPartial pct $
                sized $ \sz ->
                    if sz <= 0
                        then pure []
                        else
                            frequency
                                [ (1, pure [])
                                , (4 * sz, (:) <$> resize (sz `quot` 2) (obsGenPartial pct) <*> resize (sz - 1) (obsGenPartial pct))
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
-- Generic Derivation Helpers for User Algebraic Datatypes
-- ---------------------------------------------------------------------------

{- Note [Linear size stratification and non-geometric constructor choice]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Unweighted choice between nullary and recursive constructors at every sum node
(@oneof [L1 ..., R1 ...]@) samples unary recursive types such as Peano @Nat@
from a @Geometric(1/2)@ distribution (@P(n >= k) = 2^(-k)@), independent of the
active generator size @sz@. Combined with a concave size schedule, values near
@obsMaxSize@ are practically unreachable and false equations that hold only on
small inputs can pass bounded testing.

To sample values across the full @[0 .. obsMaxSize]@ range without exponential
blowup on branching trees:

1. 'GObsGen' and 'mkAdtObsDict' collect nullary base constructors separately
   from non-nullary constructors ('chooseSumBranches'). When @sz <= 0@, only
   base constructors run. When @sz > 0@, non-nullary constructors receive weight
   @4 * sz@ against weight @1@ for base constructors, so a unary chain reaches
   full depth @sz@ with probability @prod_{k=1..sz} 4k / (4k + 1)@ (~41% at
   @sz = 20@) while still visiting intermediate depths for multi-variable goals.
2. Multi-field products ('splitProductSize' and 'obsApHalfGen') conserve the
   node budget across child fields so total constructor count stays @O(sz)@.
3. 'sampleScheduleSize' stratifies @idx = 0 .. nTests - 1@ linearly across
   @[0 .. maxSz]@, and scalar generators ('Int', 'Word', 'Integer', 'Natural')
   mix exact @+-sz@ boundaries, the upper shell @[sz/2 .. sz]@, and @[-sz .. sz]@.
-}

splitProductSize :: Int -> Gen (Int, Int)
splitProductSize sz
    | sz <= 1 = pure (0, 0)
    | otherwise = do
        mode <- chooseInt (0, 1)
        if mode == 0
            then let half = sz `quot` 2 in pure (half, sz - half)
            else do
                k <- chooseInt (0, sz)
                pure (k, sz - k)

chooseSumBranches :: Int -> [Gen a] -> [Gen a] -> Gen a
chooseSumBranches sz bases recs
    | null recs = oneof bases
    | null bases = oneof recs
    | sz <= 0 = oneof bases
    | otherwise = frequency [(1, oneof bases), (4 * sz, oneof recs)]

class GObsGen f where
    gObsGen :: Gen (f p)
    gObsGenPartial :: Int -> Gen (f p)
    gNullaryBranches :: [Gen (f p)]
    gCompoundBranches :: [Gen (f p)]
    gCompoundBranchesPartial :: Int -> [Gen (f p)]

instance (GObsGen f) => GObsGen (M1 i c f) where
    gObsGen = M1 <$> gObsGen
    gObsGenPartial pct = M1 <$> gObsGenPartial pct
    gNullaryBranches = map (fmap M1) gNullaryBranches
    gCompoundBranches = map (fmap M1) gCompoundBranches
    gCompoundBranchesPartial pct = map (fmap M1) (gCompoundBranchesPartial pct)

instance GObsGen U1 where
    gObsGen = pure U1
    gObsGenPartial _ = pure U1
    gNullaryBranches = [pure U1]
    gCompoundBranches = []
    gCompoundBranchesPartial _ = []

instance (ObsGen c) => GObsGen (K1 i c) where
    gObsGen = K1 <$> sized (\sz -> resize (max 0 (sz - 1)) obsGen)
    gObsGenPartial pct = K1 <$> sized (\sz -> resize (max 0 (sz - 1)) (obsGenPartial pct))
    gNullaryBranches = []
    gCompoundBranches = [gObsGen]
    gCompoundBranchesPartial pct = [gObsGenPartial pct]

instance (GObsGen a, GObsGen b) => GObsGen (a :*: b) where
    gObsGen = sized $ \sz -> do
        (szL, szR) <- splitProductSize sz
        (:*:) <$> resize szL gObsGen <*> resize szR gObsGen
    gObsGenPartial pct = sized $ \sz -> do
        (szL, szR) <- splitProductSize sz
        (:*:) <$> resize szL (gObsGenPartial pct) <*> resize szR (gObsGenPartial pct)
    gNullaryBranches = []
    gCompoundBranches = [gObsGen]
    gCompoundBranchesPartial pct = [gObsGenPartial pct]

instance (GObsGen a, GObsGen b) => GObsGen (a :+: b) where
    gObsGen = sized $ \sz ->
        let bases = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches
            recs = map (fmap L1) gCompoundBranches ++ map (fmap R1) gCompoundBranches
         in chooseSumBranches sz bases recs
    gObsGenPartial pct = sized $ \sz ->
        let bases = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches
            recs = map (fmap L1) (gCompoundBranchesPartial pct) ++ map (fmap R1) (gCompoundBranchesPartial pct)
         in chooseSumBranches sz bases recs
    gNullaryBranches = map (fmap L1) gNullaryBranches ++ map (fmap R1) gNullaryBranches
    gCompoundBranches = map (fmap L1) gCompoundBranches ++ map (fmap R1) gCompoundBranches
    gCompoundBranchesPartial pct =
        map (fmap L1) (gCompoundBranchesPartial pct) ++ map (fmap R1) (gCompoundBranchesPartial pct)

class GObsShrink f where
    gObsShrink :: f p -> [f p]

instance (GObsShrink f) => GObsShrink (M1 i c f) where
    gObsShrink (M1 x) = map M1 (gObsShrink x)

instance GObsShrink U1 where
    gObsShrink U1 = []

instance (ObsGen c) => GObsShrink (K1 i c) where
    gObsShrink (K1 x) = map K1 (obsShrink x)

instance (GObsShrink a, GObsShrink b) => GObsShrink (a :*: b) where
    gObsShrink (x :*: y) =
        [x' :*: y | x' <- gObsShrink x] ++ [x :*: y' | y' <- gObsShrink y]

instance (GObsShrink a, GObsShrink b) => GObsShrink (a :+: b) where
    gObsShrink (L1 x) = map L1 (gObsShrink x)
    gObsShrink (R1 y) = map R1 (gObsShrink y)

class GObsApprox f where
    gObsApprox :: Int -> f p -> IO ObsTree

instance (GObsApprox f) => GObsApprox (M1 D c f) where
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

instance (GObsFields f) => GObsFields (M1 i c f) where
    gObsFields d (M1 x) = gObsFields d x

instance GObsFields U1 where
    gObsFields _ U1 = pure []

instance (ObsGen c) => GObsFields (K1 i c) where
    gObsFields d (K1 x) = (: []) <$> obsApprox d x

instance (GObsFields a, GObsFields b) => GObsFields (a :*: b) where
    gObsFields d (x :*: y) = (++) <$> gObsFields d x <*> gObsFields d y

-- ---------------------------------------------------------------------------
-- Synthesized ADT Dictionary Bundle and Guard Helpers
-- ---------------------------------------------------------------------------

{- | Method bundle synthesized on the fly by @Dependent.Plugin.ObsEq@ for
algebraic datatypes that do not declare an explicit 'ObsGen' instance.
-}
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

{- | Build an 'AdtObsDict' from constructor generators, a WHNF shrinker, a WHNF
tree builder, and a WHNF printer.
-}
mkAdtObsDict ::
    [Gen a] ->
    [Int -> Gen a] ->
    [Int -> Int -> Gen a] ->
    (a -> [a]) ->
    (Int -> a -> IO ObsTree) ->
    (a -> IO String) ->
    AdtObsDict a
mkAdtObsDict baseGens totalCons partialCons rawShrink rawApprox rawShow =
    AdtObsDict genTotal genPart safeShrink approxFn showFn
  where
    genTotal = sized $ \sz ->
        let stepSz = max 0 (sz - 1)
            allBranches = map (resize stepSz . ($ stepSz)) totalCons
         in chooseSumBranches sz baseGens allBranches

    genPart pct =
        mixPartial pct $
            sized $ \sz ->
                let stepSz = max 0 (sz - 1)
                    allBranches = map (\f -> resize stepSz (f pct stepSz)) partialCons
                 in chooseSumBranches sz baseGens allBranches

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

-- | Absence of a baseline boundary-sweep generator.
obsNoBaseline :: forall env. Maybe (Int -> Gen env)
obsNoBaseline = Nothing

-- | Presence of a baseline boundary-sweep generator.
obsJustBaseline :: forall env. (Int -> Gen env) -> Maybe (Int -> Gen env)
obsJustBaseline = Just

-- | Trivial guard that accepts every sample.
obsAlwaysHolds :: forall env. env -> IO GuardResult
obsAlwaysHolds _ = pure GuardHolds

-- | Lift a boolean domain predicate into a 'GuardResult' check.
obsPredGuard :: forall env. Int -> (env -> Bool) -> env -> IO GuardResult
obsPredGuard tmoUs p env = do
    t <- evalObsSample tmoUs obsApprox 2 (p env)
    pure $ case t of
        ObsCon "True" [] -> GuardHolds
        ObsCon "False" [] -> GuardFails
        ObsRaisedBottom _ -> GuardFails
        ObsRaisedSyncError -> GuardFails
        ObsTimedOut -> GuardUnknown (TimeoutReached (fromIntegral (max 1 tmoUs)))
        ObsCutoff -> GuardUnknown (DepthCutoffReached 2)
        _ -> GuardUnknown SyncExceptionRaised

-- | Lift a reified @[G] lhs ~# rhs@ precondition into a 'GuardResult' check.
obsEqGuard ::
    forall env g.
    Int ->
    Int ->
    (Int -> g -> IO ObsTree) ->
    (env -> g) ->
    (env -> g) ->
    env ->
    IO GuardResult
obsEqGuard tmoUs depth approxG gLhs gRhs env = do
    let d = max 2 depth
        tNat = fromIntegral (max 1 tmoUs)
        dNat = fromIntegral d
    tL <- evalObsSample tmoUs approxG d (gLhs env)
    tR <- evalObsSample tmoUs approxG d (gRhs env)
    pure $ case compareObsTree dNat tNat tL tR of
        ObsEqual -> GuardHolds
        ObsApart -> GuardFails
        ObsUnknown r -> GuardUnknown r

-- | Short-circuiting conjunction of two 'GuardResult' checks.
obsAndGuard :: forall env. (env -> IO GuardResult) -> (env -> IO GuardResult) -> env -> IO GuardResult
obsAndGuard g1 g2 env = do
    r1 <- g1 env
    case r1 of
        GuardHolds -> g2 env
        other -> pure other

-- ---------------------------------------------------------------------------
-- Runtime Observational Test Loops (Value, Projection, and Relation)
-- ---------------------------------------------------------------------------

{- | Compute the three-valued 'ObsVerdict' across a sample schedule without
custom guards or baseline sweeps.
-}
evalObsVerdict ::
    forall env r.
    ObsConfig ->
    (Int -> Gen env) ->
    (env -> [env]) ->
    (Int -> r -> IO ObsTree) ->
    (env -> r) ->
    (env -> r) ->
    IO (ObsVerdict env)
evalObsVerdict cfg = evalObsVerdictFull cfg Nothing obsAlwaysHolds

evalObsVerdictFull ::
    forall env r.
    ObsConfig ->
    Maybe (Int -> Gen env) ->
    (env -> IO GuardResult) ->
    (Int -> Gen env) ->
    (env -> [env]) ->
    (Int -> r -> IO ObsTree) ->
    (env -> r) ->
    (env -> r) ->
    IO (ObsVerdict env)
evalObsVerdictFull cfg mbBaseline checkGuard mkEnvGen shrinkEnv approxR evalLhs evalRhs = do
    let nTests = max 1 (fromIntegral (obsTests cfg) :: Int)
        maxAttempts = 10 * nTests
        maxSz = max 0 (fromIntegral (obsMaxSize cfg) :: Int)
        depth = max 1 (fromIntegral (obsApproxDepth cfg) :: Int)
        depthNat = max 1 (obsApproxDepth cfg)
        partPct = min 100 (max 0 (fromIntegral (obsPartialPct cfg) :: Int))
        tmoUs = max 1 (fromIntegral (obsTimeoutUs cfg) :: Int)
        tmoNat = max 1 (obsTimeoutUs cfg)
        seed0 = fromIntegral (obsSeed cfg) :: Word64
        totalGen = mkEnvGen 0
        partialGen = mkEnvGen partPct
        shallowTmo = min 500 tmoUs
        nBaseline = case mbBaseline of
            Nothing -> 0
            Just _ -> min 16 (max 4 (nTests `quot` 5))

        testEnv :: env -> IO (ObsCmp, ObsTree, ObsTree)
        testEnv env = do
            let valL = evalLhs env
                valR = evalRhs env
            if depth <= 2
                then do
                    tL <- evalObsSample tmoUs approxR depth valL
                    tR <- evalObsSample tmoUs approxR depth valR
                    pure (compareObsTree depthNat tmoNat tL tR, tL, tR)
                else do
                    tL2 <- evalObsSample shallowTmo approxR 2 valL
                    tR2 <- evalObsSample shallowTmo approxR 2 valR
                    case compareObsTree 2 (fromIntegral (max 1 shallowTmo)) tL2 tR2 of
                        ObsEqual -> pure (ObsEqual, tL2, tR2)
                        ObsApart -> pure (ObsApart, tL2, tR2)
                        ObsUnknown _ -> do
                            tL <- evalObsSample tmoUs approxR depth valL
                            tR <- evalObsSample tmoUs approxR depth valR
                            pure (compareObsTree depthNat tmoNat tL tR, tL, tR)

        shrinkLoop :: Int -> env -> (ObsTree, ObsTree) -> IO (Int, env, (ObsTree, ObsTree))
        shrinkLoop steps cur bestTrees
            | steps >= 64 = pure (steps, cur, bestTrees)
            | otherwise = safeShrinkTake 32 shrinkEnv cur >>= findSmaller
          where
            findSmaller [] = pure (steps, cur, bestTrees)
            findSmaller (cand : rest) = do
                gRes <- checkGuard cand
                case gRes of
                    GuardHolds -> do
                        (cmp, tL', tR') <- testEnv cand
                        case cmp of
                            ObsApart -> shrinkLoop (steps + 1) cand (tL', tR')
                            _ -> findSmaller rest
                    _ -> findSmaller rest

        baselineLoop :: (Int -> Gen env) -> Int -> Maybe InconclusiveReason -> IO (Either (ObsVerdict env) (Maybe InconclusiveReason))
        baselineLoop baseGen bIdx mbUnknown
            | bIdx >= nBaseline = pure (Right mbUnknown)
            | otherwise = do
                let sz = bIdx `rem` 4
                    usePartial = partPct > 0 && bIdx >= 4 && ((bIdx * 37 + 13) `rem` 100 < partPct)
                    g = if usePartial then baseGen partPct else baseGen 0
                    env = runGenAt (seed0 `xor` 0x9e3779b9) bIdx sz g
                gRes <- checkGuard env
                case gRes of
                    GuardFails -> baselineLoop baseGen (bIdx + 1) mbUnknown
                    GuardUnknown r -> baselineLoop baseGen (bIdx + 1) (keepFirstUnknown mbUnknown r)
                    GuardHolds -> do
                        (cmp, tL, tR) <- testEnv env
                        case cmp of
                            ObsEqual -> baselineLoop baseGen (bIdx + 1) mbUnknown
                            ObsUnknown r -> baselineLoop baseGen (bIdx + 1) (keepFirstUnknown mbUnknown r)
                            ObsApart -> do
                                (shrunkSteps, minEnv, (minL, minR)) <- shrinkLoop 0 env (tL, tR)
                                pure (Left (Refuted (bIdx + 1) shrunkSteps minEnv minL minR))

        mainLoop :: Int -> Int -> Maybe InconclusiveReason -> IO (ObsVerdict env)
        mainLoop passed attempts mbUnknown
            | passed >= nTests =
                pure $ case mbUnknown of
                    Nothing -> Verified
                    Just reason -> Inconclusive reason
            | attempts >= maxAttempts =
                pure (Inconclusive (InsufficientPreconditionHits (fromIntegral passed) (obsTests cfg)))
            | otherwise = do
                let sz = sampleScheduleSize passed nTests maxSz
                    usePartial = partPct > 0 && passed >= 5 && ((attempts * 37 + 13) `rem` 100 < partPct)
                    chosenGen = if usePartial then partialGen else totalGen
                    env = runGenAt seed0 attempts sz chosenGen
                gRes <- checkGuard env
                case gRes of
                    GuardFails -> mainLoop passed (attempts + 1) mbUnknown
                    GuardUnknown r -> mainLoop (passed + 1) (attempts + 1) (keepFirstUnknown mbUnknown r)
                    GuardHolds -> do
                        (cmp, tL, tR) <- testEnv env
                        case cmp of
                            ObsEqual -> mainLoop (passed + 1) (attempts + 1) mbUnknown
                            ObsUnknown r -> mainLoop (passed + 1) (attempts + 1) (keepFirstUnknown mbUnknown r)
                            ObsApart -> do
                                (shrunkSteps, minEnv, (minL, minR)) <- shrinkLoop 0 env (tL, tR)
                                pure (Refuted (passed + 1) shrunkSteps minEnv minL minR)

    case mbBaseline of
        Nothing -> mainLoop 0 0 Nothing
        Just baseGen -> do
            pre <- baselineLoop baseGen 0 Nothing
            case pre of
                Left verdict -> pure verdict
                Right mbUnk -> mainLoop 0 0 mbUnk

keepFirstUnknown :: Maybe InconclusiveReason -> InconclusiveReason -> Maybe InconclusiveReason
keepFirstUnknown Nothing r = Just r
keepFirstUnknown (Just prev) _ = Just prev

safeShrinkTake :: Int -> (env -> [env]) -> env -> IO [env]
safeShrinkTake limit shrinkFn cur = step limit (shrinkFn cur)
  where
    step 0 _ = pure []
    step k xs0 = do
        mbCons <-
            ( do
                xs <- evaluate xs0
                pure $ case xs of
                    [] -> Just Nothing
                    y : ys -> Just (Just (y, ys))
            )
                `catch` \(exn :: SomeException) ->
                    case fromException exn :: Maybe SomeAsyncException of
                        Just asyncExn -> throwIO asyncExn
                        Nothing -> pure Nothing
        case mbCons of
            Just (Just (y, ys)) -> (y :) <$> step (k - 1) ys
            _ -> pure []

-- See Note [Linear size stratification and non-geometric constructor choice].
sampleScheduleSize :: Int -> Int -> Int -> Int
sampleScheduleSize idx nTests maxSz
    | maxSz <= 0 = 0
    | nTests <= 1 = maxSz
    | idx <= 0 = 0
    | idx >= nTests - 1 = maxSz
    | nTests <= maxSz = (idx * maxSz) `quot` (nTests - 1)
    | otherwise = min maxSz ((idx * (maxSz + 1)) `quot` nTests)

formatRefuted :: (env -> String) -> String -> String -> Int -> Int -> env -> ObsTree -> ObsTree -> String
formatRefuted showEnv lhsLabel rhsLabel sampleNum shrunkSteps minEnv minL minR =
    let envStr = showEnv minEnv
        bindsPart = if null envStr then "closed sample" else envStr
     in "FAIL:after "
            ++ show sampleNum
            ++ " test(s)"
            ++ (if shrunkSteps > 0 then " and " ++ show shrunkSteps ++ " shrink(s)" else "")
            ++ ": "
            ++ bindsPart
            ++ " gives "
            ++ lhsLabel
            ++ " = "
            ++ renderObsTree minL
            ++ ", "
            ++ rhsLabel
            ++ " = "
            ++ renderObsTree minR

-- | Execute the bounded value-equality test loop for 'ObsEq'.
runObsTestLoop ::
    forall env r.
    ObsConfig ->
    -- | Optional baseline boundary-sweep generator for unguarded custom domains.
    Maybe (Int -> Gen env) ->
    -- | Reified Given precondition and domain predicate guard.
    (env -> IO GuardResult) ->
    -- | Environment generator parameterized by partiality percentage @[0..100]@.
    (Int -> Gen env) ->
    -- | Environment shrinker.
    (env -> [env]) ->
    -- | Environment pretty-printer.
    (env -> String) ->
    -- | Bounded Kleene approximation on @r@.
    (Int -> r -> IO ObsTree) ->
    -- | Left-hand side evaluator.
    (env -> r) ->
    -- | Right-hand side evaluator.
    (env -> r) ->
    IO String
runObsTestLoop cfg mbBase checkGuard mkEnvGen shrinkEnv showEnv approxR evalLhs evalRhs = do
    verdict <- evalObsVerdictFull cfg mbBase checkGuard mkEnvGen shrinkEnv approxR evalLhs evalRhs
    pure $ case verdict of
        Verified -> "PASS"
        Inconclusive reason -> "INCONCLUSIVE:" ++ show reason
        Refuted sampleNum shrunkSteps minEnv minL minR ->
            formatRefuted showEnv "lhs" "rhs" sampleNum shrunkSteps minEnv minL minR

-- | Execute the bounded projection-equality test loop for 'ObsEqOn'.
runObsOnLoop ::
    forall env a rep.
    ObsConfig ->
    Maybe (Int -> Gen env) ->
    (env -> IO GuardResult) ->
    (Int -> Gen env) ->
    (env -> [env]) ->
    (env -> String) ->
    -- | Bounded Kleene approximation on projected representation @rep@.
    (Int -> rep -> IO ObsTree) ->
    -- | Observation projection @proj@.
    (a -> rep) ->
    -- | Left-hand side evaluator.
    (env -> a) ->
    -- | Right-hand side evaluator.
    (env -> a) ->
    IO String
runObsOnLoop cfg mbBase checkGuard mkEnvGen shrinkEnv showEnv approxRep proj evalLhs evalRhs = do
    verdict <-
        evalObsVerdictFull
            cfg
            mbBase
            checkGuard
            mkEnvGen
            shrinkEnv
            approxRep
            (proj . evalLhs)
            (proj . evalRhs)
    pure $ case verdict of
        Verified -> "PASS"
        Inconclusive reason -> "INCONCLUSIVE:" ++ show reason
        Refuted sampleNum shrunkSteps minEnv minL minR ->
            formatRefuted showEnv "proj lhs" "proj rhs" sampleNum shrunkSteps minEnv minL minR

data ByFailure
    = ByPrimaryFalse !ObsTree
    | ByReflLhsFalse
    | ByReflRhsFalse
    | BySymFalse

{- | Execute the bounded equivalence-relation test loop for 'ObsEqBy', checking
primary relation truth alongside endpoint reflexivity and symmetry.
-}
runObsByLoop ::
    forall env a.
    ObsConfig ->
    Maybe (Int -> Gen env) ->
    (env -> IO GuardResult) ->
    (Int -> Gen env) ->
    (env -> [env]) ->
    (env -> String) ->
    -- | Source name of relation @rel@ for diagnostics.
    String ->
    -- | Candidate boolean equivalence relation @rel@.
    (a -> a -> Bool) ->
    (env -> a) ->
    (env -> a) ->
    IO String
runObsByLoop cfg mbBase checkGuard mkEnvGen shrinkEnv showEnv relName relFn evalLhs evalRhs = do
    let nTests = max 1 (fromIntegral (obsTests cfg) :: Int)
        maxAttempts = 10 * nTests
        maxSz = max 0 (fromIntegral (obsMaxSize cfg) :: Int)
        partPct = min 100 (max 0 (fromIntegral (obsPartialPct cfg) :: Int))
        tmoUs = max 1 (fromIntegral (obsTimeoutUs cfg) :: Int)
        tmoNat = max 1 (obsTimeoutUs cfg)
        seed0 = fromIntegral (obsSeed cfg) :: Word64
        totalGen = mkEnvGen 0
        partialGen = mkEnvGen partPct
        nBaseline = case mbBase of
            Nothing -> 0
            Just _ -> min 16 (max 4 (nTests `quot` 5))

        evalBool :: Bool -> IO ObsTree
        evalBool b = evalObsSample tmoUs obsApprox 2 b

        checkSample :: env -> IO (Either InconclusiveReason (Maybe ByFailure))
        checkSample env = do
            let vL = evalLhs env
                vR = evalRhs env
            tLR <- evalBool (relFn vL vR)
            case tLR of
                ObsTimedOut -> pure (Left (TimeoutReached tmoNat))
                ObsCutoff -> pure (Left (DepthCutoffReached 2))
                ObsCon "False" [] -> pure (Right (Just (ByPrimaryFalse tLR)))
                ObsRaisedBottom _ -> pure (Right (Just (ByPrimaryFalse tLR)))
                ObsRaisedSyncError -> pure (Right (Just (ByPrimaryFalse tLR)))
                ObsCon "True" [] -> do
                    tRL <- evalBool (relFn vR vL)
                    tLL <- evalBool (relFn vL vL)
                    tRR <- evalBool (relFn vR vR)
                    pure $ checkLaws tRL tLL tRR
                _ -> pure (Left SyncExceptionRaised)

        checkLaws :: ObsTree -> ObsTree -> ObsTree -> Either InconclusiveReason (Maybe ByFailure)
        checkLaws tRL tLL tRR
            | ObsCon "False" [] <- tRL = Right (Just BySymFalse)
            | ObsCon "False" [] <- tLL = Right (Just ByReflLhsFalse)
            | ObsCon "False" [] <- tRR = Right (Just ByReflRhsFalse)
            | any (== ObsTimedOut) [tRL, tLL, tRR] = Left (TimeoutReached tmoNat)
            | any (== ObsRaisedSyncError) [tRL, tLL, tRR] = Left SyncExceptionRaised
            | otherwise = Right Nothing

        sameKindFailure :: ByFailure -> ByFailure -> Bool
        sameKindFailure (ByPrimaryFalse _) (ByPrimaryFalse _) = True
        sameKindFailure ByReflLhsFalse ByReflLhsFalse = True
        sameKindFailure ByReflRhsFalse ByReflRhsFalse = True
        sameKindFailure BySymFalse BySymFalse = True
        sameKindFailure _ _ = False

        shrinkBy :: Int -> env -> ByFailure -> IO (Int, env, ByFailure)
        shrinkBy steps cur fail0
            | steps >= 64 = pure (steps, cur, fail0)
            | otherwise = safeShrinkTake 32 shrinkEnv cur >>= tryCands
          where
            tryCands [] = pure (steps, cur, fail0)
            tryCands (cand : rest) = do
                gRes <- checkGuard cand
                case gRes of
                    GuardHolds -> do
                        res <- checkSample cand
                        case res of
                            Right (Just fail1)
                                | sameKindFailure fail0 fail1 ->
                                    shrinkBy (steps + 1) cand fail1
                            _ -> tryCands rest
                    _ -> tryCands rest

        renderByFailure :: Int -> Int -> env -> ByFailure -> String
        renderByFailure sampleNum shrunkSteps minEnv failure =
            let envStr = showEnv minEnv
                bindsPart = if null envStr then "closed sample" else envStr
             in case failure of
                    ByPrimaryFalse t ->
                        "FAIL:after "
                            ++ show sampleNum
                            ++ " test(s)"
                            ++ (if shrunkSteps > 0 then " and " ++ show shrunkSteps ++ " shrink(s)" else "")
                            ++ ": "
                            ++ bindsPart
                            ++ " gives rel lhs rhs = "
                            ++ renderObsTree t
                    BySymFalse ->
                        "FAIL:relation '"
                            ++ relName
                            ++ "' failed symmetry at "
                            ++ bindsPart
                            ++ ": rel lhs rhs = True, rel rhs lhs = False"
                    ByReflLhsFalse ->
                        "FAIL:relation '"
                            ++ relName
                            ++ "' failed reflexivity at "
                            ++ bindsPart
                            ++ ": rel lhs lhs = False"
                    ByReflRhsFalse ->
                        "FAIL:relation '"
                            ++ relName
                            ++ "' failed reflexivity at "
                            ++ bindsPart
                            ++ ": rel rhs rhs = False"

        baseLoop :: (Int -> Gen env) -> Int -> Maybe InconclusiveReason -> IO (Either String (Maybe InconclusiveReason))
        baseLoop baseGen bIdx mbUnk
            | bIdx >= nBaseline = pure (Right mbUnk)
            | otherwise = do
                let sz = bIdx `rem` 4
                    usePartial = partPct > 0 && bIdx >= 4 && ((bIdx * 37 + 13) `rem` 100 < partPct)
                    g = if usePartial then baseGen partPct else baseGen 0
                    env = runGenAt (seed0 `xor` 0x9e3779b9) bIdx sz g
                gRes <- checkGuard env
                case gRes of
                    GuardFails -> baseLoop baseGen (bIdx + 1) mbUnk
                    GuardUnknown r -> baseLoop baseGen (bIdx + 1) (keepFirstUnknown mbUnk r)
                    GuardHolds -> do
                        sRes <- checkSample env
                        case sRes of
                            Left r -> baseLoop baseGen (bIdx + 1) (keepFirstUnknown mbUnk r)
                            Right Nothing -> baseLoop baseGen (bIdx + 1) mbUnk
                            Right (Just f0) -> do
                                (sh, minE, minF) <- shrinkBy 0 env f0
                                pure (Left (renderByFailure (bIdx + 1) sh minE minF))

        loop :: Int -> Int -> Maybe InconclusiveReason -> IO String
        loop passed attempts mbUnk
            | passed >= nTests =
                pure $ case mbUnk of
                    Nothing -> "PASS"
                    Just r -> "INCONCLUSIVE:" ++ show r
            | attempts >= maxAttempts =
                pure ("INCONCLUSIVE:" ++ show (InsufficientPreconditionHits (fromIntegral passed) (obsTests cfg)))
            | otherwise = do
                let sz = sampleScheduleSize passed nTests maxSz
                    usePartial = partPct > 0 && passed >= 5 && ((attempts * 37 + 13) `rem` 100 < partPct)
                    baseGen = if usePartial then partialGen else totalGen
                    env = runGenAt seed0 attempts sz baseGen
                gRes <- checkGuard env
                case gRes of
                    GuardFails -> loop passed (attempts + 1) mbUnk
                    GuardUnknown r -> loop (passed + 1) (attempts + 1) (keepFirstUnknown mbUnk r)
                    GuardHolds -> do
                        sRes <- checkSample env
                        case sRes of
                            Left r -> loop (passed + 1) (attempts + 1) (keepFirstUnknown mbUnk r)
                            Right Nothing -> loop (passed + 1) (attempts + 1) mbUnk
                            Right (Just f0) -> do
                                (sh, minE, minF) <- shrinkBy 0 env f0
                                pure (renderByFailure (passed + 1) sh minE minF)

    case mbBase of
        Nothing -> loop 0 0 Nothing
        Just baseGen -> do
            pre <- baseLoop baseGen 0 Nothing
            case pre of
                Left err -> pure err
                Right mbUnk -> loop 0 0 mbUnk

-- ---------------------------------------------------------------------------
-- Core Synthesis Combinators
-- ---------------------------------------------------------------------------

-- | Unconstrained 'pure' for 'Gen', used by plugin Core synthesis.
obsPureGen :: a -> Gen a
obsPureGen = pure

-- | Unconstrained '(<*>)' for 'Gen', used by plugin Core synthesis.
obsApGen :: Gen (a -> b) -> Gen a -> Gen b
obsApGen = (<*>)

-- | Apply a constructor generator to a branching field generator at half size.
obsApHalfGen :: Gen (a -> b) -> Gen a -> Gen b
obsApHalfGen gf gx = gf <*> sized (\sz -> resize (sz `quot` 2) gx)

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

-- | Unconstrained 'map', used by synthesized ADT field shrinkers.
obsMapList :: (a -> b) -> [a] -> [b]
obsMapList = map

{- | Combine two partiality-parameterized generators into a pair generator
with axis-isolated boundary splits and full-size axis probes.
-}
obsPairGen :: (Int -> Gen a) -> (Int -> Gen b) -> Int -> Gen (a, b)
obsPairGen ga gb pct = Gen $ \s sz ->
    let (s0, sRest) = splitSeed s
        (s1, s2) = splitSeed sRest
        (w, _) = stepSeed s0
        half = sz `quot` 2
        (szA, szB) =
            case w .&. 7 of
                1 -> (sz, 0)
                2 -> (0, sz)
                3 -> (sz, half)
                4 -> (half, sz)
                _ -> (half, sz - half)
     in (unGen (ga pct) s1 szA, unGen (gb pct) s2 szB)

{- | Combine two component shrinkers into a pair shrinker with a bounded
@4 x 4@ diagonal suffix for coupled multi-argument invariants.
-}
obsPairShrink :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
obsPairShrink sa sb (x, y) =
    let xs = sa x
        ys = sb y
     in [(x', y) | x' <- xs]
            ++ [(x, y') | y' <- ys]
            ++ [(x', y') | x' <- take 4 xs, y' <- take 4 ys]

-- | Combine two component printers into a comma-separated environment string.
obsPairShow :: (a -> String) -> (b -> String) -> (a, b) -> String
obsPairShow pa pb (x, y) = pa x ++ ", " ++ pb y

-- | Prefix a rendered variable value with its source binder name.
obsNamedShow :: String -> (a -> String) -> a -> String
obsNamedShow nm pa x = nm ++ " = " ++ pa x
