# dependent-obs-eq

`dependent-obs-eq` provides a GHC typechecker plugin (`Dependent.Plugin.ObsEq`) and combinator library (`Dependent.ObsEq`) for counterexample refutation, constructive Knuth-Bendix equational completion, and explicit observational-equivalence witnesses in Dependent Haskell (`-XDependentTypes`).

## Attribution

Based on the observational-equivalence / QuickCheck `TcPlugin` idea proposed by **Jules (@analytichegel)**.

## Installation

`dependent-obs-eq` is published on [`dependent.head.hackage`](https://cdn.tharkun.se/dependent-hackage/) for Dependent Haskell (`ghc-10.1`). Add `head.hackage.ghc.haskell.org` and `dependent.head.hackage` to `cabal.project`:

```cabal
repository head.hackage.ghc.haskell.org
  url: https://ghc.gitlab.haskell.org/head.hackage/
  secure: True
  key-threshold: 3
  root-keys:
    f76d08be13e9a61a377a85e2fb63f4c5435d40f8feb3e12eb05905edb8cdea89
    26021a13b401500c8eb2761ca95c61f2d625bfef951b939a8124ed12ecf07329
    7541f32a4ccca4f97aea3b22f5e593ba2c0267546016b992dfadcd2fe944e55d

repository dependent.head.hackage
  url: https://cdn.tharkun.se/dependent-hackage/
  secure: True
  key-threshold: 3
  root-keys:
    1ad4d9522ed07750746d4c5fca5fe2dc72f47ba643f9eb337a7b332cb50db4c3
    650abe1aaf95bfe819c0b6d5f41f756ac71652ea3e62064ad4eb00805bcec45d
    fc14639fb76e8b8d3e6b9fcfbdc16c8a095483438642a8291a6da37c8d9643cb

active-repositories:
  hackage.haskell.org,
  head.hackage.ghc.haskell.org:merge,
  dependent.head.hackage:override
```

Fetch the overlay index, add `dependent-obs-eq >= 0.2 && < 0.3` to `build-depends`, and build with a Stage 1 Dependent Haskell compiler:

```sh
cabal update dependent.head.hackage
cabal build -w /path/to/ghc/_build/stage1/bin/ghc
```

## Scope, Completion, and Policies

In Dependent Haskell, structurally recursive functions (`plus`, `appendList`) publish certified closed type-family equations (`SourceTable`) that GHC reduces directly on constructor heads. Use deductive proofs or `dependent-proof-search` when structural equations hold by induction.

Non-structural definitions—tail-recursive accumulators (`accPlus`, `revAcc`), coalgebraic state loops (`unfoldPlus`), fuel-free recursion, and canonicalizing container operations—do not emit outer structural equations because recursive calls accumulate into a state parameter or hide inside a local helper. As a result, an indexed type such as `Vec a (accPlus m n)` does not unify definitionally with `Vec a (plus m n)` on open variables `m` and `n`.

`Dependent.Plugin.ObsEq` handles open equalities in three stages:

1. **Constructive zero-`UnivCo` equational completion**: Before compiling bytecode, `Dependent.Plugin.ObsEq.Rewrite` runs triangular variable unification, constructor decomposition, and bounded unfailing Knuth-Bendix completion (KBO) over in-scope Given equalities and reachable certified `SourceTable` axioms. When Givens algebraically entail the goal, the plugin emits a pure System FC coercion (`SymCo`, `TransCo`, `TyConAppCo`, `AxiomCo`, `SelCo`) with zero `UnivCo` axioms and zero bytecode evaluations.
2. **Automatic counterexample refutation**: When a Wanted nominal equality `[W] lhs ~# rhs` remains stuck, the plugin evaluates bounded three-valued Kleene constructor approximations (`ObsTree`) over total inputs and synthetic partial demand probes (`ObsBottom`). When a sample distinguishes `lhs` and `rhs`, the plugin shrinks the input (including `4 x 4` diagonal coupled pair shrinking) and reports the minimal counterexample at the source span.
3. **Explicit observational witnesses**: Under the default `ExplicitOnly` policy (`policy=explicit`), explicit constraints (`ObsEq`, `ObsEqOn`, `ObsEqBy`) discharge `obsEq`, `checkObsEq`, `obsEqOn`, `checkObsEqOn`, `obsEqBy`, and `checkObsEqBy` when Kleene testing verifies the equation across the configured domain. Under `RefuteOnly` (`policy=refute-only`), the plugin runs constructive KBO completion and counterexample refutation only and never emits `UnivCo`. Under `ImplicitAssume` (`policy=assume`), verified bare nominal equalities are also discharged.

Resource cutoffs (`ObsCutoff`), timeouts and 64 MiB per-sample allocation limits (`ObsTimedOut`), double synchronous exceptions (`ObsRaisedSyncError`), insufficient precondition hits, and polymorphic class constraints (`PolymorphicClassConstraint`) return `Inconclusive` and never emit nominal coercions.

## Self-Contained Examples

Each example below is a complete module that compiles on its own with `-fplugin=Dependent.Plugin.ObsEq`. The examples define `Nat` and `Vec` inline so they depend only on `base` and `dependent-obs-eq`; `Nat`, `plus`, and `Vec` from `dependent-base` (`Data.Nat.Dependent` and `Data.Vec.Dependent`) work identically.

### 1. Non-Structural Functions, Indexed Transport, and Constructive Completion

`plus` recurses structurally on its first argument, whereas `unfoldPlus` steps through a `Maybe Nat` state and `accPlus` and `revAcc` accumulate into a second argument:

- `unfoldPlus` emits outer `Succ` constructors lazily as it consumes `m`, matching `plus` on both total values and partial spines (`ObsBottom`). Default `obsEq` injects partial thunks in 25% of samples (`partial-pct=25`) and verifies lazy equivalence.
- `accPlus` forces the entire spine of `m` before returning any constructor (`plus (Succ bottom) n` produces `Succ (plus bottom n)`, whereas `accPlus (Succ bottom) n` diverges at the root). Default `obsEq` refutes `accPlus m n :~: plus m n` on partial inputs; `totalObsConfig` sets `partial-pct=0` to test total inputs.
- When the target type constructor is matchable (such as `Vec Int`), `castEq` infers the context and both index endpoints without `@` type applications. Passing a monomorphic index witness `accPlusLaw m n` to `castEq` or `usingEq` transports `Vec a` polymorphically in `a`.
- When an equation such as `accPlus m n ~ plus m n` is already in scope as a Given constraint, constructive KBO + `SourceTable` completion proves algebraic consequences such as `Succ (accPlus m n) :~: plus (Succ m) n` directly on bare `Refl` with zero `UnivCo` axioms (including under `policy=refute-only`).

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module NonStructuralTransport where

import Data.Type.Equality ((:~:) (Refl))
import Dependent.ObsEq (
    castEq,
    checkObsEq,
    obsEq,
    setTests,
    totalObsConfig,
    usingEq,
 )

data Nat = Zero | Succ Nat
    deriving (Eq, Show)

data Vec a (n :: Nat) where
    VNil :: Vec a Zero
    VCons :: a -> Vec a n -> Vec a (Succ n)

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc = acc
    step (Just Zero) acc = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc = acc
    go (Succ k) acc = go k (Succ acc)

appendList :: [a] -> [a] -> [a]
appendList [] ys = ys
appendList (x : xs) ys = x : appendList xs ys

revSpec :: [a] -> [a]
revSpec [] = []
revSpec (x : xs) = appendList (revSpec xs) [x]

revAcc :: [a] -> [a] -> [a]
revAcc [] acc = acc
revAcc (x : xs) acc = revAcc xs (x : acc)

-- Lazy equivalence (including partial ObsBottom spines):
unfoldPlusLaw :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusLaw _m _n = obsEq

-- Total equivalence on accumulator functions (partial-pct=0):
accPlusLaw :: foreach (m :: Nat) (n :: Nat) -> accPlus m n :~: plus m n
accPlusLaw _m _n = checkObsEq (setTests 80 totalObsConfig)

revAccLaw :: foreach (xs :: [a]) -> revAcc xs '[] :~: revSpec xs
revAccLaw _xs = checkObsEq totalObsConfig

-- Zero-annotation transport across matchable Vec Int:
toAccVec ::
    foreach (m :: Nat) (n :: Nat) ->
    Vec Int (plus m n) ->
    Vec Int (accPlus m n)
toAccVec _m _n v = castEq (checkObsEq (setTests 80 totalObsConfig)) v

-- Polymorphic transport in `a` via `castEq` or `usingEq`:
fromAccVec ::
    foreach (m :: Nat) (n :: Nat) ->
    Vec a (accPlus m n) ->
    Vec a (plus m n)
fromAccVec m n v = castEq (accPlusLaw m n) v

fromAccVecUsing ::
    foreach (m :: Nat) (n :: Nat) ->
    Vec a (accPlus m n) ->
    Vec a (plus m n)
fromAccVecUsing m n v = usingEq (accPlusLaw m n) v

-- Constructive zero-UnivCo KBO + SourceTable proof from a Given equality:
succAccStep ::
    foreach (m :: Nat) (n :: Nat) ->
    (accPlus m n ~ plus m n) =>
    Succ (accPlus m n) :~: plus (Succ m) n
succAccStep _m _n = Refl
```

### 2. Preconditions and Invariant-Preserving `ObsDomain` Overrides

State partial-domain preconditions explicitly as Given constraints (such as `isEvenNat n ~ True` or `isEvenInt n ~ True`) so out-of-domain call sites fail statically. Pair preconditions with `ObsDomain` overrides (`forVar` for a specific `foreach` binder, or `forType` for every binder of that type) so generated and shrunk samples satisfy the invariant without rejection starvation. `domainVia build unbuild` generates and shrinks values through an unconstrained `ObsGen` proxy (`domain`, `domainGen`, and `domainSuchThat` cover custom generators and predicate filters):

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module GuardedDomains where

import Data.Type.Equality ((:~:))
import Dependent.ObsEq (
    ObsDomain,
    ObsGen,
    checkObsEq,
    domainVia,
    forVar,
    totalObsConfig,
 )
import GHC.Generics (Generic)

data Nat = Zero | Succ Nat
    deriving (Eq, Show, Generic)

instance ObsGen Nat

notBool :: Bool -> Bool
notBool False = True
notBool True = False

isEvenNat :: Nat -> Bool
isEvenNat Zero = True
isEvenNat (Succ n) = notBool (isEvenNat n)

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

halfNat :: Nat -> Nat
halfNat Zero = Zero
halfNat (Succ Zero) = Zero
halfNat (Succ (Succ n)) = Succ (halfNat n)

twiceHalfNat :: Nat -> Nat
twiceHalfNat n
    | isEvenNat n = plus (halfNat n) (halfNat n)
    | otherwise = error "twiceHalfNat: odd input"

evenNatDomain :: ObsDomain Nat
evenNatDomain = domainVia (\k -> plus k k) halfNat

evenNatRoundtrip :: foreach (n :: Nat) -> (isEvenNat n ~ True) => twiceHalfNat n :~: n
evenNatRoundtrip n = checkObsEq (forVar n evenNatDomain totalObsConfig)

isEvenInt :: Int -> Bool
isEvenInt n = n `rem` 2 == 0

twiceHalfEven :: Int -> Int
twiceHalfEven n
    | isEvenInt n = (n `quot` 2) * 2
    | otherwise = error "twiceHalfEven: odd input"

evenIntDomain :: ObsDomain Int
evenIntDomain = domainVia (* 2) (`quot` 2)

evenIntRoundtrip :: foreach (n :: Int) -> (isEvenInt n ~ True) => twiceHalfEven n :~: n
evenIntRoundtrip n = checkObsEq (forVar n evenIntDomain totalObsConfig)
```

### 3. Sound Canonical Projections (`ObsEquivOn`) and Quotient Lifting (`liftObsEqOn`)

Two search trees `insertBST Zero (insertBST (Succ Zero) Empty)` and `insertBST (Succ Zero) (insertBST Zero Empty)` contain the same sorted elements (`toAscList`) but have distinct root keys (`Succ Zero` vs `Zero`). Forging `t1 :~: t2` from projection agreement would be unsound in System FC because pattern matching on internal constructors distinguishes `t1` and `t2`.

`obsEqOn` and `checkObsEqOn` return `ObsEquivOn proj lhs rhs`, a newtype around `proj lhs :~: proj rhs` (`projectEq`) equipped with `reflObsOn`, `symObsOn`, `transObsOn`, and `castEqOn`. Operations `f` that commute with a canonicalizer `reify` (`f (reify (proj t)) :~: f t`, such as `sizeBST` under `fromListBST . toAscList`) lift constructively across `ObsEquivOn` via `liftObsEqOn`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module CanonicalProjections where

import Data.Type.Equality ((:~:) (Refl))
import Dependent.ObsEq (
    ObsDomain,
    ObsEquivOn (projectEq),
    ObsGen,
    castEqOn,
    checkObsEq,
    checkObsEqOn,
    domainVia,
    forType,
    forVar,
    liftObsEqOn,
    setTests,
    totalObsConfig,
 )
import GHC.Generics (Generic)

data Nat = Zero | Succ Nat
    deriving (Eq, Show, Generic)

instance ObsGen Nat

notBool :: Bool -> Bool
notBool False = True
notBool True = False

andBool :: Bool -> Bool -> Bool
andBool False _ = False
andBool True b = b

leNat :: Nat -> Nat -> Bool
leNat Zero _ = True
leNat (Succ _) Zero = False
leNat (Succ m) (Succ n) = leNat m n

ltNat :: Nat -> Nat -> Bool
ltNat Zero n = notBool (leNat n Zero)
ltNat (Succ m) n = notBool (leNat n (Succ m))

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

appendNat :: [Nat] -> [Nat] -> [Nat]
appendNat [] ys = ys
appendNat (x : xs) ys = x : appendNat xs ys

data BST = Empty | Node BST Nat BST
    deriving (Eq, Show)

ifBST :: Bool -> BST -> BST -> BST
ifBST False _ b = b
ifBST True a _ = a

insertBST :: Nat -> BST -> BST
insertBST x Empty = Node Empty x Empty
insertBST x (Node l y r) =
    ifBST
        (ltNat x y)
        (Node (insertBST x l) y r)
        (ifBST (ltNat y x) (Node l y (insertBST x r)) (Node l y r))

fromListBST :: [Nat] -> BST
fromListBST [] = Empty
fromListBST (x : xs) = insertBST x (fromListBST xs)

toAscList :: BST -> [Nat]
toAscList Empty = []
toAscList (Node l x r) = appendNat (toAscList l) (x : toAscList r)

sizeBST :: BST -> Nat
sizeBST Empty = Zero
sizeBST (Node l _ r) = Succ (plus (sizeBST l) (sizeBST r))

allLt :: Nat -> BST -> Bool
allLt _ Empty = True
allLt b (Node l x r) = andBool (ltNat x b) (andBool (allLt b l) (allLt b r))

allGt :: Nat -> BST -> Bool
allGt _ Empty = True
allGt b (Node l x r) = andBool (ltNat b x) (andBool (allGt b l) (allGt b r))

isValidBST :: BST -> Bool
isValidBST Empty = True
isValidBST (Node l x r) =
    andBool (allLt x l) (andBool (allGt x r) (andBool (isValidBST l) (isValidBST r)))

bstDomain :: ObsDomain BST
bstDomain = domainVia fromListBST toAscList

insertComm ::
    foreach (x :: Nat) (y :: Nat) (t :: BST) ->
    (isValidBST t ~ True) =>
    ObsEquivOn toAscList (insertBST x (insertBST y t)) (insertBST y (insertBST x t))
insertComm _x _y _t =
    checkObsEqOn (forType bstDomain (setTests 60 totalObsConfig)) toAscList

insertPreservesBST ::
    foreach (x :: Nat) (t :: BST) ->
    (isValidBST t ~ True) =>
    isValidBST (insertBST x t) :~: True
insertPreservesBST _x t =
    checkObsEq (forVar t bstDomain (setTests 60 totalObsConfig))

sizeCanon ::
    foreach (t :: BST) ->
    (isValidBST t ~ True) =>
    sizeBST (fromListBST (toAscList t)) :~: sizeBST t
sizeCanon t =
    checkObsEq (forVar t bstDomain (setTests 60 totalObsConfig))

sizeInsertComm ::
    foreach (x :: Nat) (y :: Nat) (t :: BST) ->
    (isValidBST t ~ True) =>
    sizeBST (insertBST x (insertBST y t)) :~: sizeBST (insertBST y (insertBST x t))
sizeInsertComm x y t =
    case (insertPreservesBST y t, insertPreservesBST x t) of
        (Refl, Refl) ->
            case (insertPreservesBST x (insertBST y t), insertPreservesBST y (insertBST x t)) of
                (Refl, Refl) ->
                    liftObsEqOn
                        fromListBST
                        sizeBST
                        (sizeCanon (insertBST x (insertBST y t)))
                        (sizeCanon (insertBST y (insertBST x t)))
                        (insertComm x y t)

newtype SortedSummary (xs :: [Nat]) = SortedSummary Int

retagSummary ::
    foreach (x :: Nat) (y :: Nat) (t :: BST) ->
    (isValidBST t ~ True) =>
    SortedSummary (toAscList (insertBST x (insertBST y t))) ->
    SortedSummary (toAscList (insertBST y (insertBST x t)))
retagSummary x y t s = castEqOn (insertComm x y t) s

projectedListEq ::
    foreach (x :: Nat) (y :: Nat) (t :: BST) ->
    (isValidBST t ~ True) =>
    toAscList (insertBST x (insertBST y t)) :~: toAscList (insertBST y (insertBST x t))
projectedListEq x y t = projectEq (insertComm x y t)
```

### 4. Symmetric Equivalence Relations (`ObsEquivBy`)

`obsEqBy` and `checkObsEqBy` test equivalence under a binary boolean relation `rel :: a -> a -> Bool` and return `ObsEquivBy rel lhs rhs`, which wraps `rel lhs rhs :~: True` (`relEqTrue`) without forging `lhs :~: rhs`. On each sample, the plugin checks `rel lhs rhs` together with endpoint reflexivity (`rel lhs lhs`, `rel rhs rhs`) and symmetry (`rel rhs lhs`), rejecting non-symmetric relations such as `<=`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}

module EquivalenceRelations where

import Data.Type.Equality ((:~:))
import Dependent.ObsEq (
    ObsEquivBy (relEqTrue),
    checkObsEqBy,
    obsEqBy,
    totalObsConfig,
 )

data Nat = Zero | Succ Nat
    deriving (Eq, Show)

data TaggedNat = MkTaggedNat Bool Nat
    deriving (Eq, Show)

notBool :: Bool -> Bool
notBool False = True
notBool True = False

eqBool :: Bool -> Bool -> Bool
eqBool False b = notBool b
eqBool True b = b

tagOf :: TaggedNat -> Bool
tagOf (MkTaggedNat b _) = b

sameTag :: TaggedNat -> TaggedNat -> Bool
sameTag (MkTaggedNat b1 _) t2 = eqBool b1 (tagOf t2)

isEvenNat :: Nat -> Bool
isEvenNat Zero = True
isEvenNat (Succ n) = notBool (isEvenNat n)

eqMod2 :: Nat -> Nat -> Bool
eqMod2 Zero n = isEvenNat n
eqMod2 (Succ m) n = notBool (eqMod2 m n)

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc = acc
    step (Just Zero) acc = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- `eqMod2` inspects the full `Nat` spine, so test over total inputs:
doubleEvenMod2 :: foreach (n :: Nat) -> ObsEquivBy eqMod2 (plus n n) Zero
doubleEvenMod2 _n = checkObsEqBy totalObsConfig eqMod2

-- `sameTag` inspects only the outer tag, so default `obsEqBy` succeeds even
-- when the `Nat` payload contains partial `ObsBottom` thunks:
unfoldSameTag ::
    foreach (m :: Nat) (n :: Nat) ->
    ObsEquivBy sameTag (MkTaggedNat True (unfoldPlus m n)) (MkTaggedNat True (plus m n))
unfoldSameTag _m _n = obsEqBy sameTag

extractBoolEq :: foreach (n :: Nat) -> eqMod2 (plus n n) Zero :~: True
extractBoolEq n = relEqTrue (doubleEvenMod2 n)
```

## Configuration and Plugin Options

Per-witness configurations build on `defaultObsConfig` (`partial-pct=25`) or `totalObsConfig` (`partial-pct=0`) with `setTests`, `setMaxSize`, `setApproxDepth`, `setPartialPct`, `setTimeoutUs`, `setSeed`, `forType`, and `forVar`.

Module-wide defaults and discharge policies can also be set via `-fplugin-opt=Dependent.Plugin.ObsEq:<option>`:

| Option | Default | Meaning |
| --- | --- | --- |
| `tests=N` | `100` | Number of test samples per constraint |
| `max-size=S` | `20` | Maximum generator size parameter |
| `approx-depth=D` | `100` | Bounded Kleene constructor-tree depth |
| `partial-pct=P` | `25` | Percentage of samples seeded with `ObsBottom` thunks |
| `timeout-us=T` | `10000` | Microsecond timeout per side per sample |
| `seed=K` | `0` | Deterministic starting PRNG seed |
| `policy=refute-only\|explicit\|assume` | `explicit` | Constructive KBO proofs and counterexample refutation only (`refute-only`), also discharge explicit witnesses (`explicit`), or also discharge bare nominal equalities (`assume`) |
| `warn-assume` | off | Emit a diagnostic note when `policy=assume` discharges a bare nominal equality |

Same-module definitions execute as bytecode inside `hscInterp` and yield on every jump, and every sample runs under a 64 MiB thread-local allocation limit. When testing precompiled external modules that may enter zero-allocation infinite loops, compile those provider modules with `-fno-omit-yields` so `System.Timeout.timeout` preempts them cleanly.
