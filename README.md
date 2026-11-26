# dependent-obs-eq

`dependent-obs-eq` provides a GHC typechecker plugin (`Dependent.Plugin.ObsEq`) and combinator library (`Dependent.ObsEq`) for counterexample refutation and explicit observational-equivalence witnesses in Dependent Haskell (`-XDependentTypes`).

## Attribution

Based on the observational-equivalence / QuickCheck `TcPlugin` idea proposed by **Jules (@analytichegel)**.

## Scope and Design

In Dependent Haskell, structural functions publish certified closed type-family equations (`SourceTable`) that GHC reduces directly. Use inductive proofs or `dependent-proof-search` when structural equations hold deductively. Use `dependent-obs-eq` for two tasks:

1. **Automatic counterexample refutation**: When a nominal equality `[W] lhs ~# rhs` gets stuck on open terms, the plugin tests bounded three-valued Kleene approximations (`ObsTree`) over total and partially defined (`ObsBottom`) inputs. When a sample distinguishes `lhs` and `rhs`, the plugin shrinks the input and reports the minimal counterexample at the source span.
2. **Bridging non-structural equations at transport sites**: Accumulator-passing functions, unfold loops, fuel-free recursion, and abstract container operations do not emit structural `SourceTable` equations. Explicit witnesses (`obsEq`, `checkObsEq`, `obsEqOn`, `obsEqBy`) test the law over configured domains and supply evidence to transport combinators (`castEq`, `usingEq`, `castEqOn`, `liftObsEqOn`).

Before running bytecode samples, the plugin runs a constructive Knuth-Bendix and `SourceTable` completion pass over in-scope Given equalities. When Givens algebraically entail the goal, the plugin emits a pure System FC coercion (`SymCo`, `TransCo`, `TyConAppCo`, `AxiomCo`) with zero `UnivCo` axioms and zero bytecode compilations.

Resource cutoffs (`ObsCutoff`), timeouts and allocation limits (`ObsTimedOut`), double synchronous exceptions (`ObsRaisedSyncError`), and polymorphic class constraints return `Inconclusive` and never emit nominal coercions.

## Usage

Enable the plugin in a module:

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}
```

### Value Equality and Zero-Annotation Indexed Transport

Construct witnesses with `obsEq` or `checkObsEq`, and eliminate them with `castEq` or `usingEq`:

```haskell
import Data.Type.Equality ((:~:))
import Dependent.ObsEq
  ( castEq
  , checkObsEq
  , obsEq
  , setTests
  , totalObsConfig
  )

unfoldPlusLaw :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusLaw m n = obsEq

fromAccVec
  :: foreach (m :: Nat) (n :: Nat)
  -> Vec Int (accPlus m n)
  -> Vec Int (plus m n)
fromAccVec m n v = castEq (checkObsEq (setTests 80 totalObsConfig)) v
```

When the target type constructor is matchable (such as `Vec Int`), `castEq` infers the context and both endpoints with zero `@` type annotations.

### Preconditions and Invariant-Preserving `ObsDomain` Overrides

State partial-domain preconditions explicitly as Given constraints so invalid call sites fail statically, and guide sampling and shrinking with `forVar` or `forType`:

```haskell
import Dependent.ObsEq
  ( ObsDomain
  , checkObsEq
  , domainVia
  , forVar
  , totalObsConfig
  )

evenIntDomain :: ObsDomain Int
evenIntDomain = domainVia (* 2) (`quot` 2)

evenRoundtrip :: foreach (n :: Int) -> (even n ~ True) => twiceHalfEven n :~: n
evenRoundtrip n = checkObsEq (forVar n evenIntDomain totalObsConfig)
```

### Sound Projections (`ObsEquivOn`) and Quotient Lifting (`liftObsEqOn`)

Non-injective projections (such as `toListRB :: RBTree Int -> [Int]`) return `ObsEquivOn proj lhs rhs`, which wraps `proj lhs :~: proj rhs` instead of forging `lhs :~: rhs` on raw internal constructors. Operations that respect canonicalization lift constructively via `liftObsEqOn`:

```haskell
import Dependent.ObsEq
  ( ObsEquivOn
  , checkObsEq
  , checkObsEqOn
  , forVar
  , liftObsEqOn
  , totalObsConfig
  )

insertComm
  :: foreach (x :: Int) (y :: Int) (t :: RBTree Int)
  -> (isValidBST t ~ True)
  => ObsEquivOn toListRB (insertRB x (insertRB y t)) (insertRB y (insertRB x t))
insertComm x y t = checkObsEqOn (forVar t rbDomain totalObsConfig) toListRB
```

Boolean equivalence relations (`obsEqBy`, `checkObsEqBy`) return `ObsEquivBy rel lhs rhs` (`rel lhs rhs :~: True`) after verifying primary truth alongside endpoint reflexivity and symmetry.

## Plugin Options

Pass options with `-fplugin-opt=Dependent.Plugin.ObsEq:<option>`:

| Option | Default | Meaning |
| --- | --- | --- |
| `tests=N` | `100` | Number of test samples per constraint |
| `max-size=S` | `20` | Maximum generator size parameter |
| `approx-depth=D` | `100` | Bounded Kleene constructor-tree depth |
| `partial-pct=P` | `25` | Percentage of samples seeded with `ObsBottom` thunks |
| `timeout-us=T` | `10000` | Microsecond timeout per side per sample |
| `seed=K` | `0` | Deterministic starting PRNG seed |
| `policy=refute-only\|explicit\|assume` | `explicit` | Refute and prove constructively only (`refute-only`), also discharge explicit witnesses (`explicit`), or also discharge bare nominal equalities (`assume`) |

Same-module functions run as bytecode inside `hscInterp` and yield on every jump. Each sample also runs under a 64 MiB thread-local allocation limit. When testing precompiled external modules that may enter zero-allocation infinite loops, compile those provider modules with `-fno-omit-yields` so `System.Timeout.timeout` preempts them cleanly.
