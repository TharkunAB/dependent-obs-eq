# dependent-obs-eq

`dependent-obs-eq` provides a GHC typechecker plugin (`Dependent.Plugin.ObsEq`) and user combinator library (`Dependent.ObsEq`) for bounded observational-equivalence testing and counterexample refutation in Dependent Haskell (`-XDependentTypes`).

## Attribution

Based on the observational-equivalence / QuickCheck `TcPlugin` idea proposed by **Jules (@analytichegel)**.

## Overview

In Dependent Haskell, structural functions produce certified closed type-family equations (`SourceTable`). Lazy, partial, accumulator-based, or non-structural functions do not have structural equations. When `-fplugin=Dependent.Plugin.ObsEq` is enabled:

1. **Uninterpreted term calls**: GHC elaborates open calls to uncertified functions into stuck closed-family applications instead of rejecting them before constraint solving.
2. **Automatic counterexample refutation**: On any stuck nominal equality `[W] lhs ~# rhs` over testable domains, the plugin evaluates bounded Kleene approximations over both total and partially defined (`ObsBottom`) inputs. When a sample distinguishes `lhs` and `rhs`, the plugin shrinks the input and reports the minimal counterexample at the source span.
3. **Explicit observational witnesses (`ExplicitOnly` default)**: `obsEq`, `obsEqWith`, and `obsEqGen` discharge `lhs :~: rhs` when all configured samples agree up to the approximation depth and per-sample timeout. Bare `Refl` remains rejected unless an actual definitional or inductive proof exists (or `policy=assume` is explicitly enabled).

## Usage

Enable the plugin in a module:

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}
```

Prove an observational law explicitly:

```haskell
import Data.Type.Equality ((:~:))
import Dependent.ObsEq (obsEq, obsEqGen, obsEqWith, withTests, defaultObsConfig)

accPlusLaw :: foreach (m :: Nat) (n :: Nat) -> accPlus m n :~: plus m n
accPlusLaw m n = obsEq
```

Override test parameters per call or pass a custom domain generator:

```haskell
evenHalfLaw :: foreach (n :: Int) -> twiceHalf n :~: n
evenHalfLaw n = obsEqGen genEvenInt

deepLaw :: foreach (m :: Nat) -> collatzToOne m :~: Succ Zero
deepLaw m = obsEqWith (withTests 200 defaultObsConfig)
```

## Plugin Options

Pass options with `-fplugin-opt=Dependent.Plugin.ObsEq:<option>`:

| Option | Default | Meaning |
| --- | --- | --- |
| `tests=N` | `100` | Number of test samples per constraint |
| `max-size=S` | `20` | Maximum generator size parameter |
| `approx-depth=D` | `8` | Bounded Kleene constructor-tree depth |
| `partial-pct=P` | `25` | Percentage of samples seeded with `ObsBottom` thunks |
| `timeout-us=T` | `10000` | Microsecond timeout per side per sample |
| `seed=K` | `0` | Deterministic starting PRNG seed |
| `policy=explicit\|assume` | `explicit` | Keep bare `Refl` conservative (`explicit`) or discharge passing nominal equalities (`assume`) |

Same-module functions run as bytecode inside `hscInterp` and yield on every jump. When testing precompiled external modules that may enter zero-allocation infinite loops, compile those provider modules with `-fno-omit-yields` so `System.Timeout.timeout` can preempt them cleanly.
