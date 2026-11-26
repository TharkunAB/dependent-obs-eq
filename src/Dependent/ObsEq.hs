{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Dependent.ObsEq
-- Description : Observational-equivalence witnesses, projections, and domains
-- License     : BSD-3-Clause
-- Maintainer  : mpg@mpg.is
--
-- Explicit observational-equivalence witnesses ('obsEq', 'checkObsEq'),
-- canonical observation projections ('ObsEquivOn', 'obsEqOn', 'liftObsEqOn'),
-- symmetric boolean equivalence relations ('ObsEquivBy', 'obsEqBy'), indexed
-- transport eliminators ('castEq', 'usingEq'), and invariant-preserving
-- 'ObsDomain' overrides ('forType', 'forVar') for @-fplugin=Dependent.Plugin.ObsEq@.
--
-- Credit: Based on the observational-equivalence / QuickCheck @TcPlugin@ idea
-- proposed by Jules (\@analytichegel).
module Dependent.ObsEq
  ( -- * Value-level observational equality witnesses
    ObsEq (..)
  , obsEq
  , checkObsEq

    -- * Projection and equivalence-relation witnesses
  , ObsEquivOn (UnsafeObsEquivOn, projectEq)
  , ObsEqOn (..)
  , obsEqOn
  , checkObsEqOn
  , reflObsOn
  , symObsOn
  , transObsOn
  , castEqOn
  , liftObsEqOn
  , ObsEquivBy (UnsafeObsEquivBy, relEqTrue)
  , ObsEqBy (..)
  , obsEqBy
  , checkObsEqBy

    -- * Witness eliminators
  , castEq
  , usingEq

    -- * Configuration and domain overrides
  , ObsConfig
      ( obsTests
      , obsMaxSize
      , obsApproxDepth
      , obsPartialPct
      , obsTimeoutUs
      , obsSeed
      )
  , defaultObsConfig
  , totalObsConfig
  , setTests
  , setMaxSize
  , setApproxDepth
  , setPartialPct
  , setTimeoutUs
  , setSeed
  , ObsDomain (..)
  , domain
  , domainGen
  , domainVia
  , domainSuchThat
  , forType
  , forVar

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

    -- * Partial demand probes and Kleene observation verdicts
  , ObsBottom (..)
  , obsBottom
  , freshBottom
  , mixPartial
  , ObsTree (..)
  , InconclusiveReason (..)
  , ObsCmp (..)
  , ObsVerdict (..)
  , GuardResult (..)
  , compareObsTree
  , evalObsSample
  , renderObsTree
  , ObsGen (..)

    -- * Plugin runtime harness helpers
  , AdtObsDict (..)
  , mkAdtObsDict
  , runObsTestLoop
  , runObsOnLoop
  , runObsByLoop
  ) where

import Data.Kind ( Constraint, Type )
import Data.Type.Equality ( (:~:) (Refl), sym, trans )
import GHC.Matchability ( M, U )

import Dependent.ObsEq.Domain
  ( AdtObsDict (..)
  , Gen (..)
  , GuardResult (..)
  , InconclusiveReason (..)
  , ObsBottom (..)
  , ObsCmp (..)
  , ObsDomain (..)
  , ObsGen (..)
  , ObsTree (..)
  , ObsVerdict (..)
  , Seed (..)
  , chooseInt
  , chooseInteger
  , chooseWord64
  , compareObsTree
  , domain
  , domainGen
  , domainSuchThat
  , domainVia
  , elements
  , evalObsSample
  , forType
  , forVar
  , frequency
  , freshBottom
  , listOf
  , mixPartial
  , mkAdtObsDict
  , mkSeed
  , obsBottom
  , oneof
  , renderObsTree
  , resize
  , runGenAt
  , runObsByLoop
  , runObsOnLoop
  , runObsTestLoop
  , sized
  , splitSeed
  , stepSeed
  )
import Dependent.ObsEq.Internal
  ( DefaultObsConfig
  , ObsConfig (..)
  , defaultObsConfig
  , setApproxDepth
  , setMaxSize
  , setPartialPct
  , setSeed
  , setTests
  , setTimeoutUs
  , totalObsConfig
  )

{- Note [Orthogonal witness construction and elimination]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Credit: Jules (@analytichegel) proposed using a randomized property-testing
@TcPlugin@ to test and discharge observational type equalities on open terms in
Dependent Haskell.

"Dependent.ObsEq" separates witness construction, configuration modification,
and witness elimination into three orthogonal groups:

1. Witness constructors ('obsEq', 'checkObsEq', 'obsEqOn', 'checkObsEqOn',
   'obsEqBy', 'checkObsEqBy') request observational evidence without coupling
   the witness to a continuation.
2. Configuration modifiers ('setTests' .. 'setSeed', 'forType', 'forVar')
   compose onto 'defaultObsConfig' and 'totalObsConfig' without repeating
   scope-introducing @with@ prefixes.
3. Witness eliminators ('castEq' and 'usingEq') consume any propositional
   equality witness @lhs :~: rhs@ (whether produced by 'obsEq' or by a
   deductive proof).

In 'castEq', bidirectional type inference unifies @p lhs@ against the input type
and @p rhs@ against the expected result type. When @p@ is headed by a matchable
generative type constructor (such as @Vec Int (accPlus m n) -> Vec Int (plus m n)@),
GHC infers @p := Vec Int@, @lhs := accPlus m n@, and @rhs := plus m n@ with zero
explicit @\@@ type applications before invoking @Dependent.Plugin.ObsEq@.
-}

-- | Explicit value-equality constraint parameterized by 'ObsConfig' and
-- discharged by @Dependent.Plugin.ObsEq@.
type ObsEq :: forall {k}. ObsConfig -> k -> k -> Constraint
class ObsEq cfg lhs rhs where
  -- | Propositional equality witness supplied by @Dependent.Plugin.ObsEq@.
  obsEqProof :: lhs :~: rhs

-- | Obtain a propositional equality witness @lhs :~: rhs@ under the active
-- default configuration ('defaultObsConfig' plus any CLI plugin flags).
-- See Note [Orthogonal witness construction and elimination].
obsEq :: forall {k} (lhs :: k) (rhs :: k). ObsEq DefaultObsConfig lhs rhs => lhs :~: rhs
obsEq = obsEqProof @DefaultObsConfig @lhs @rhs

-- | Obtain a propositional equality witness @lhs :~: rhs@ under an explicit
-- 'ObsConfig' (including 'forType' and 'forVar' domain overrides).
-- See Note [Orthogonal witness construction and elimination].
checkObsEq
  :: forall {k}.
     forall (cfg :: ObsConfig)
  -> forall (lhs :: k) (rhs :: k).
     ObsEq cfg lhs rhs
  => lhs :~: rhs
checkObsEq (type cfg) @lhs @rhs = obsEqProof @cfg @lhs @rhs

{- Note [Soundness boundary for ObsEquivOn and ObsEquivBy]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In System FC, a nominal equality @lhs :~: rhs@ on an algebraic datatype asserts
that @lhs@ and @rhs@ have identical constructor trees in all contexts, including
pattern matching on internal representation constructors. Two balanced search
trees @t1@ and @t2@ can have equal sorted element lists
(@toAscList t1 == toAscList t2@) while having different root keys
(@rootKey t1 /= rootKey t2@). Forging @t1 :~: t2@ from projection agreement
would allow @cong rootKey@ to derive @Just 1 :~: Just 2@ and @Int :~: Bool@.

Therefore, projection and equivalence-relation witnesses inhabit dedicated
newtypes that expose only the true nominal equation:

* 'ObsEquivOn' @proj lhs rhs@ wraps @proj lhs :~: proj rhs@ ('projectEq').
* 'ObsEquivBy' @rel lhs rhs@ wraps @rel lhs rhs :~: True@ ('relEqTrue'), and
  @Dependent.Plugin.ObsEq@ tests endpoint reflexivity (@rel x x@, @rel y y@) and
  symmetry (@rel y x@) alongside @rel x y@.

Combinator 'liftObsEqOn' lifts @ObsEquivOn proj lhs rhs@ through any operation
@f :: a -> b@ that commutes with a canonicalizer @reify :: rep -> a@ by
composing single-variable canonicalization witnesses
@f (reify (proj x)) :~: f x@ constructively, without emitting extra axioms.
Operations that leak internal structure (such as @rootKey@) fail the
canonicalization check @rootKey (fromAscList (toAscList t)) :~: rootKey t@ with
a shrunk counterexample.
-}

-- | Witness that @lhs@ and @rhs@ produce equal observations under @proj@.
-- Exposes @proj lhs :~: proj rhs@, never @lhs :~: rhs@.
-- See Note [Soundness boundary for ObsEquivOn and ObsEquivBy].
type ObsEquivOn :: forall {a} {rep}. (a %U -> rep) -> a -> a -> Type
newtype ObsEquivOn proj lhs rhs = UnsafeObsEquivOn
  { projectEq :: proj lhs :~: proj rhs
  }

-- | Explicit projection-equality constraint discharged by @Dependent.Plugin.ObsEq@.
type ObsEqOn :: forall {a} {rep}. ObsConfig -> (a %U -> rep) -> a -> a -> Constraint
class ObsEqOn cfg proj lhs rhs where
  -- | Projection witness supplied by @Dependent.Plugin.ObsEq@.
  obsEqOnProof :: ObsEquivOn proj lhs rhs

-- | Test equality of @lhs@ and @rhs@ up to projection @proj@ under
-- 'defaultObsConfig'.
obsEqOn
  :: forall {a} {rep}.
     forall (proj :: a %U -> rep)
  -> forall (lhs :: a) (rhs :: a).
     ObsEqOn DefaultObsConfig proj lhs rhs
  => ObsEquivOn proj lhs rhs
obsEqOn (type proj) @lhs @rhs = obsEqOnProof @DefaultObsConfig @proj @lhs @rhs

-- | Test equality of @lhs@ and @rhs@ up to projection @proj@ under @cfg@.
checkObsEqOn
  :: forall {a} {rep}.
     forall (cfg :: ObsConfig) (proj :: a %U -> rep)
  -> forall (lhs :: a) (rhs :: a).
     ObsEqOn cfg proj lhs rhs
  => ObsEquivOn proj lhs rhs
checkObsEqOn (type cfg) (type proj) @lhs @rhs = obsEqOnProof @cfg @proj @lhs @rhs

-- | Constructive reflexivity of 'ObsEquivOn'.
reflObsOn :: forall {a} {rep} {proj :: a %U -> rep} {x :: a}. ObsEquivOn proj x x
reflObsOn = UnsafeObsEquivOn Refl

-- | Constructive symmetry of 'ObsEquivOn'.
symObsOn
  :: forall {a} {rep} {proj :: a %U -> rep} {lhs :: a} {rhs :: a}.
     ObsEquivOn proj lhs rhs
  -> ObsEquivOn proj rhs lhs
symObsOn (UnsafeObsEquivOn eq) = UnsafeObsEquivOn (sym eq)

-- | Constructive transitivity of 'ObsEquivOn'.
transObsOn
  :: forall {a} {rep} {proj :: a %U -> rep} {x :: a} {y :: a} {z :: a}.
     ObsEquivOn proj x y
  -> ObsEquivOn proj y z
  -> ObsEquivOn proj x z
transObsOn (UnsafeObsEquivOn p) (UnsafeObsEquivOn q) = UnsafeObsEquivOn (trans p q)

-- | Transport a value of a matchable type constructor @p@ indexed by the
-- canonical observation @proj x@.
castEqOn
  :: forall {a} {rep}
     {p :: rep %M -> Type} {proj :: a %U -> rep} {lhs :: a} {rhs :: a}.
     ObsEquivOn proj lhs rhs
  -> p (proj lhs)
  -> p (proj rhs)
castEqOn (UnsafeObsEquivOn eqProj) px = castEq eqProj px

congUnmatchable
  :: forall {a} {b}.
     forall (h :: a %U -> b)
  -> forall {u :: a} {v :: a}.
     (u :~: v)
  -> h u :~: h v
congUnmatchable (type _) Refl = Refl

-- | Lift @ObsEquivOn proj lhs rhs@ through an operation @f@ that commutes with
-- a canonicalizer @reify@ on both endpoints.
-- See Note [Soundness boundary for ObsEquivOn and ObsEquivBy].
liftObsEqOn
  :: forall {a} {rep} {b}.
     forall (reify :: rep %U -> a) (f :: a %U -> b)
  -> forall {proj :: a %U -> rep} {lhs :: a} {rhs :: a}.
     (f (reify (proj lhs)) :~: f lhs)
  -> (f (reify (proj rhs)) :~: f rhs)
  -> ObsEquivOn proj lhs rhs
  -> f lhs :~: f rhs
liftObsEqOn (type reify) (type f) eqL eqR (UnsafeObsEquivOn eqProj) =
  trans (sym eqL) (trans (congUnmatchable f (congUnmatchable reify eqProj)) eqR)

-- | Witness that @rel lhs rhs@ evaluates to 'True' and behaves reflexively and
-- symmetrically on the tested endpoints.
-- Exposes @rel lhs rhs :~: True@, never @lhs :~: rhs@.
-- See Note [Soundness boundary for ObsEquivOn and ObsEquivBy].
type ObsEquivBy :: forall {a}. (a %U -> a %U -> Bool) -> a -> a -> Type
newtype ObsEquivBy rel lhs rhs = UnsafeObsEquivBy
  { relEqTrue :: rel lhs rhs :~: True
  }

-- | Explicit equivalence-relation constraint discharged by
-- @Dependent.Plugin.ObsEq@.
type ObsEqBy :: forall {a}. ObsConfig -> (a %U -> a %U -> Bool) -> a -> a -> Constraint
class ObsEqBy cfg rel lhs rhs where
  -- | Relation witness supplied by @Dependent.Plugin.ObsEq@.
  obsEqByProof :: ObsEquivBy rel lhs rhs

-- | Test equivalence of @lhs@ and @rhs@ under boolean relation @rel@ and
-- 'defaultObsConfig'.
obsEqBy
  :: forall {a}.
     forall (rel :: a %U -> a %U -> Bool)
  -> forall (lhs :: a) (rhs :: a).
     ObsEqBy DefaultObsConfig rel lhs rhs
  => ObsEquivBy rel lhs rhs
obsEqBy (type rel) @lhs @rhs = obsEqByProof @DefaultObsConfig @rel @lhs @rhs

-- | Test equivalence of @lhs@ and @rhs@ under boolean relation @rel@ and @cfg@.
checkObsEqBy
  :: forall {a}.
     forall (cfg :: ObsConfig) (rel :: a %U -> a %U -> Bool)
  -> forall (lhs :: a) (rhs :: a).
     ObsEqBy cfg rel lhs rhs
  => ObsEquivBy rel lhs rhs
checkObsEqBy (type cfg) (type rel) @lhs @rhs = obsEqByProof @cfg @rel @lhs @rhs

-- | Cast a value from @p lhs@ to @p rhs@ along @lhs :~: rhs@.
-- Because @p@ is matchable (@k %M -> Type@, such as @Vec Int@), GHC infers @p@,
-- @lhs@, and @rhs@ from the value argument and expected result type with zero
-- explicit @\@@ annotations. Use 'usingEq' when the target context is headed by
-- an unmatchable type family.
-- See Note [Orthogonal witness construction and elimination].
castEq
  :: forall {k} {p :: k %M -> Type} {lhs :: k} {rhs :: k}.
     (lhs :~: rhs)
  -> p lhs
  -> p rhs
castEq Refl px = px

-- | Bring the nominal equality @lhs ~ rhs@ into scope for a continuation @r@.
-- See Note [Orthogonal witness construction and elimination].
usingEq
  :: forall {k} {lhs :: k} {rhs :: k} {r}.
     (lhs :~: rhs)
  -> ((lhs ~ rhs) => r)
  -> r
usingEq Refl k = k

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

Function 'compareObsTree' (implemented in "Dependent.ObsEq.Domain") evaluates a
strong three-valued Kleene lattice ('ObsCmp'):
* Two 'ObsCon' nodes with different constructor names or arities are
  'ObsApart'. Matching constructors combine child results with Kleene
  conjunction: any 'ObsApart' child yields 'ObsApart' immediately, else any
  'ObsUnknown' child yields 'ObsUnknown', else 'ObsEqual'.
* 'ObsRaisedBottom' carries the deterministic PRNG tag of an injected partial
  input thunk. Raising the same tag on both sides proves identical first-demand
  laziness ('ObsEqual'); raising different tags or matching a value against
  'ObsRaisedBottom' proves a strictness mismatch ('ObsApart').
* Resource limits ('ObsCutoff', 'ObsTimedOut') and double 'ObsRaisedSyncError'
  always yield 'ObsUnknown', which aggregates to 'Inconclusive' and never emits
  a nominal coercion.
-}
