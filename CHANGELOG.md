# Revision history for dependent-obs-eq

## 0.2.0.0 -- 2026-11-26

* Replace coupled `withObsEq*` / `obsEqWith` / `obsEqGen` combinators with
  orthogonal witness constructors (`obsEq`, `checkObsEq`, `obsEqOn`,
  `checkObsEqOn`, `obsEqBy`, `checkObsEqBy`), eliminators (`castEq`,
  `usingEq`), presets (`defaultObsConfig`, `totalObsConfig`), and scalar
  `setTests` .. `setSeed` modifiers.
* Add sound projection witnesses (`ObsEquivOn`, `reflObsOn`, `symObsOn`,
  `transObsOn`, `castEqOn`, `liftObsEqOn`) and symmetric boolean
  equivalence-relation witnesses (`ObsEquivBy`) with endpoint reflexivity and
  symmetry verification.
* Add `ObsDomain` (`domain`, `domainGen`, `domainVia`, `domainSuchThat`),
  per-type `forType` and lexical `forVar` overrides, Given boolean precondition
  filtering, unguarded baseline boundary sweeps, `4 x 4` diagonal coupled pair
  shrinking, and synthesized ADT constructor-field shrinking.
* Enforce strong three-valued Kleene comparison (`compareObsTree`, `ObsCmp`,
  `ObsVerdict`, `InconclusiveReason`), raise default `obsApproxDepth` to `100`,
  add `policy=refute-only`, block unsound positive discharge under polymorphic
  class constraints (`PolymorphicClassConstraint`), and isolate speculative
  `ExprHoleOrigin` checks.
* Add constructive Knuth-Bendix + `SourceTable` pre-pass
  (`Dependent.Plugin.ObsEq.Rewrite`), per-module desugar/verdict/fingerprint
  caches (`GHC.Core.Map.Type`), batched bytecode evaluation, shallow depth-2
  screening, and a 64 MiB per-sample allocation limit.

## 0.1.0.0 -- 2026-11-25

* Initial release of `Dependent.ObsEq` and `Dependent.Plugin.ObsEq`:
  observational-equivalence testing and counterexample refutation for
  Dependent Haskell (`-XDependentTypes`).
