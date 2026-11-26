{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq #-}
{-# OPTIONS_GHC -fplugin-opt=Dependent.Plugin.ObsEq:policy=refute-only #-}
{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module DeferredRefuteOnly
  ( constructiveUnderRefuteOnly
  , badExplicitUnderRefuteOnly
  ) where

import Data.Type.Equality ( (:~:) (Refl) )
import Dependent.ObsEq ( obsEq )
import Defs ( Nat (..), plus, unfoldPlus )

-- 1. Purely constructive KBO + SourceTable proof succeeds under policy=refute-only
-- with zero UnivCo and zero BCO evaluation!
constructiveUnderRefuteOnly
  :: foreach (m :: Nat) (n :: Nat)
  -> (plus m n ~ plus n m)
  => Succ (plus m n) :~: plus (Succ n) m
constructiveUnderRefuteOnly _m _n = Refl

-- 2. Under policy=refute-only, even a valid explicit 'obsEq' goal is left
-- unsolved (no UnivCo emitted).
refuteOnlyBlocksObsEq :: foreach (m :: Nat) (n :: Nat) -> unfoldPlus m n :~: plus m n
refuteOnlyBlocksObsEq _m _n = obsEq

badExplicitUnderRefuteOnly :: unfoldPlus Zero Zero :~: plus Zero Zero
badExplicitUnderRefuteOnly = refuteOnlyBlocksObsEq Zero Zero
