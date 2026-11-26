{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Dependent.ObsEq.Internal
-- Description : Configuration types and modifiers for Dependent.ObsEq
-- License     : BSD-3-Clause
-- Maintainer  : mpg@mpg.is
--
-- Scalar configuration record, stuck 'DefaultObsConfig' marker family, and
-- modifiers for "Dependent.ObsEq".
module Dependent.ObsEq.Internal
  ( ObsConfig (..)
  , DefaultObsConfig
  , defaultObsConfig
  , totalObsConfig
  , setTests
  , setMaxSize
  , setApproxDepth
  , setPartialPct
  , setTimeoutUs
  , setSeed
  ) where

import Numeric.Natural ( Natural )

-- | Scalar parameters for bounded observational-equivalence testing.
data ObsConfig = ObsConfig
  { obsTests :: Natural
  -- ^ Number of test samples to run (default: @100@).
  , obsMaxSize :: Natural
  -- ^ Maximum generator size parameter (default: @20@).
  , obsApproxDepth :: Natural
  -- ^ Maximum constructor-tree approximation depth (default: @100@).
  , obsPartialPct :: Natural
  -- ^ Percentage @[0..100]@ of samples that inject @ObsBottom@ thunks (default: @25@).
  , obsTimeoutUs :: Natural
  -- ^ Per-side evaluation timeout in microseconds (default: @10000@).
  , obsSeed :: Natural
  -- ^ Deterministic starting PRNG seed (default: @0@).
  }
  deriving (Eq, Ord, Show, Read)

-- | Stuck closed type family representing the active plugin configuration
-- ('defaultObsConfig' overridden by any CLI @-fplugin-opt@ flags) inside
-- 'Dependent.ObsEq.obsEq', 'Dependent.ObsEq.obsEqOn', and
-- 'Dependent.ObsEq.obsEqBy'.
type family DefaultObsConfig :: ObsConfig where

-- | Default observational-equivalence configuration (@obsTests = 100@,
-- @obsMaxSize = 20@, @obsApproxDepth = 100@, @obsPartialPct = 25@,
-- @obsTimeoutUs = 10000@, @obsSeed = 0@).
defaultObsConfig :: ObsConfig
defaultObsConfig = ObsConfig 100 20 100 25 10000 0

-- | Preset configuration for total-domain equations (@obsPartialPct = 0@).
totalObsConfig :: ObsConfig
totalObsConfig = ObsConfig 100 20 100 0 10000 0

-- | Set 'obsTests' on an 'ObsConfig'.
setTests :: Natural -> ObsConfig -> ObsConfig
setTests n (ObsConfig _ s d p t sd) = ObsConfig n s d p t sd

-- | Set 'obsMaxSize' on an 'ObsConfig'.
setMaxSize :: Natural -> ObsConfig -> ObsConfig
setMaxSize s (ObsConfig n _ d p t sd) = ObsConfig n s d p t sd

-- | Set 'obsApproxDepth' on an 'ObsConfig'.
setApproxDepth :: Natural -> ObsConfig -> ObsConfig
setApproxDepth d (ObsConfig n s _ p t sd) = ObsConfig n s d p t sd

-- | Set 'obsPartialPct' on an 'ObsConfig'.
setPartialPct :: Natural -> ObsConfig -> ObsConfig
setPartialPct p (ObsConfig n s d _ t sd) = ObsConfig n s d p t sd

-- | Set 'obsTimeoutUs' on an 'ObsConfig'.
setTimeoutUs :: Natural -> ObsConfig -> ObsConfig
setTimeoutUs t (ObsConfig n s d p _ sd) = ObsConfig n s d p t sd

-- | Set 'obsSeed' on an 'ObsConfig'.
setSeed :: Natural -> ObsConfig -> ObsConfig
setSeed sd (ObsConfig n s d p t _) = ObsConfig n s d p t sd
