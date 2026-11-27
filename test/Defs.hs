{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DependentTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ListTuplePuns #-}
{-# OPTIONS_GHC -fno-omit-yields #-}

module Defs (
    Nat (..),
    notBool,
    plus,
    unfoldPlus,
    accPlus,
    collatz,
    isEvenNat,
    halfNat,
    tripleNat,
    leNat,
    eqMod2Nat,
    TaggedNat (..),
    sameTagPair,
    loopNat,
    spinAlloc,
    deepNat12,
    nearMissNat6,
    nearMissNat15,
    nearMissInt15,
    Vec (..),
    vToList,
    Color (..),
    RBTree (..),
    emptyRB,
    insertRB,
    fromListRB,
    toListRB,
    sizeRB,
    rootKey,
    isValidBST,
    rbDomain,
    isEvenInt,
    twiceHalfEven,
    evenIntDomain,
    twiceHalfNat,
    evenNatDomain,
) where

import Dependent.ObsEq (ObsDomain, ObsGen, domainVia)
import GHC.Generics (Generic)

-- ---------------------------------------------------------------------------
-- Peano Naturals and Structural / Non-Structural Operations
-- ---------------------------------------------------------------------------

data Nat = Zero | Succ Nat
    deriving (Eq, Ord, Show, Generic)

instance ObsGen Nat

notBool :: Bool -> Bool
notBool False = True
notBool True = False

andBool :: Bool -> Bool -> Bool
andBool False _ = False
andBool True b = b

eqBool :: Bool -> Bool -> Bool
eqBool False b = notBool b
eqBool True b = b

data TaggedNat = MkTaggedNat Bool Nat
    deriving (Eq, Ord, Show, Generic)

instance ObsGen TaggedNat

tagOf :: TaggedNat -> Bool
tagOf (MkTaggedNat b _) = b

sameTagPair :: TaggedNat -> TaggedNat -> Bool
sameTagPair (MkTaggedNat b1 _) t2 = eqBool b1 (tagOf t2)

plus :: Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)

-- | Non-structural unfold addition (agrees with 'plus' on partial spines too).
unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc = acc
    step (Just Zero) acc = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- | Non-structural accumulator addition (agrees with 'plus' on total Nats).
accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc = acc
    go (Succ k) acc = go k (Succ acc)

-- | Fuel-free Collatz convergence on total Nats.
collatz :: Nat -> Nat
collatz Zero = Succ Zero
collatz (Succ Zero) = Succ Zero
collatz n
    | isEvenNat n = collatz (halfNat n)
    | otherwise = collatz (Succ (tripleNat n))

isEvenNat :: Nat -> Bool
isEvenNat Zero = True
isEvenNat (Succ n) = notBool (isEvenNat n)

halfNat :: Nat -> Nat
halfNat Zero = Zero
halfNat (Succ Zero) = Zero
halfNat (Succ (Succ n)) = Succ (halfNat n)

tripleNat :: Nat -> Nat
tripleNat Zero = Zero
tripleNat (Succ n) = Succ (Succ (Succ (tripleNat n)))

-- | Non-symmetric order on 'Nat' (reflexive and transitive, NOT symmetric).
leNat :: Nat -> Nat -> Bool
leNat Zero _ = True
leNat (Succ _) Zero = False
leNat (Succ m) (Succ n) = leNat m n

-- | Symmetric parity equivalence relation on 'Nat' with checked equations.
eqMod2Nat :: Nat -> Nat -> Bool
eqMod2Nat Zero n = isEvenNat n
eqMod2Nat (Succ m) n = notBool (eqMod2Nat m n)

-- | Non-terminating function on 'Nat' for timeout tests.
loopNat :: Nat -> Nat
loopNat n = loopNat (Succ n)

-- | Allocating diverging loop for native runtime 'evalObsSample' tests.
spinAlloc :: Integer -> Nat
spinAlloc k
    | k < 0 = Zero
    | otherwise = spinAlloc (k + 1)

-- | Prepend 12 'Succ' constructors to test shallow depth cutoffs.
deepNat12 :: Nat -> Nat
deepNat12 n =
    Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ n)))))))))))

-- | Agrees with identity on @0..5@ and collapses to 'Zero' at @>= 6@.
nearMissNat6 :: Nat -> Nat
nearMissNat6 Zero = Zero
nearMissNat6 (Succ Zero) = Succ Zero
nearMissNat6 (Succ (Succ Zero)) = Succ (Succ Zero)
nearMissNat6 (Succ (Succ (Succ Zero))) = Succ (Succ (Succ Zero))
nearMissNat6 (Succ (Succ (Succ (Succ Zero)))) = Succ (Succ (Succ (Succ Zero)))
nearMissNat6 (Succ (Succ (Succ (Succ (Succ Zero))))) = Succ (Succ (Succ (Succ (Succ Zero))))
nearMissNat6 _ = Zero

natAtLeast15 :: Nat -> Bool
natAtLeast15 (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ _))))))))))))))) = True
natAtLeast15 _ = False

-- | Agrees with identity on @0..14@ and collapses to 'Zero' at @>= 15@.
nearMissNat15 :: Nat -> Nat
nearMissNat15 n
    | natAtLeast15 n = Zero
    | otherwise = n

-- | Agrees with identity on @[-14..14]@ and collapses to @0@ when @|n| >= 15@.
nearMissInt15 :: Int -> Int
nearMissInt15 n
    | n >= (-14) && n <= 14 = n
    | otherwise = 0

-- ---------------------------------------------------------------------------
-- Length-Indexed Vectors
-- ---------------------------------------------------------------------------

data Vec a (n :: Nat) where
    VNil :: Vec a Zero
    VCons :: a -> Vec a n -> Vec a (Succ n)

vToList :: Vec a n -> [a]
vToList VNil = []
vToList (VCons x xs) = x : vToList xs

-- ---------------------------------------------------------------------------
-- Colored Binary Search Trees and Sorted-List Canonicalization
-- ---------------------------------------------------------------------------

data Color = R | B
    deriving (Eq, Ord, Show)

data RBTree a = E | T Color (RBTree a) a (RBTree a)
    deriving (Eq, Ord, Show)

emptyRB :: RBTree Nat
emptyRB = E

flipCol :: Color -> Color
flipCol R = B
flipCol B = R

ifTree :: Bool -> RBTree Nat -> RBTree Nat -> RBTree Nat
ifTree False _ b = b
ifTree True a _ = a

appendNat :: [Nat] -> [Nat] -> [Nat]
appendNat [] ys = ys
appendNat (x : xs) ys = x : appendNat xs ys

insertRB :: Nat -> RBTree Nat -> RBTree Nat
insertRB x E = T B E x E
insertRB x (T col l y r) =
    ifTree
        (notBool (leNat y x))
        (T (flipCol col) (insertRB x l) y r)
        (ifTree (notBool (leNat x y)) (T (flipCol col) l y (insertRB x r)) (T col l y r))

fromListRB :: [Nat] -> RBTree Nat
fromListRB [] = E
fromListRB (k : ks) = insertRB k (fromListRB ks)

toListRB :: RBTree Nat -> [Nat]
toListRB E = []
toListRB (T _ l k r) = appendNat (toListRB l) (k : toListRB r)

sizeRB :: RBTree Nat -> Nat
sizeRB E = Zero
sizeRB (T _ l _ r) = Succ (plus (sizeRB l) (sizeRB r))

{- | Internal-structure-sensitive observer that distinguishes trees with
identical 'toListRB' projections.
-}
rootKey :: RBTree Nat -> Maybe Nat
rootKey E = Nothing
rootKey (T _ _ k _) = Just k

-- | Strictly-ordered binary search tree invariant with checked equations.
ltNat :: Nat -> Nat -> Bool
ltNat Zero n = notBool (leNat n Zero)
ltNat (Succ m) n = notBool (leNat n (Succ m))

allLtNat :: Nat -> RBTree Nat -> Bool
allLtNat _ E = True
allLtNat bound (T _ l k r) =
    andBool (ltNat k bound) (andBool (allLtNat bound l) (allLtNat bound r))

allGtNat :: Nat -> RBTree Nat -> Bool
allGtNat _ E = True
allGtNat bound (T _ l k r) =
    andBool (ltNat bound k) (andBool (allGtNat bound l) (allGtNat bound r))

isValidBST :: RBTree Nat -> Bool
isValidBST E = True
isValidBST (T _ l k r) =
    andBool
        (allLtNat k l)
        (andBool (allGtNat k r) (andBool (isValidBST l) (isValidBST r)))

rbDomain :: ObsDomain (RBTree Nat)
rbDomain = domainVia fromListRB toListRB

-- ---------------------------------------------------------------------------
-- Guarded Even Domains
-- ---------------------------------------------------------------------------

isEvenInt :: Int -> Bool
isEvenInt n = n `rem` 2 == 0

twiceHalfEven :: Int -> Int
twiceHalfEven n
    | isEvenInt n = (n `quot` 2) * 2
    | otherwise = error "twiceHalfEven: odd input"

evenIntDomain :: ObsDomain Int
evenIntDomain = domainVia (* 2) (`quot` 2)

twiceHalfNat :: Nat -> Nat
twiceHalfNat n
    | isEvenNat n = plus (halfNat n) (halfNat n)
    | otherwise = error "twiceHalfNat: odd input"

evenNatDomain :: ObsDomain Nat
evenNatDomain = domainVia (\k -> plus k k) halfNat
