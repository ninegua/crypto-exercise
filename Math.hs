{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module Math
  ( embed
  , Positive
  , Negative
  , NonNegative
  , NonPositive
  , ifZero
  , positive
  --
  , coprime
  , gcdEq
  , primes
  , isPrime
  --
  , pow
  , invmod
  , expmod
  , modulo
  , minus
  --
  , Prime(..)
  , CoPrime(..)
  , test
  )
where

import Data.List       (inits)
import Test.QuickCheck


-------------------------------------------------------------------------------------
-- Before we dive into any theory or modulo arithmetics. We introduce the
-- concept of sub-type, and define an embed function to convert values from
-- sub-type to super-type.

-- s <: t means type s is a sub-type of t.
class s <: t where
  -- embed is a total function
  embed :: s -> t

instance (Show a, Ord a, Num a) => Positive a <: NonNegative a where
  embed (Positive x) = NonNegative x

instance (Show a, Ord a, Num a) => Positive a <: a where
  embed (Positive x) = x

instance (Show a, Ord a, Num a) => NonNegative a <: a where
  embed (NonNegative x) = x

-- Relation (<:) is reflexive.
instance a <: a where
  embed = id

-------------------------------------------------------------------------------------
-- The Positive and NonNegative types are defined in QuickCheck, but they were
-- not made as instances of Num. Here we give the missing definitions.

instance (Ord a, Num a, Show a, Integral a) => Num (Positive a) where
  Positive x + Positive y = Positive (x + y)
  Positive x - Positive y = fromIntegral (x - y)
  Positive x * Positive y = Positive (x * y)
  negate x = error $ "negate: " ++ show x
  fromInteger x
    | x > 0     = Positive (fromInteger x)
    | otherwise = error $ "fromInteger: " ++ show x ++ " is not Positive"
  abs x = x
  signum _ = 1

instance (Ord a, Num a, Show a, Integral a) => Num (NonNegative a) where
  NonNegative x + NonNegative y = NonNegative (x + y)
  NonNegative x - NonNegative y = fromIntegral (x - y)
  NonNegative x * NonNegative y = NonNegative (x * y)
  negate x = error $ "negate: " ++ show x
  fromInteger x
    | x >= 0    = NonNegative (fromInteger x)
    | otherwise = error $ "fromInteger: " ++ show x ++ " is not NonNegative"
  abs x = x
  signum (NonNegative x) = if x == 0 then 0 else 1

ifZero :: (Eq a, Num a) => NonNegative a -> b -> (Positive a -> b) -> b
ifZero (NonNegative 0) t _ = t
ifZero (NonNegative x) _ f = f (Positive x)

positive :: (Integral a, Show a) => NonNegative a -> Positive a
positive (NonNegative x) = fromIntegral x

-------------------------------------------------------------------------------------
-- Basic Modular Arithmetics
--
-- The mod function from Prelude's Integral class is not precise enough to
-- capture the expected domain and range used in modular arithmetics.
--
-- For this purpose, we define a custom modulo function: x `modulo` y, where x
-- is an integer, y is Positive, and the result is NonNegative.
modulo :: (Ord a, Num a, Integral a, b <: a) => b -> Positive a -> NonNegative a
modulo x (Positive y) = NonNegative (if r >= 0 then r else r + y)
  where r = embed x `mod` y

-- A helper function to compute x - y (mod p) when x and y are NonNegative.
minus
  :: forall a
   . (Ord a, Num a, Show a, Integral a)
  => Positive a
  -> NonNegative a
  -> NonNegative a
  -> NonNegative a
minus p x y = z `modulo` p where z = embed x - embed y :: a

-- Compute x^y, where y is one of Positive, NonNegative.
pow :: forall f a b . (Num a, Show b, Integral b, f b <: b) => a -> f b -> a
pow x y = x ^ (embed y :: b)

-- Two numbers x and y are coprime to each other if and only if gcd(x, y) == 1,
-- where both x and y are either Positive or NonNegative.
coprime :: (a <: Integer, b <: Integer) => a -> b -> Bool
coprime = gcdEq 1

-- Return True if z == gcd x y
gcdEq :: (a <: c, b <: c, Integral c, Eq c) => c -> a -> b -> Bool
gcdEq z x y = z == gcd (embed x) (embed y)

-- Extended Euclidean Algorithm is to find x and y such that ax + my = 1, where
-- all numbers are integers.
-- https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
--
-- If ax + my = 1 is given as a condition, it implies ax = 1 (mod m), when m is
-- Positive. Therefore, this algorithm is used to find modular multiplicative
-- inverses.
--
egcd :: Integral a => a -> a -> (a, a, a)
egcd a b = egcd' a b 1 0 0 1
 where
  egcd' a b u v x y
    | a == 0
    = (b, x, y)
    | b == 0
    = (a, u, v)
    | a > b
    = let (i, j) = a `divMod` b in egcd' j b (u - i * x) (v - i * y) x y
    | otherwise
    = let (i, j) = b `divMod` a in egcd' a j u v (x - i * u) (y - i * v)

-- Find the multiplicative inverse x of a (mod m), such that ax = 1 (mod m).
-- This function is partial, and gives error when a and m are not coprimes.
invmod :: (Integral a, Show a) => Positive a -> Positive a -> NonNegative a
invmod (Positive a) (Positive m) =
  let (r, x, _) = egcd (a `mod` m) m
      x'        = x `mod` m
  in  if r == 1
        then fromIntegral $ if x' < 0 then x' + m else x'
        else error $ "invmod: not coprime " ++ show (a, m)

-- Calculate the modular exponent: g^x (mod m), where g is either Positive or
-- NonNegative, x is Integer, and m is Positive.
expmod
  :: forall a b f
   . (Integral a, Show a, Ord a, f a <: a)
  => f a
  -> a
  -> Positive a
  -> NonNegative a
expmod g x m = case x `compare` 0 of
  LT -> invmod (fromIntegral $ (embed g :: a) ^ (-x)) m
  EQ -> 1
  GT -> ((embed g :: a) ^ x) `modulo` m

-- A QuickCheck property to test g^x g^(-x) == 1 (mod m).
propInvExpMod :: Positive Integer -> NonNegative Integer -> Property
propInvExpMod m x = do
  -- Given a value of m, we first find an arbitary coprime g of m.
  let gs = filter (coprime m) [2 .. m]
  forAll (elements gs) $ \a ->
    not (null gs) ==> coprime (expmod a (embed x) m * expmod a (-embed x) m) m

propModulo :: Integer -> Positive Integer -> Bool
propModulo x m =
  (y >= 0) && (y < m') && (y == x `mod` m' || y - (-x) `mod` m' == m')
 where
  y  = embed (x `modulo` m)
  m' = embed m


-------------------------------------------------------------------------------------
-- onCurve x y p = y * y - x * x * x - 7 `mod` p

-------------------------------------------------------------------------------------
-- Prime number functions
-- https://wiki.haskell.org/Prime_numbers

primes :: Num a => [a]
primes = fromIntegral <$> 2 : ops
 where
  ops = sieve 3 9 ops (inits ops) -- odd primes
  sieve x q ~(_ : pt) (fs : ft) =
    filter ((`all` fs) . ((> 0) .) . rem) [x, x + 2 .. q - 2]
      ++ sieve (q + 2) (head pt ^ 2) pt ft

isPrime :: (Num a, Ord a) => a -> Bool
isPrime n = n > 1 && n `elem` takeWhile (<= n) primes

newtype Prime a = Prime (Positive a) deriving (Show, Eq)

-- Produce arbitrary prime number less than `getSize` from QuickCheck.
instance (Integral a, Show a) => Arbitrary (Prime a) where
  arbitrary =
    Prime <$> (takeWhile . (>=) <$> getSize' <*> pure primes >>= elements)
    where getSize' = fromIntegral <$> getSize `suchThat` (> 1)

data CoPrime a = CoPrime (Positive a) (Positive a) deriving (Show, Eq)

instance (Arbitrary a, Integral a, Show a, Ord a) => Arbitrary (CoPrime a) where
  arbitrary = do
    p <- arbitrary `suchThat` (>= 2)
    g <- elements [1 .. p - 1] `suchThat` gcdEq (1 :: a) p
    pure $ CoPrime g p

test = do
  quickCheck propModulo
  quickCheck propInvExpMod
