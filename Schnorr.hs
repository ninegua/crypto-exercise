-------------------------------------------------------------------------------------
-- Schnorr Signatures - A Haskell Exercise
--
-- While studying Schnorr Signatures, I find most online materials either
-- imprecise, or inadequate. Often mathematical notations are being quoted
-- without fully explaining conditions, expecations, and variables/functions
-- domain and/or range. They are confusing enough that any attempt to turn them
-- into real programs is doomed, either producing something that is wrong, or
-- even worse, something that you think is correct but is actually wrong.
--
-- Here is my attempt to reconstruct the theory behind Schnorr Signatures (and
-- basic crypto primitives that are used) in a systematic manner, hopefully
-- precise enough to read and understand by a Haskell programmer.

{-# LANGUAGE RankNTypes #-}

module Schnorr where

import Data.List       (inits, nub, sort)
import Math            hiding (test)
import Test.QuickCheck

-------------------------------------------------------------------------------------
-- Multiplicative Group
--
-- Integers that are coprime to n from the set [1..n-1] form the multiplicative
-- group of integers modulo n.
groupOf :: Positive Integer -> [Positive Integer]
groupOf n = [ x | x <- [1 .. n - 1], coprime x n ]

-- The order of a multiplicative group is its size.
-- Sometimes it is as written as φ(n).
groupOrderOf :: Positive Integer -> Positive Integer
groupOrderOf n = fromIntegral $ length $ groupOf n

-- Given co-prime positive integer g and p, the multiplicative order of
-- g (mod p) is the smallest positive q such that g^q = 1 (mod p).
-- Sometimes it is also written as q = ord_p(g).
orderOf :: Positive Integer -> Positive Integer -> Positive Integer
orderOf g p
  | not (coprime g p) = error $ "orderOf: not coprime " ++ show (g, p)
  | otherwise = fromIntegral $ 1 + length (takeWhile ((/= 1) . (`modulo` p)) gs)
  where gs = g : map (g *) gs

-- As a consequence of Lagrange's theorem, ord_p(g) always divides φ(p).
-- We can check this property with the following test.
propMultOrd :: CoPrime Integer -> Property
propMultOrd (CoPrime g p) = groupOrderOf p `modulo` orderOf g p === 0

-------------------------------------------------------------------------------------
-- Modular Arithmetics
-- https://en.wikipedia.org/wiki/Modular_arithmetic
--
-- Below are some properties related to exponentiation, which only hold
-- under two conditions: q=φ(p), and g and p are positive coprime numbers.
--
--   a = b   (mod q)  ==>  g^a = g^b       (mod p)
--   a = b+c (mod q)  ==>  g^a = g^(b + c) (mod p)
--   a = bc  (mod q)  ==>  g^a = (g^b)^c   (mod p)
--
propModExp :: CoPrime Integer -> Property
propModExp (CoPrime g p) = do
  let q        = groupOrderOf p
      positive = arbitrary :: Gen (Positive Integer)
  forAll ((,) <$> positive <*> positive) $ \(a, b) ->
    let u = (a + b) `modulo` q
        v = (a * b) `modulo` q
        s = a `modulo` q
    in  (pow g u `modulo` p === (pow g a * pow g b) `modulo` p)
          .&. (pow g v `modulo` p === pow (pow g a) b `modulo` p)
          .&. (pow g a `modulo` p === pow g s `modulo` p)

-------------------------------------------------------------------------------------
--
-- Discrete Logarithm Problem (DLOG).
-- https://en.wikipedia.org/wiki/Discrete_logarithm
--
-- Choose g, p, q such that f(x) = g^x (mod p), where 0 <= x < q, is hard to
-- invert, or in other words, it is hard to guess what x is just from a value
-- of f(x).
--
-- One solution is the multiplicative group of integers modulo prime number p.
-- https://en.wikipedia.org/wiki/Multiplicative_group_of_integers_modulo_n
--
-- 1. Choose q that is a large prime such that p = 2q + 1 is also prime.
--
-- 2. Define G = [g | g <- [0..p-1], g ^ q == 1 (mod p)], which is called
--    the multiplicative group of prime order q modulo p.
--
-- 3. It can be proven that G has q elements.
--
-- 4. Every g in G where g /= 1 is called a generator.
--
-- 5. f(x) = g ^ x (mod p) is a bijective mapping from [0..q-1] to G.
--
-- Essentially this means every element in [f(x) | x <- [0..q-1]] is unique,
-- and is a number in G.

-- A set of (p, q) pairs used for testing, with maximum prime < 5000.
randomPQ :: Gen (Positive Integer, Positive Integer)
randomPQ =
  resize 2500
    $          ((\(Prime q) -> (2 * q + 1, q)) <$> arbitrary)
    `suchThat` (isPrime . fst)

-- One way to calculate generators is by testing all values in [1..p-1].
-- Technically, generators are greater than 1 for all interesting p and q.
generators :: Positive Integer -> Positive Integer -> [Positive Integer]
generators p q | p > 1     = filter (\g -> pow g q `modulo` p == 1) [1 .. p - 1]
               | otherwise = []

-- Arbitrary generator that is greater than 1
generator :: Positive Integer -> Positive Integer -> Gen (Positive Integer)
generator p q = elements (generators p q) `suchThat` (> 1)

-- Calculate the range (co-domain) of f(x) = g^x (mod p).
rangeOfF
  :: Positive Integer
  -> Positive Integer
  -> Positive Integer
  -> [Positive Integer]
rangeOfF g p q =
  nub $ sort [ positive (expmod g x p) | x <- [0 .. embed q - 1] ]

-- For any qualifying pair (p, q), let g be a generator of (p, q), we can
-- verify that G is the co-domain of f(x) = g^x (mod p)
--
-- This is only true for prime numbers p and q.
propDLOG :: Property
propDLOG = forAll randomPQG $ \(p, q, g) -> rangeOfF g p q == generators p q
 where
  randomPQG = do
    (p, q) <- randomPQ
    g      <- generator p q
    pure (p, q, g)

-- Instead of iterating through all [0..p-1] to find generators, we can also
-- start with a known generator, and apply f to find all.
generators' :: Positive Integer -> Positive Integer -> [Positive Integer]
generators' p q = rangeOfF (generators p q !! 1) p q

-------------------------------------------------------------------------------------
-- Fiat-Shamir heuristic turns an interactive proof of a known secret into a
-- non-interactive one, using random oracle access.
-- https://en.wikipedia.org/wiki/Fiat–Shamir_heuristic
-- (This wiki page is a bit confusing, where n is really the same as p)
--
-- Non-interactive proof of knowing a secret x without revealing it, in
-- y = g ^ x (mod p), where y is known as the public key.

-- A triple of (p, g, y), where y is the public key, and p and g are parameters
-- necessary to carry out computation using y.
type PubKey = (Positive Integer, Positive Integer, NonNegative Integer)

-- A tuple of (q, x), where x is the secret, and q is a parameter required to
-- perform computation using x, but not necessarily secret.
type SecKey = (Positive Integer, NonNegative Integer)

-- Generate a random key pair given parameter (p, q), by choosing a random
-- x in the range [0, embed q - 1].
--
-- Note that in practice, x = 0 is a trivial case that should be ignored.
keypairs :: Positive Integer -> Positive Integer -> Gen (PubKey, SecKey)
keypairs p q = do
  g <- generator p q
  x <- choose (0, embed q - 1)
  pure ((p, g, expmod g x p), (q, fromInteger x))

-- A made-up hash function that is absolutely insecure.
type Hashing = forall a . Show a => a -> NonNegative Integer
hash :: Hashing
hash = fromIntegral . sum . map fromEnum . show

-- A proof (t, r) is produced by:
--
-- Choose a random v in [0..q-1]
-- let t = g^v (mod p)
-- let c = hash(g, y, t) (mod q)
-- let r = v - cx (mod q)
--
-- The resulting proof can be checked by anyone with knowledge of PubKey.
type Proof = (NonNegative Integer, NonNegative Integer)
prove :: Hashing -> PubKey -> SecKey -> Gen Proof
prove hash (p, g, y) (q, x) = do
  v <- choose (0, embed q - 1)
  let t = expmod g v p
      c = hash (g, y, t)
      r = (v - embed (c * x)) `modulo` q
  pure (t, r)

-- Verifying the proof (t, r) by checking if t == g^r y^c (mod p).
--
-- This always holds because (where all exponent values are modulo q):
--
--       g^r y^c (mod p)
--     = g^r (g^x)^c (mod p)
--     = g^(r + xc) (mod p)
--     = g^(v - cx + xc) (mod p)
--     = g^v (mod p)
--     = t
verifyProof :: Hashing -> PubKey -> Proof -> Property
verifyProof hash (p, g, y) (t, r) =
  let c = hash (g, y, t)
  in  t === (pow g r `modulo` p * pow y c `modulo` p) `modulo` p

-- For any key pair, we can check that a random proof can always be verified.
propFiatShamir :: Property
propFiatShamir = forAll randomPQ $ \(p, q) -> forAll (keypairs p q)
  $ \(pub, sec) -> forAll (prove hash pub sec) $ verifyProof hash pub

-------------------------------------------------------------------------------------
-- Schnorr Signature
-- https://en.wikipedia.org/wiki/Schnorr_signature

-- For a given message msg, A Signature (c, r) is produced by:
--
-- 1. Choose a random v in [0..q-1]
-- 2. Compute t = g^v (mod p)
-- 3. Compute c =  hash(t, msg)
-- 4. Compute r = v - cx (mod q)
--
-- The resulting proof can be checked by anyone with knowledge of msg and PubKey.
type Signature = (NonNegative Integer, NonNegative Integer)
sign :: Show a => Hashing -> PubKey -> SecKey -> a -> Gen Signature
sign hash (p, g, a) (q, x) msg = do
  v <- choose (0, embed q - 1)
  let t = expmod g v p
      c = hash (t, msg)
      r = (v - embed (c * x)) `modulo` q
  pure (c, r)

-- Verifying the proof (c, r) by:
--
-- 1. Compute t' = g^r y^c (mod p).
-- 2. Check if hash(t', msg) == c
--
-- This always holds because (where all exponent values are modulo q):
--
--       g^r y^c (mod p)
--     = g^r (g^x)^c (mod p)
--     = g^(r + xc) (mod p)
--     = g^(v - cx + xc) (mod p)
--     = g^v (mod p)
--     = t
--
-- Therefore t' = t, and hash(t', msg) == hash(t, msg) == c
verify :: Show a => Hashing -> PubKey -> a -> Signature -> Property
verify hash (p, g, y) msg (c, r) =
  let t = (pow g r `modulo` p * pow y c `modulo` p) `modulo` p
  in  hash (t, msg) === c

-- For any key pair and a random message, we can check that a Schnorr signature
-- always be verified.
propSchnorr :: String -> Property
propSchnorr msg = forAll randomPQ $ \(p, q) ->
  forAll (keypairs p q) $ \(pub, sec) ->
    forAll (sign hash pub sec msg) $ \sig -> verify hash pub msg sig

-------------------------------------------------------------------------------------
test :: IO ()
test = do
  quickCheck propMultOrd
  quickCheck propModExp
  quickCheck propDLOG
  quickCheck propFiatShamir
  quickCheck propSchnorr


