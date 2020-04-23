-------------------------------------------------------------------------------------
-- Elliptic Curve Cryptography - A Haskell Exercise
--
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module ECC where

import Data.List       (inits, sort)
import Data.Maybe
import Math            hiding (test)
import Test.QuickCheck

data Point a = Point (NonNegative a) (NonNegative a) deriving Eq

instance Show a => Show (Point a) where
  show (Point (NonNegative x) (NonNegative y)) = show (x, y)

-- A curve y
data Curve a
  = Curve (NonNegative a) -- a
          (NonNegative a) -- b
          (Positive a)    -- p
  deriving (Eq, Show)

-- The k1 curve as used by secp256p1: y^2 = x^3 + 7 (mod p)
makeK1 :: Integral a => Positive a -> Curve a
makeK1 = Curve 0 7

-------------------------------------------------------------------------------------
onCurve :: Integral a => Curve a -> Point a -> Bool
onCurve (Curve a b p) (Point x y) =
  minus p (x * x * x + a * x + b) (y * y) == 0

point :: forall a . Integral a => Curve a -> Gen (Point a)
point curve@(Curve _ _ p) = flip suchThat (onCurve curve) $ do
  let range = [0 .. embed p - 1]
  x <- elements range
  y <- elements range
  pure $ Point x y

-------------------------------------------------------------------------------------
-- Adding two points.
--
-- Given point A=(x0, y0) and B=(x1, y1) on a curve: y^2 = x^3 + ax + b,
-- find C=A+B.
--
-- Steps:
--
-- 1. Since A,B forms a line, we find its slope m as follows:
--
--   a. When x0 == x1:
--
--     (i) if y0 == y1 /= 0, then C=2A, which is calculated as follows:
--
--         The slope m at A is the derivative at x0, which is calculated to be:
--
--           m = (3*x0^2 + a) / (2*y0)
--
--     (ii) if y0 == y1 == 0, or y0 /= y1, then by the symmetry of an elliptic
--          curve, A,B must be a vertical line and y0 + y1 = 0. In this case C
--          does not exist, and by convention C is called an infinity point.
--
--   b. When x0 /= x1, let the line A,B be y = mx + v
--
--      m = (y0 - y1) / (x0 - x1)
--
-- 2. Let the line A,B,C be y = mx + v, since A,B,C are all on the curve too, by
--    solving the equation we have:
--
--      x2 = m^m - x0 - x1
--      y2 = mx2 + v
--      v  = y0 - mx0 = y1 - mx1 = (x0y1 - x1y0) / (x0 - x1)
--
-- 3. The solution C is the opposite of (x2, y2), which is (x2, -y2)
--
-- 4. When applied to modular integer math, all above calculation should be (mod p).
--
addPoint
  :: (Eq a, Integral a, Num a, Ord a)
  => Curve a
  -> Maybe (Point a)
  -> Maybe (Point a)
  -> Maybe (Point a)
addPoint (Curve a b p) u       Nothing = u
addPoint (Curve a b p) Nothing v       = v
addPoint (Curve a b p) (Just (Point x0 y0)) (Just (Point x1 y1))
  | dx == 0 && dy /= 0 = Nothing
  | otherwise = ifZero
    dx
    (ifZero y0 Nothing (\y0 -> compute $ (3 * x0 * x0 + a) * invmod (2 * y0) p))
    (\dx -> compute $ dy * invmod dx p)
 where
  dx = minus p x0 x1
  dy = minus p y0 y1
  compute m =
    let x2 = minus p (m * m) (x0 + x1)
        y2 = (m * x2 + v) `modulo` p
        v  = minus p y0 (m * x0)
    in  Just (Point x2 (minus p 0 y2))

propAddPoint :: (Integral a, Show a) => Prime a -> Property
propAddPoint (Prime p) = forAll
  (do
    let curve = makeK1 p
        add   = addPoint curve
    u <- Just <$> point curve
    v <- Just <$> point curve
    w <- Just <$> point curve
    let x = add (add u v) w
        y = add u (add v w)
    pure (curve, u, v, w, x, y)
  )
  (\(curve, u, v, w, x, y) ->
    p > 2 ==> (x === y .&. (isJust x ==> onCurve curve (fromJust x)))
  )

test :: IO ()
test = quickCheck (propAddPoint <$> resize 1000 arbitrary)
