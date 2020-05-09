-- |
-- Module      :  Cryptol.Eval.Concrete.Value
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
-- {-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.Concrete.Value
  ( BV(..)
  , binBV
  , unaryBV
  , bvVal
  , ppBV
  , mask
  , integerToChar
  , lg2
  , Value
  , Concrete(..)
  , liftBinIntMod
  , doubleAndAdd
  ) where

import qualified Control.Exception as X
import Data.Bits
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr
import Data.Parameterized.Pair
import Data.Parameterized.Some
import Numeric (showIntAtBase)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Value
import Cryptol.TypeCheck.Solver.InfNat (genLog)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

data Concrete = Concrete deriving Show

type Value = GenValue Concrete

-- | Concrete bitvector values: width, value
-- Invariant: The value must be within the range 0 .. 2^width-1
data BV = forall w . BV !(NatRepr w) !(BV.BV w)

instance Show BV where
  show = show . bvVal

binBV :: Applicative m
      => String
      -> (forall w . NatRepr w -> BV.BV w -> BV.BV w -> BV.BV w)
      -> BV -> BV -> m BV
binBV fName f (BV w x) (BV w' y)
  | Just Refl <- w `testEquality` w' = pure $! BV w (f w x y)
  | otherwise = panic ("Called " ++ fName ++ " on words of different sizes")
                [show w, show w']

unaryBV :: Applicative m
     => (forall w . NatRepr w -> BV.BV w -> BV.BV w)
     -> BV -> m BV
unaryBV f (BV w x) = pure $! BV w (f w x)

-- -- | Apply an integer function to the values of bitvectors.
-- --   This function assumes both bitvectors are the same width.
-- binBV :: Applicative m => (Integer -> Integer -> Integer) -> BV -> BV -> m BV
-- binBV f (BV w x) (BV _ y) = pure $! mkBv w (f x y)
-- {-# INLINE binBV #-}

-- -- | Apply an integer function to the values of a bitvector.
-- --   This function assumes the function will not require masking.
-- unaryBV :: (Integer -> Integer) -> BV -> BV
-- unaryBV f (BV w x) = mkBv w $! f x
-- {-# INLINE unaryBV #-}

bvVal :: BV -> Integer
bvVal (BV _w x) = BV.asUnsigned x
{-# INLINE bvVal #-}

-- -- | Smart constructor for 'BV's that checks for the width limit
-- mkBv :: Integer -> Integer -> BV
-- mkBv w i = BV w (mask w i)

-- signedBV :: BV -> Integer
-- signedBV (BV i x) = signedValue i x

-- signedValue :: Integer -> Integer -> Integer
-- signedValue i x = if testBit x (fromInteger (i-1)) then x - (1 `shiftL` (fromInteger i)) else x

integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0


ppBV :: PPOpts -> BV -> Doc
ppBV opts (BV (intValue -> width) (BV.BV i))
  | base > 36 = integer i -- not sure how to rule this out
  | asciiMode opts width = text (show (toEnum (fromInteger i) :: Char))
  | otherwise = prefix <.> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <.> padding 1
    8  -> text "0o" <.> padding 3
    10 -> empty
    16 -> text "0x" <.> padding 4
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"

-- Concrete Big-endian Words ------------------------------------------------------------

mask ::
  Integer  {- ^ Bit-width -} ->
  Integer  {- ^ Value -} ->
  Integer  {- ^ Masked result -}
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. (bit (fromInteger w) - 1)

instance Backend Concrete where
  type SBit Concrete = Bool
  type SWord Concrete = BV
  type SInteger Concrete = Integer
  type SEval Concrete = Eval

  raiseError _ err = io (X.throwIO err)

  assertSideCondition _ True _ = return ()
  assertSideCondition _ False err = io (X.throwIO err)

  wordLen _ (BV w _) = intValue w
  wordAsChar _ (BV _ x) = Just $! integerToChar (BV.asUnsigned x)

  wordBit _ (BV w x) idx = pure $! BV.testBit' (fromInteger (intValue w - 1 - idx)) x

  wordUpdate _ (BV w x) idx b
    | Just (Some i) <- someNat (intValue w - 1 - idx)
    , NatCaseLT LeqProof <- testNatCases i w = if b
                                               then pure $! BV w (BV.setBit i x)
                                               else pure $! BV w (BV.clearBit w i x)
    | otherwise = panic "Called wordUpdate on incompatible width and index"
                  [show w, show idx]

  isReady _ (Ready _) = True
  isReady _ _ = False

  mergeEval _sym f c mx my =
    do x <- mx
       y <- my
       f c x y

  sDeclareHole _ = blackhole
  sDelayFill _ = delayFill

  ppBit _ b | b         = text "True"
            | otherwise = text "False"

  ppWord _ = ppBV

  ppInteger _ _opts i = integer i

  bitLit _ b = b
  bitAsLit _ b = Just b

  bitEq _  x y = pure $! x == y
  bitOr _  x y = pure $! x .|. y
  bitAnd _ x y = pure $! x .&. y
  bitXor _ x y = pure $! x `xor` y
  bitComplement _ x = pure $! complement x

  iteBit _ b x y  = pure $! if b then x else y
  iteWord _ b x y = pure $! if b then x else y
  iteInteger _ b x y = pure $! if b then x else y

  wordLit _ iw i = case mkNatRepr (fromInteger iw) of
    Some w -> pure $! BV w (BV.mkBV w i)
  wordAsLit _ (BV w i) = Just (intValue w, BV.asUnsigned i)
  integerLit _ i = pure i
  integerAsLit _ = Just

  wordToInt _ (BV _ x) = pure (BV.asUnsigned x)
  wordFromInt _ iw x = case mkNatRepr (fromInteger iw) of
    Some w -> pure $! BV w (BV.mkBV w x)

  packWord _ bits = case BV.bitsBE bits of
    Pair w bv -> pure $! BV w bv

  unpackWord _ (BV w bv) = pure $ BV.asBitsBE w bv

  joinWord _ (BV i x) (BV j y) = pure $! BV (i `addNat` j) (BV.concat i j x y)

  splitWord _ leftW rightW (BV w x) = case (someNat leftW, someNat rightW) of
    (Just (Some lw), Just (Some rw))
      | Just LeqProof <- lw `testLeq` w
      , Just LeqProof <- rw `testLeq` w
      , Just LeqProof <- (rw `addNat` lw) `testLeq` w
      , Just Refl <- (lw `addNat` rw) `testEquality` w -> do
          let lx = BV.select rw lw x
              rx = BV.select (knownNat @0) rw x
          pure (BV lw lx, BV rw rx)
    _ -> panic "Attempt to split word into incompatible subword sizes: splitWord"
         ["Left: " ++ show leftW, "Right: " ++ show rightW, "Total: " ++ show w]

  extractWord _ n i (BV w x) = case (someNat n, someNat i) of
    (Just (Some nw), Just (Some iw)) | Just LeqProof <- (iw `addNat` nw) `testLeq` w ->
                                       pure $ BV nw (BV.select iw nw x)
    _ -> panic "Attempt to extract from word with incompatible index and width: extractWord"
         ["Index: " ++ show i, "Extract: " ++ show n, "From: " ++ show w]
    
  wordEq _ (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = pure $! x == y
    | otherwise = panic "Attempt to compare words of different sizes: wordEq" [show i, show j]

  wordSignedLessThan _ (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j
    , Right LeqProof <- isZeroOrGT1 i = pure $! BV.slt i x y
    | otherwise = panic "Attempt to compare words of different or illegal sizes: wordSignedLessThan" [show i, show j]

  wordLessThan _ (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = pure $! BV.ult x y
    | otherwise = panic "Attempt to compare words of different sizes: wordLessThan" [show i, show j]

  wordGreaterThan _ (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = pure $! BV.ult y x
    | otherwise = panic "Attempt to compare words of different sizes: wordGreaterThan" [show i, show j]

  wordAnd _ = binBV "wordAnd" (const BV.and)

  wordOr _ = binBV "wordOr" (const BV.or)

  wordXor _ = binBV "wordXor" (const BV.xor)

  wordComplement _ = unaryBV BV.complement

  wordPlus _ = binBV "wordPlus" BV.add

  wordNegate _ = unaryBV BV.negate

  wordMinus _ = binBV "wordMinus" BV.sub

  wordMult _ = binBV "wordMult" BV.mul

  wordDiv sym (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = case isZeroOrGT1 i of
        Left Refl -> pure $! BV i (BV.zero i)
        Right LeqProof  -> do assertSideCondition sym (y /= BV.zero i) DivideByZero
                              pure $! BV i (BV.uquot x y)
    | otherwise = panic "Called wordDiv on words on different sizes:" [show i, show j]
  
  wordMod sym (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = case isZeroOrGT1 i of
        Left Refl -> pure $! BV i (BV.zero i)
        Right LeqProof -> do assertSideCondition sym (y /= BV.zero i) DivideByZero
                             pure $! BV i (BV.urem x y)
    | otherwise = panic "Called wordMod on words on different sizes:" [show i, show j]

  wordSignedDiv sym (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = case isZeroOrGT1 i of
        Left Refl -> pure $! BV i (BV.zero i)
        Right LeqProof -> do assertSideCondition sym (y /= BV.zero i) DivideByZero
                             pure $! BV i (BV.squot i x y)
    | otherwise = panic "Called wordSignedDiv on words on different sizes:" [show i, show j]
  
  wordSignedMod sym (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = case isZeroOrGT1 i of
        Left Refl -> pure $! BV i (BV.zero i)
        Right LeqProof -> do assertSideCondition sym (y /= BV.zero i) DivideByZero
                             pure $! BV i (BV.srem i x y)
    | otherwise = panic "Called wordSignedMod on words on different sizes:" [show i, show j]

  wordExp _ (BV i x) (BV j y)
    | Just Refl <- i `testEquality` j = case isZeroOrGT1 i of
        Left Refl -> pure $! BV i (BV.zero i)
        Right LeqProof -> do let modulus = 0 `setBit` widthVal i
                             pure . BV i . BV.mkBV i $! doubleAndAdd (BV.asUnsigned x) (BV.asUnsigned y) modulus
    | otherwise = panic "Attempt to exp words of different sizes: wordSignedMod" [show i, show j]
    

  wordLg2 _ (BV i x) = pure $! BV i $ BV.mkBV i $ lg2 (BV.asUnsigned x)

  intEq _ x y = pure $! x == y
  intLessThan _ x y = pure $! x < y
  intGreaterThan _ x y = pure $! x > y

  intPlus  _ x y = pure $! x + y
  intMinus _ x y = pure $! x - y
  intNegate _ x  = pure $! negate x
  intMult  _ x y = pure $! x * y
  intDiv sym x y =
    do assertSideCondition sym (y /= 0) DivideByZero
       pure $! x `div` y
  intMod sym x y =
    do assertSideCondition sym (y /= 0) DivideByZero
       pure $! x `mod` y
  intExp sym x y =
    do assertSideCondition sym (y >= 0) NegativeExponent
       pure $! x ^ y
  intLg2 sym x =
    do assertSideCondition sym (x >= 0) LogNegative
       pure $! lg2 x

  intToZn _ 0 _ = evalPanic "intToZn" ["0 modulus not allowed"]
  intToZn _ m x = pure $! x `mod` m

  -- NB: requires we maintain the invariant that
  --     Z_n is in reduced form
  znToInt _ _m x = pure x
  znEq _ _m x y = pure $! x == y

  znPlus  _ = liftBinIntMod (+)
  znMinus _ = liftBinIntMod (-)
  znMult  _ = liftBinIntMod (*)
  znNegate _ 0 _ = evalPanic "znNegate" ["0 modulus not allowed"]
  znNegate _ m x = pure $! (negate x) `mod` m

  znExp _sym m x y
    | m == 0    = evalPanic "znExp" ["0 modulus not allowed"]
    | otherwise = pure $! (doubleAndAdd x y m) `mod` m

{-# INLINE liftBinIntMod #-}
liftBinIntMod :: Monad m =>
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> m Integer
liftBinIntMod op m x y
  | m == 0    = evalPanic "znArithmetic" ["0 modulus not allowed"]
  | otherwise = pure $ (op x y) `mod` m

doubleAndAdd :: Integer -- ^ base
             -> Integer -- ^ exponent mask
             -> Integer -- ^ modulus
             -> Integer
doubleAndAdd base0 expMask modulus = go 1 base0 expMask
  where
  go acc base k
    | k > 0     = acc' `seq` base' `seq` go acc' base' (k `shiftR` 1)
    | otherwise = acc
    where
    acc' | k `testBit` 0 = acc `modMul` base
         | otherwise     = acc

    base' = base `modMul` base

    modMul x y = (x * y) `mod` modulus
