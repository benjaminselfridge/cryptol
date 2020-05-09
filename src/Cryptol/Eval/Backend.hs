{-# LANGUAGE DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Cryptol.Eval.Backend
  ( Backend(..)
  , sDelay
  , invalidIndex
  , cryUserError
  , cryNoPrimError
  ) where

import Control.Monad.IO.Class
import qualified Data.BitVector.Sized as BV
import Data.Kind (Type)
import Data.Parameterized.NatRepr
import GHC.TypeNats

import Cryptol.Eval.Monad
import Cryptol.TypeCheck.AST(Name)
import Cryptol.Utils.PP


invalidIndex :: Backend sym => sym -> Integer -> SEval sym a
invalidIndex sym = raiseError sym . InvalidIndex . Just

cryUserError :: Backend sym => sym -> String -> SEval sym a
cryUserError sym = raiseError sym . UserError

cryNoPrimError :: Backend sym => sym -> Name -> SEval sym a
cryNoPrimError sym = raiseError sym . NoPrim


{-# INLINE sDelay #-}
-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Raise a loop
--   error if the resulting thunk is forced during its own evaluation.
sDelay :: Backend sym => sym -> Maybe String -> SEval sym a -> SEval sym (SEval sym a)
sDelay sym msg m =
  let msg'  = maybe "" ("while evaluating "++) msg
      retry = raiseError sym (LoopError msg')
   in sDelayFill sym m retry

-- | This type class defines a collection of operations on bits, words and integers that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class MonadIO (SEval sym) => Backend sym where
  type SBit sym :: Type
  type SWord sym :: Nat -> Type
  type SInteger sym :: Type
  type SEval sym :: Type -> Type

  -- ==== Evaluation monad operations ====

  -- | Check if an operation is "ready", which means its
  --   evaluation will be trivial.
  isReady :: sym -> SEval sym a -> Bool

  -- | Produce a thunk value which can be filled with its associated computation
  --   after the fact.  A preallocated thunk is returned, along with an operation to
  --   fill the thunk with the associated computation.
  --   This is used to implement recursive declaration groups.
  sDeclareHole :: sym -> String -> SEval sym (SEval sym a, SEval sym a -> SEval sym ())

  -- | Delay the given evaluation computation, returning a thunk
  --   which will run the computation when forced.  Run the 'retry'
  --   computation instead if the resulting thunk is forced during
  --   its own evaluation.
  sDelayFill :: sym -> SEval sym a -> SEval sym a -> SEval sym (SEval sym a)

  -- | Merge the two given computations according to the predicate.
  mergeEval ::
     sym ->
     (SBit sym -> a -> a -> SEval sym a) {- ^ A merge operation on values -} ->
     SBit sym {- ^ The condition -} ->
     SEval sym a {- ^ The "then" computation -} ->
     SEval sym a {- ^ The "else" computation -} ->
     SEval sym a

  -- | Assert that a condition must hold, and indicate what sort of
  --   error is indicated if the condition fails.
  assertSideCondition :: sym -> SBit sym -> EvalError -> SEval sym ()

  -- | Indiciate that an error condition exists
  raiseError :: sym -> EvalError -> SEval sym a


  -- ==== Pretty printing  ====
  -- | Pretty-print an individual bit
  ppBit :: sym -> SBit sym -> Doc

  -- | Pretty-print a word value
  ppWord :: sym -> PPOpts -> SWord sym w -> Doc

  -- | Pretty-print an integer value
  ppInteger :: sym -> PPOpts -> SInteger sym -> Doc


  -- ==== Identifying literal values ====

  -- | Determine if this symbolic bit is a boolean literal
  bitAsLit :: sym -> SBit sym -> Maybe Bool

  -- | The number of bits in a word value.
  wordLen :: sym -> SWord sym w -> NatRepr w

  -- | Determine if this symbolic word is a literal.
  --   If so, return the bit width and value.
  wordAsLit :: sym -> SWord sym w -> Maybe (NatRepr w, BV.BV w)

  -- | Attempt to render a word value as an ASCII character.  Return 'Nothing'
  --   if the character value is unknown (e.g., for symbolic values).
  wordAsChar :: sym -> SWord sym w -> Maybe Char

  -- | Determine if this symbolic integer is a literal
  integerAsLit :: sym -> SInteger sym -> Maybe Integer

  -- ==== Creating literal values ====

  -- | Construct a literal bit value from a boolean.
  bitLit :: sym -> Bool -> SBit sym

  -- | Construct a literal word value given a bit width and a value.
  wordLit ::
    sym ->
    NatRepr w {- ^ Width -} ->
    BV.BV w   {- ^ Value -} ->
    SEval sym (SWord sym w)

  -- | Construct a literal integer value from the given integer.
  integerLit ::
    sym ->
    Integer {- ^ Value -} ->
    SEval sym (SInteger sym)

  -- ==== If/then/else operations ====
  iteBit :: sym -> SBit sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  iteWord :: sym -> SBit sym -> SWord sym w -> SWord sym w -> SEval sym (SWord sym w)
  iteInteger :: sym -> SBit sym -> SInteger sym -> SInteger sym -> SEval sym (SInteger sym)


  -- ==== Bit operations ====
  bitEq  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitOr  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitAnd :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitXor :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitComplement :: sym -> SBit sym -> SEval sym (SBit sym)


  -- ==== Word operations ====

  -- | Extract the numbered bit from the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordBit :: w' + 1 <= w =>
    sym ->
    SWord sym w ->
    NatRepr w' {- ^ Bit position to extract -} ->
    SEval sym (SBit sym)

  -- | Update the numbered bit in the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordUpdate :: w' + 1 <= w =>
    sym ->
    SWord sym w ->
    NatRepr w' {- ^ Bit position to update -} ->
    SBit sym ->
    SEval sym (SWord sym w)

  -- | Construct a word value from a finite sequence of bits.
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   first element of the list will be the most significant bit.
  packWord ::
    sym ->
    [SBit sym] ->
    SEval sym (Some (SWord sym))

  -- | Deconstruct a packed word value in to a finite sequence of bits.
  --   NOTE: this produces a list of bits that represent a big-endian word, so
  --   the most significant bit is the first element of the list.
  unpackWord ::
    sym ->
    SWord sym w ->
    SEval sym [SBit sym]

  -- | Construct a packed word of the specified width from an integer value.
  wordFromInt ::
    sym ->
    NatRepr w {- ^ bit-width -} ->
    SInteger sym ->
    SEval sym (SWord sym w)

  -- | Concatenate the two given word values.
  --   NOTE: the first argument represents the more-significant bits
  joinWord ::
    sym ->
    SWord sym w ->
    SWord sym w' ->
    SEval sym (SWord sym (w+w'))

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  --   The two integer sizes must sum to the length of the given word value.
  splitWord ::
    sym ->
    NatRepr w  {- ^ left width -} ->
    NatRepr w' {- ^ right width -} ->
    SWord sym (w+w') ->
    SEval sym (SWord sym w, SWord sym w')

  -- | Extract a subsequence of bits from a packed word value.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation @extractWord n i w@ is equivalent to
  --   first shifting @w@ right by @i@ bits, and then truncating to
  --   @n@ bits.
  extractWord :: ix + w' <= w =>
    sym ->
    NatRepr w' {- ^ Number of bits to take -} ->
    NatRepr ix {- ^ starting bit -} ->
    SWord sym w ->
    SEval sym (SWord sym w')

  -- | Bitwise OR
  wordOr ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Bitwise AND
  wordAnd ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Bitwise XOR
  wordXor ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Bitwise complement
  wordComplement ::
    sym ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement addition of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordPlus ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement subtraction of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordMinus ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement multiplication of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. The high bits of the
  --   multiplication are silently discarded.
  wordMult ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement unsigned division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordDiv ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement unsigned modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordMod ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement signed division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedDiv ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement signed modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedMod ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Exponentiation of bitvectors.
  wordExp ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | 2's complement negation of bitvectors
  wordNegate ::
    sym ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Compute rounded-up log-2 of the input
  wordLg2 ::
    sym ->
    SWord sym w ->
    SEval sym (SWord sym w)

  -- | Test if two words are equal.  Arguments must have the same width.
  wordEq ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SBit sym)

  -- | Signed less-than comparison on words.  Arguments must have the same width.
  wordSignedLessThan ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SBit sym)

  -- | Unsigned less-than comparison on words.  Arguments must have the same width.
  wordLessThan ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SBit sym)

  -- | Unsigned greater-than comparison on words.  Arguments must have the same width.
  wordGreaterThan ::
    sym ->
    SWord sym w ->
    SWord sym w ->
    SEval sym (SBit sym)

  -- | Construct an integer value from the given packed word.
  wordToInt ::
    sym ->
    SWord sym w ->
    SEval sym (SInteger sym)

  -- ==== Integer operations ====

  -- | Addition of unbounded integers.
  intPlus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Negation of unbounded integers
  intNegate ::
    sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of unbounded integers.
  intMinus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of unbounded integers.
  intMult ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer division, rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @div@ operation.
  intDiv ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer modulus, with division rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @mod@ operation.
  intMod ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer exponentiation.  The second argument must be non-negative.
  intExp ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Rounded-up log-2 of the input
  intLg2 ::
    sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Equality comparison on integers
  intEq ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Less-than comparison on integers
  intLessThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Greater-than comparison on integers
  intGreaterThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)


  -- ==== Operations on Z_n ====

  -- | Turn an integer into a value in Z_n
  intToZn ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Transform a Z_n value into an integer, ensuring the value is properly
  --   reduced modulo n
  znToInt ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Addition of integers modulo n, for a concrete positive integer n.
  znPlus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Additive inverse of integers modulo n
  znNegate ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of integers modulo n, for a concrete positive integer n.
  znMinus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of integers modulo n, for a concrete positive integer n.
  znMult ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Equality test of integers modulo n
  znEq ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)


  -- ==== Z_n operations defined via projection to the integers ====

  -- | Division of integers modulo n, for a concrete positive integer n.
  --   NOTE: this is integer division on the initial segement of Z,
  --   and not the multiplicative inverse in Z_p.
  znDiv ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)
  znDiv sym m x y =
    do x' <- znToInt sym m x
       y' <- znToInt sym m y
       intToZn sym m =<< intDiv sym x' y'

  -- | Modulus of integers modulo n, for a concrete positive integer n.
  --   NOTE: this is the modulus corresponding to integer division on the initial
  --   segement of Z, and not related to multiplicative inverse in Z_p.
  znMod ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)
  znMod sym m x y =
    do x' <- znToInt sym m x
       y' <- znToInt sym m y
       intToZn sym m =<< intMod sym x' y'

  -- | Exponentation of integers modulo n
  znExp ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)
  znExp sym m x y =
    do x' <- znToInt sym m x
       y' <- znToInt sym m y
       intToZn sym m =<< intExp sym x' y'

  -- | Log base 2 of integers modulo n.
  znLg2 ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)
  znLg2 sym m x =
    do x' <- znToInt sym m x
       intToZn sym m =<< intLg2 sym x'

  -- | Less-than test of integers modulo n.  Note this test
  --   first computes the reduced integers and compares.
  znLessThan ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)
  znLessThan sym m x y =
    do x' <- znToInt sym m x
       y' <- znToInt sym m y
       intLessThan sym x' y'

  -- | Greater-than test of integers modulo n.  Note this test
  --   first computes the reduced integers and compares.
  znGreaterThan ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)
  znGreaterThan sym m x y =
    do x' <- znToInt sym m x
       y' <- znToInt sym m y
       intGreaterThan sym x' y'
