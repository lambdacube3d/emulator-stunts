{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Word1 where

import Data.Word
import Data.Bits
import Data.Maybe
import Control.Arrow
import Control.Applicative
import Control.Lens

---------------------------

newtype Word1 = Word1 { _bit0 :: Bool }
    deriving (Eq, Ord, Enum)

bit0 :: Iso' Word1 Bool
bit0 = iso _bit0 Word1

instance Show Word1 where
    show = show . fromIntegral

instance Bits Word1 where
    Word1 a .&. Word1 b = Word1 $ a && b
    Word1 a .|. Word1 b = Word1 $ a || b
    Word1 a `xor` Word1 b = Word1 $ a /= b
    rotate w _ = w
    shift w 0 = w
    shift _ _ = 0
    complement (Word1 a) = Word1 $ not a
    popCount (Word1 a) = fromEnum a
    testBit (Word1 a) 0 = a
    bit 0 = 1
    bit _ = 0
    bitSizeMaybe _ = Just 1
    bitSize _ = 1
    isSigned _ = False

instance FiniteBits Word1 where
    finiteBitSize _ = 1

instance Num Word1 where
    fromInteger = Word1 . toEnum . fromInteger . (`mod` 2)
    Word1 a + Word1 b = Word1 (a /= b)
    Word1 a - Word1 b = Word1 (a /= b)
    Word1 a * Word1 b = Word1 (a && b)
    abs = id
    signum = id

instance Real Word1 where
    toRational = toRational . fromEnum . (^. bit0)

instance Integral Word1 where
    toInteger = toInteger . fromEnum . (^. bit0)
    a `quotRem` 1 = (a, 0)
    a `quotRem` 0 = error $ "quotRem " ++ show a ++ " 0 :: Word1"


--------------------------

data Defined a
    = Defined a
    | Undefined

instance Functor Defined where
    fmap f (Defined a) = Defined $ f a
    fmap _ _ = Undefined

instance Applicative Defined where
    pure = Defined
    Defined f <*> Defined x = Defined $ f x
    _         <*> _         = Undefined

instance Monad Defined where
    return = Defined
    Defined x >>= f = f x
    _ >>= _ = Undefined

instance Show a => Show (Defined a) where
    show (Defined a) = show a
    show _ = "?"

instance Eq a => Eq (Defined a) where
    Defined a == Defined b = a == b
--    _ == _ = error "(==) on undefined value"
    _ == _ = False -- !!! error "(==) on undefined value"

instance Ord a => Ord (Defined a) where
    Defined a `compare` Defined b = a `compare` b
    Undefined `compare` Undefined = EQ -- !!!
    Undefined `compare` _ = LT -- !!!
    _ `compare` _ = GT   -- !!!

instance Enum a => Enum (Defined a) where
    fromEnum = error "fromEnum :: Defined"
    toEnum   = error "fromEnum :: Defined"

defined :: b -> (a -> b) -> Defined a -> b
defined _ f (Defined a) = f a
defined b _ _ = b

fromDefined' :: String -> Defined a -> a
fromDefined' _ (Defined a) = a
fromDefined' e _ = error e


fromDefined :: Defined a -> a
fromDefined (Defined a) = a

isDefined :: Defined a -> Bool
isDefined = defined False (const True)

--------------------------

instance Bits a => Bits (Defined a) where
    (.&.) = liftA2 (.&.)
    (.|.) = liftA2 (.|.)
    xor   = liftA2 xor
    rotate w i = fmap (`rotate` i) w
    shift  w i = fmap (`shift`  i) w
    complement = fmap complement
    popCount = popCount . fromDefined
    testBit a i = testBit (fromDefined a) i
    bit = Defined . bit
    bitSizeMaybe = bitSizeMaybe . fromDefined
    bitSize = fromJust . bitSizeMaybe
    isSigned = isSigned . fromDefined

instance FiniteBits a => FiniteBits (Defined a) where
    finiteBitSize = finiteBitSize . fromDefined

instance Num a => Num (Defined a) where
    fromInteger = Defined . fromInteger
    (+) = liftA2 (+)
    (-) = liftA2 (-)
    (*) = liftA2 (*)
    abs    = fmap abs
    signum = fmap signum

instance Real a => Real (Defined a) where
    toRational = toRational . fromDefined

instance Integral a => Integral (Defined a) where
    toInteger = toInteger . fromDefined
    quotRem a b = defined (Undefined, Undefined) (Defined *** Defined) $ liftA2 quotRem a b
    divMod  a b = defined (Undefined, Undefined) (Defined *** Defined) $ liftA2 divMod  a b

