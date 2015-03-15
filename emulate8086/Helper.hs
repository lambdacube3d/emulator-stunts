module Helper where

import Numeric
import Data.Word
import Data.Int
import Data.Bits hiding (bit)
import Data.Char
import qualified Data.Sequence as S
import Control.Arrow
import Control.Lens as Lens

----------------------------------------------

everyNth n [] = []
everyNth n xs = take n xs: everyNth n (drop n xs)

showHex' :: (Show a, Integral a) => Int -> a -> String
showHex' i x = replicate (i - length s) '0' ++ s where s = showHex x ""

showHex''' :: (Show a, Integral a) => Int -> a -> String
showHex''' i x = map toUpper $ showHex' i x

pad :: a -> Int -> [a] -> [a]
pad x i xs = xs ++ replicate (i - length xs) x

bitAlign :: (Bits a, Num a) => Int -> a -> a
bitAlign n i = (i + complement mask) .&. mask
  where
    mask = (-1) `shiftL` n

quotRemSafe :: Integral a => a -> a -> Maybe (a, a)
quotRemSafe a 0 = Nothing
quotRemSafe a b = Just $ quotRem a b

----------------------------------------------

convertingInt :: (Integral a, Integral b) => Iso' a b
convertingInt = iso fromIntegral fromIntegral

shifting :: Bits a => Int -> Iso' a a
shifting i = iso (`shift` i) (`shift` (-i))

bit :: Bits a => Int -> Lens' a Bool
bit i = lens (`testBit` i) $ \x b -> (if b then setBit else clearBit) x i

bits :: (Bits a, Num a) => Int -> Int -> Lens' a a
bits off l = lens (.&. bitMask) (\w x -> w .&. complement bitMask .|. x) . from (shifting off)
  where
    bitMask = (complement $ (-1) `shiftL` l) `shiftL` off

highBit :: forall a . FiniteBits a => Lens' a Bool
highBit = bit $ finiteBitSize (undefined :: a) - 1

seqList :: Iso' (S.Seq a) [a]
seqList = iso toList S.fromList where
    toList s = case S.viewl s of
        S.EmptyL -> []
        x S.:< xs -> x: toList xs

--------------------------- TODO: eliminate this

uComb :: Lens' a b -> Lens' a c -> Lens' a (b, c)
uComb x y = lens ((^. x) &&& (^. y)) $ \a (b, c) -> set x b . set y c $ a

--------------------------

class (FiniteBits a, Integral a) => WordX a where

instance WordX Word8  where
instance WordX Word16 where
instance WordX Word32 where
instance WordX Word64 where
instance WordX Word   where

---------------------------------

class (WordX a, Integral (Signed a), FiniteBits (Signed a)) => AsSigned a where
    type Signed a :: *

instance AsSigned Word8  where    type Signed Word8  = Int8
instance AsSigned Word16 where    type Signed Word16 = Int16
instance AsSigned Word32 where    type Signed Word32 = Int32
instance AsSigned Word64 where    type Signed Word64 = Int64

asSigned :: AsSigned a => a -> Signed a
asSigned = fromIntegral

class (Integral a, Integral (X2 a), FiniteBits a, FiniteBits (X2 a)) => Extend a where
    type X2 a :: *

instance Extend Word8  where    type X2 Word8  = Word16
instance Extend Word16 where    type X2 Word16 = Word32
instance Extend Word32 where    type X2 Word32 = Word64

instance Extend Int8   where    type X2 Int8   = Int16
instance Extend Int16  where    type X2 Int16  = Int32
instance Extend Int32  where    type X2 Int32  = Int64

extend :: Extend a => a -> X2 a
extend = fromIntegral

combine :: forall a . Extend a => Iso' (a, a) (X2 a)
combine = iso (\(hi,lo) -> fromIntegral hi `shiftL` s .|. fromIntegral lo) (\d -> (fromIntegral $ d `shiftR` s, fromIntegral d))
  where
    s = finiteBitSize (undefined :: a)

high, low :: forall a . Extend a => Lens' (X2 a) a
low = lens fromIntegral (\st lo -> (st `shiftR` s) `shiftL` s .|. fromIntegral lo)
  where
    s = finiteBitSize (undefined :: a)

high = lens (fromIntegral . (`shiftR` s)) (\st hi -> fromIntegral hi `shiftL` s .|. fromIntegral (fromIntegral st :: a))
  where
    s = finiteBitSize (undefined :: a)

-------------------

checkAlign n i
    | i ^. bits 0 n == 0 = i
    | otherwise = error $ "checkAlign: " ++ show n ++ " " ++ show i

paragraph :: Iso' Word16 Int
paragraph = convertingInt . shifting 4 . iso id (checkAlign 4)

segAddr :: Word16 -> Word16 -> Int
segAddr s w = fromIntegral s `shiftL` 4 + fromIntegral w

