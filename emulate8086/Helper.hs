module Helper where

import Numeric
import Data.Word
import Data.Int
import Data.Bits hiding (bit)
import Data.Char
import Control.Lens as Lens

--------------------------------------------------------------------------------

instance Num Bool where
    (+) = xor
    (-) = xor
    (*) = (&&)
    abs = id
    signum = id
    fromInteger = odd

instance Real Bool where
    toRational = toRational . fromEnum

instance Integral Bool where
    toInteger = toInteger . fromEnum
    a `quotRem` 1 = (a, 0)
    a `quotRem` 0 = error $ "quotRem " ++ show a ++ " 0 :: Bool"

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

---------------------------------

class (Integral a, FiniteBits a, Integral (Signed a), FiniteBits (Signed a)) => AsSigned a where
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

debug = False

paragraph :: Iso' Word16 Int
paragraph = if debug then iso ((`shiftL` 4) . fromIntegral) (fromIntegral . (`shiftR` 4) . check16)
            else iso ((`shiftL` 4) . fromIntegral) (fromIntegral . (`shiftR` 4))
  where
    check16 x = if x .&. complement 0xf == 0 then x else error "paragraph"

segAddr :: Word16 -> Word16 -> Int
segAddr s w = fromIntegral s `shiftL` 4 + fromIntegral w

