{-# OPTIONS_GHC -fno-warn-orphans #-}
module Helper where

import Numeric
import Data.Word
--import Data.Int
import Data.Bits hiding (bit)
--import Data.Char
--import Control.Lens as Lens

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

--showHex''' :: (Show a, Integral a) => Int -> a -> String
--showHex''' i x = map toUpper $ showHex' i x

pad :: a -> Int -> [a] -> [a]
pad x i xs = xs ++ replicate (i - length xs) x

-------------------

{-# INLINE debug #-}
debug = False

segAddr :: Word16 -> Word16 -> Int
segAddr s w = fromIntegral s `shiftL` 4 + fromIntegral w

