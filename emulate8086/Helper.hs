{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Helper where

import Numeric
import Numeric.Lens
import Data.Word
import Data.Int
import Data.Bits hiding (bit)
import qualified Data.Bits as Bits
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Functor.Compose
import qualified Data.FingerTree as F
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Sequence as S
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as V
import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Lens as Lens
import Control.Lens.Internal.Iso as Lens (Exchange (..))
import Control.Lens.Internal.Indexed as Lens (Indexing (..))
import Control.Lens.Action.Internal as Lens

import Word1

----------------------------------------------

everyNth n [] = []
everyNth n xs = take n xs: everyNth n (drop n xs)

showHex' :: (Show a, Integral a) => Int -> a -> String
showHex' i x = replicate (i - length s) '0' ++ s where s = showHex x ""

showHex'' :: (Show a, Integral a) => Int -> Defined a -> String
showHex'' i x = defined (replicate i '?') (showHex''' i) x

showHex''' :: (Show a, Integral a) => Int -> a -> String
showHex''' i x = map toUpper $ showHex' i x

pad :: a -> Int -> [a] -> [a]
pad x i xs = xs ++ replicate (i - length xs) x
{-
align :: Integral a => a -> a -> a
align n i = ((i + n - 1) `div` n) * n
-}
-- bitAlign n i  ==  align (2^n) i
bitAlign :: (Bits a, Num a) => Int -> a -> a
bitAlign n i = (i + complement mask) .&. mask
  where
    mask = (-1) `shiftL` n
{-
assert :: Monad m => String -> Bool -> m ()
assert _ True = return ()
assert m _ = error m
-}
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

fingerTreeList :: F.Measured m a => Iso' (F.FingerTree m a) [a]
fingerTreeList = iso toList F.fromList where
    toList x = case F.viewl x of
        F.EmptyL -> []
        a F.:< as -> a: toList as

--------------------------- TODO: eliminate this

uComb :: Lens' a b -> Lens' a c -> Lens' a (b, c)
uComb x y = lens ((^. x) &&& (^. y)) $ \a (b, c) -> set x b . set y c $ a

--------------------------

-- BitChunk i w :  0 <= w < 2^i
data BitChunk a = BitChunk
    { _bcSize :: Int 
    , _bcValue :: a
    }

$(makeLenses ''BitChunk)

instance Eq a => Eq (BitChunk a) where
    BitChunk i j == BitChunk i' j' = (i, j) == (i', j')

instance F.Measured BitSize (BitChunk a) where
    measure (BitChunk i _) = Sum i

instance F.Measured m a => F.Measured m [a] where
    measure = mconcat . map F.measure

bitChunk :: (Num a, Bits a) => Int -> Int -> a -> BitChunk a
bitChunk off i a = BitChunk i $ a ^. bits off i

type BitChunks a = [BitChunk a]

dropChunks :: (Num a, Bits a) => Int -> BitChunks a -> BitChunks a
dropChunks _ [] = []
dropChunks 0 xs = xs
dropChunks n (BitChunk i b: xs)
    | i <= n = dropChunks (n-i) xs
    | otherwise = bitChunk n (i-n) b: xs

takeChunks :: (Num a, Bits a) => Int -> BitChunks a -> BitChunks a
takeChunks _ [] = []
takeChunks 0 xs = []
takeChunks n (c@(BitChunk i b): xs)
    | i <= n = c: takeChunks (n-i) xs
    | otherwise = bitChunk 0 n b: []

class (FiniteBits a, Integral a) => WordX a where
    -- hack
    asInt :: Iso' a (Maybe Integer)
    asInt = iso (Just . toInteger) $ maybe (error "fromInteger'") fromInteger

instance WordX Word1  where
instance WordX Word8  where
instance WordX Word16 where
instance WordX Word32 where
instance WordX Word64 where
instance WordX Word   where
instance WordX a => WordX (Defined a)  where
    asInt = iso (defined Nothing $ Just . toInteger) (maybe Undefined $ Defined . fromInteger)

convWords :: (WordX a, WordX b) => a -> b
convWords = (^. (asInt . from asInt))

convChunks_ :: (Bits a, Num a, Bits b, Num b) => Int -> (a -> b) -> BitChunks a -> BitChunks b
convChunks_ sb conv = unfoldr g where
    g [] = Nothing
    g xs = Just (BitChunk (measure ys) (foldr h 0 ys), dropChunks sb xs)
      where
        ys = takeChunks sb xs
        h (BitChunk i a) acc = (acc `shiftL` i) .|. conv a

convChunks :: forall a b . (WordX a, WordX b) => Iso' (BitChunks a) (BitChunks b)
convChunks = iso f f where
    f :: forall a b . (WordX a, WordX b) => BitChunks a -> BitChunks b
    f = convChunks_ (finiteBitSize (undefined :: b)) convWords

instance WordX a => Show (BitChunk a) where
    show = concatMap ((show :: Defined Word1 -> String) . (^. bcValue)) . reverse . (^. convChunks) . (:[])

bitChunks :: forall a b . (WordX a, WordX b) => Prism' (BitChunks a) b
bitChunks = convChunks . prism' ((:[]) . BitChunk sb) f
  where
    sb = finiteBitSize (undefined :: b)

    f []  = Just 0
    f [x] = Just $ x ^. bcValue
    f _ = Nothing

--------------------------------- TODO: refactor?

class (WordX a, Integral (Signed a), FiniteBits (Signed a)) => AsSigned a where
    type Signed a :: *

instance AsSigned Word8  where    type Signed Word8  = Int8
instance AsSigned Word16 where    type Signed Word16 = Int16
instance AsSigned Word32 where    type Signed Word32 = Int32
instance AsSigned Word64 where    type Signed Word64 = Int64

instance AsSigned a => AsSigned (Defined a) where    type Signed (Defined a) = Defined (Signed a)

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

instance Extend a => Extend (Defined a)  where type X2 (Defined a) = Defined (X2 a)

extend :: Extend a => a -> X2 a
extend = fromIntegral

combine :: forall a . Extend a => Iso' (a, a) (X2 a)
combine = iso (\(hi,lo) -> fromIntegral hi `shiftL` s .|. fromIntegral lo) (\d -> (fromIntegral $ d `shiftR` s, fromIntegral d))
  where
    s = finiteBitSize (undefined :: a)

high, low :: Extend a => Lens' (X2 a) a
high = from combine . _1
low  = from combine . _2

-------------------

checkAlign n i
    | i ^. bits 0 n == 0 = i
    | otherwise = error $ "checkAlign: " ++ show n ++ " " ++ show i


byte :: Iso' Int Int
byte = shifting 3 . iso id (checkAlign 3)

paragraph :: Iso' Word16 Int
paragraph = convertingInt . shifting 4 . iso id (checkAlign 4)

segAddr :: Word16 -> Word16 -> Int
segAddr s w = (s ^. paragraph + w ^. convertingInt) ^. byte

showAddr :: Int -> String
showAddr x = showHex' 5 (x ^. shifting (-3)) ++ concat ["," ++ showHex' 1 y | let y = x ^. bits 0 3, y /= 0]

------------------------------

data Hashed a = Hashed Int a
    deriving Show

class Hash a where
    hash :: a -> Int

hashed :: Hash a => Iso' a (Hashed a)
hashed = iso (\x -> Hashed (hash x) x) (\(Hashed _ a) -> a)

--------------------------

-- TODO: dedicated type for bitsize?
type BitSize = Sum Int

measure :: F.Measured (Sum b) a => a -> b
measure = getSum . F.measure

mapWithPositions_ :: Monoid c => (a -> c) -> (c -> c -> a -> b) -> [a] -> [b]
mapWithPositions_ measure f xs = zipWith3 f (scanl mappend mempty is) is xs
  where
    is = map measure xs

mapWithPositions :: (F.Measured (Sum c) a, Num c) => (c -> c -> a -> b) -> [a] -> [b]
mapWithPositions f = mapWithPositions_ F.measure $ \i j -> f (getSum i) (getSum j)
{-
zipWithPositions :: F.Measured BitSize a => (Int -> Int -> a -> b -> c) -> [a] -> [b] -> [c]
zipWithPositions f xs ys = mapWithPositions_ (measure . fst) (\off l (x, y) -> f off l x y) $ zip xs ys
-}

fSplit :: (F.Measured (Sum c) a, Real c) => c -> F.FingerTree (Sum c) a -> (F.FingerTree (Sum c) a, c, F.FingerTree (Sum c) a)
fSplit x f = (a, x - measure a, b) where (a, b) = F.split (> Sum x) f

-------------------

--wordSize :: Int
--wordSize = finiteBitSize (undefined :: Word)

--------------------------

data Halt
    = CleanHalt
    | Err String
  deriving Show

-- instance Except String Halt where



combDef :: Iso' (Defined a, Defined b) (Defined (a, b))
combDef = iso f g where
    f (Defined a, Defined b) = Defined (a, b)
    f _ = Undefined
    g (Defined (a, b)) = (Defined a, Defined b)
    g _ = (Undefined, Undefined)


-- TODO: revise & generalize
prismToIso :: b -> Prism' a b -> Iso' a b
prismToIso x p = iso (fromMaybe x . (^? p)) (^. re p)


