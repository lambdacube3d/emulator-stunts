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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PackageImports #-}
module Emulate where

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
import qualified Data.FingerTree as F
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Sequence as S
import qualified Data.Set as Set
import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as V
import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Except
import Control.Lens as Lens
import Control.Concurrent.MVar
import Control.Exception (evaluate)
import System.Directory
import System.FilePath (takeFileName)
import "Glob" System.FilePath.Glob

import Debug.Trace
import System.IO.Unsafe

import Hdis86 hiding (wordSize)
import Hdis86.Incremental

import Helper
import Word1
import Edsl hiding (Flags, trace_, ips, sps, segAddr_, addressOf, addressOf', byteOperand, wordOperand)
import qualified Edsl

----------------------------------------------

data MemPiece
    = MemPacked (F.FingerTree BitSize MemPiece)
    | MemSlice !Int{-offset-} !Int{-length-} (Hashed MemPiece)
    | MemGroup GroupInfo MemPiece

    | MemBits !Int{-bitlength-} !Word
    | MemReserved ReservedInfo  -- don't read, write or allocate
    | MemUndefined !Int
    | MemTimes Int MemPiece     -- for efficiency
    | MemRam (S.Seq Word8)      -- for efficiency
    | MemRom BS.ByteString      -- for efficiency
    deriving Show

type Info = BS.ByteString

data ReservedInfo
    = RI
    deriving Show

data GroupInfo
    = GIAllocated
    | GIFlags
    deriving Show

memAllocated x = MemGroup GIAllocated $ mconcat
    [ MemReserved RI
    , x
    ]

instance F.Measured BitSize ReservedInfo where
    measure = \case
        RI -> Sum $ 16 ^. byte

instance F.Measured BitSize MemPiece where
    measure = \case
        MemPacked x     -> F.measure x
        MemSlice _ l _  -> Sum l
        MemTimes i x    -> Sum $ i * measure x
        MemGroup _ x    -> F.measure x
        MemBits i _     -> Sum i
        MemRom bs       -> Sum $ BS.length bs ^. byte
        MemRam s        -> Sum $ S.length s ^. byte
        MemReserved i   -> F.measure i
        MemUndefined i  -> Sum i

instance Hash MemPiece where
    hash = error "hash mempiece"

--------------

undef = Defined 0 --Undefined
undefBool = Defined False

-- TODO: revise this
joinMP :: MemPiece -> MemPiece -> F.FingerTree BitSize MemPiece
MemRam s `joinMP` MemRam s'     = F.singleton $ MemRam $ s S.>< s'
MemRam s `joinMP` MemBits 8 s'  = F.singleton $ MemRam $ s S.|> fromIntegral s'
MemRam s `joinMP` MemBits 16 s' = F.singleton $ MemRam $ s S.|> fromIntegral s' S.|> fromIntegral (s' `shiftR` 8)
MemBits 8 s  `joinMP` MemRam s' = F.singleton $ MemRam $ fromIntegral s S.<| s'
MemBits 16 s `joinMP` MemRam s' = F.singleton $ MemRam $ fromIntegral s S.<| fromIntegral (s `shiftR` 8) S.<| s'
x            `joinMP` y         = F.fromList [x, y]

instance Monoid MemPiece where
    mempty = MemPacked F.empty

    MemPacked p_ `mappend` f = case F.viewr p_ of
        F.EmptyR -> f
        p F.:> p0 -> memPacked $ case f of
            MemPacked f -> case F.viewl f of
                F.EmptyL -> p_
                f0 F.:< f -> p F.>< p0 `joinMP` f0 F.>< f
            _ -> p F.>< p0 `joinMP` f
    p `mappend` MemPacked f = case F.viewl f of
        F.EmptyL -> p
        f0 F.:< f -> memPacked $ p `joinMP` f0 F.>< f
    p `mappend` f = memPacked $ p `joinMP` f


memBits :: Int -> Int -> Word -> MemPiece
memBits _ 0 _   = mempty
memBits off l w = MemBits l $ w ^. bits off l

--memRom _ 0 _ = mempty
memRom off l bs
    | d == d' = memBits m (m'-m) $ fromIntegral $ BS.index bs d
    | otherwise = memBits m (8-m) (fromIntegral $ BS.index bs d)
            `mappend` memRom' (BS.take (d' - d - 1) $ BS.drop (d + 1) bs)
            `mappend` memBits 0 m' (fromIntegral $ BS.index bs d')
  where
    (d, m_) = divMod (off - 1) 8
    m = m_ + 1
    (d', m') = divMod (off+l) 8
    memRom' bs | BS.null bs = mempty
    memRom' bs = MemRom bs

--memRam _ 0 _ = mempty
memRam off l bs
    | d == d' = memBits m (m'-m) $ fromIntegral $ S.index bs d
    | otherwise = memBits m (8-m) (fromIntegral $ S.index bs d)
            `mappend` memRam' (S.take (d' - d - 1) $ S.drop (d + 1) bs)
            `mappend` memBits 0 m' (fromIntegral $ S.index bs d')
  where
    (d, m_) = divMod (off - 1) 8
    m = m_ + 1
    (d', m') = divMod (off+l) 8
    memRam' bs | S.null bs = mempty
    memRam' bs = MemRam bs

memTimes :: Int -> MemPiece -> MemPiece
--memTimes i x = mconcat $ replicate i x
memTimes 0 x = mempty
memTimes i x | i > 0 = MemTimes i x

memUndefined 0 = mempty
memUndefined i | i > 0 = MemUndefined i

memUndefined' = memUndefined --i = toRam $ replicate i $ error "memUndef"

--memUndefined'' i = memTimes i $ memBits 0 8 0

toRam :: [Word8] -> MemPiece
toRam = MemRam . S.fromList --mconcat . map (memBits 0 8 . fromIntegral)

toRom :: BS.ByteString -> MemPiece
toRom = MemRom --toRam . BS.unpack --MemRom

memPacked :: F.FingerTree BitSize MemPiece -> MemPiece
memPacked a = case F.viewl a of
    x F.:< xs | F.null xs -> x
    _ -> MemPacked a

--------------

--flattenMemPiece :: MemPiece -> [MemPiece]
flattenMemPiece unGroup unMemSlice unMemTimes = \case
    MemPacked x      -> concatMap (flattenMemPiece unGroup unMemSlice unMemTimes) $ x ^. fingerTreeList
    MemGroup g x     -> unGroup (flattenMemPiece unGroup unMemSlice unMemTimes) g x
    MemSlice off l x -> unMemSlice (flattenMemPiece unGroup unMemSlice unMemTimes) off l x
    MemTimes i x     -> unMemTimes (flattenMemPiece unGroup unMemSlice unMemTimes) i x
    x -> [x]

unGroup f _ x = f x
keepGroup _ gr f = [MemGroup gr f]
keepMemSlice _ off l x = [MemSlice off l x]
keepMemTimes _ i x = [MemTimes i x]
unMemTimes f i x = concat $ replicate i $ f x

showMemPiece :: MemPiece -> String
showMemPiece = -- showAddr . measure 
            f -- . flattenMemPiece unGroup keepMemSlice keepMemTimes
  where
    f (MemTimes i x) = show i ++ "x{" ++ showMemPiece x ++ "}"
    f (MemBits i x) = "" -- show i ++ "x{" ++ showMemPiece x ++ "}"
    f (MemRam s) = "Ram_" ++ showHex' 5 (S.length s)
    f (MemRom s) = "Rom_" ++ showHex' 5 (BS.length s)
    f (MemReserved i) = "res_" ++ showAddr (measure i)
    f (MemUndefined i) = "undef_" ++ showAddr i
    f (MemGroup _ x) = "{" ++ showMemPiece x ++ "}"
    f (MemPacked x) = "<" ++ intercalate "|" (map f $ x ^. fingerTreeList) ++ ">"
{-
showMemPiece = intercalate "|" . f . flattenFRam'
  where
    f ps = zipWith g (scanl (+) 0 $ map measure ps) ps
    g addr p = case p of
        MemRam s -> "Rom " ++ showAddr addr ++ "-" ++ showAddr (addr + measure p)
        MemTimes s MemFree -> "Free " ++ showAddr addr ++ "-" ++ showAddr (addr + measure p)
        MemTimes s MemUninitialized -> "Uninit " ++ showAddr addr ++ "-" ++ showAddr (addr + measure p)
        MemFilled s b -> "Filled " ++ showHex' 2 b ++ " " ++ showAddr addr ++ "-" ++ showAddr (addr + measure p)
        MemAllocated f -> "Allocated{" ++ showMemPiece f ++ "}"
        _ -> ""
-}

memBitChunks :: Iso' MemPiece (BitChunks (Defined Word))
memBitChunks = iso (concatMap f . flattenMemPiece unGroup keepMemSlice unMemTimes) g
  where
    g x = mconcat $ map gf x
    gf (BitChunk 8 (Defined s)) = MemRam $ S.singleton $ fromIntegral s
    gf (BitChunk 16 (Defined s)) = MemRam $ S.fromList [fromIntegral s, fromIntegral (s `shiftR` 8)]
    gf (BitChunk 32 (Defined s)) = MemRam $ S.fromList [fromIntegral s, fromIntegral (s `shiftR` 8), fromIntegral (s `shiftR` 16), fromIntegral (s `shiftR` 24)]
    gf (BitChunk n (Defined w)) = memBits 0 n w
    gf (BitChunk n Undefined) = MemUndefined n

    f = \case
        MemSlice off l x -> takeChunks l $ dropChunks off $ f (x ^. from hashed)
        MemBits i x -> [BitChunk i $ Defined x]
        MemRom bs -> [bitChunk 0 8 $ fromIntegral x | x <- BS.unpack bs]
        MemRam bs -> [bitChunk 0 8 $ fromIntegral x | x <- bs ^. seqList]
        MemReserved i -> undefineds $ measure i
        MemUndefined i -> undefineds i

    s = finiteBitSize (undefined :: Word)
    undefineds i = zipWith BitChunk (replicate d s ++ [m | m /= 0]) $ repeat undef
      where
        (d, m) = divMod i s

showBits :: String -> MemPiece -> String
showBits mask = zipWith f mask . reverse . (^. memBitChunks . convChunks) where
    f _ (BitChunk 1 Undefined) = '?'
    f c (BitChunk 1 (Defined (Word1 x))) = case c of
        '_' -> head . show . fromEnum $ x
        _ -> (if x then toUpper else toLower) c

--------------

-- we statically know that the size of the MemPiece is 'a' (a ~ WordX)
newtype MemPieceS a
    = MemPieceS { _memPieceS :: MemPiece }
    deriving Show

$(makeLenses ''MemPieceS)

type MemPiece1  = MemPieceS Word1
type MemPiece8  = MemPieceS Word8
type MemPiece16 = MemPieceS Word16
type MemPiece32 = MemPieceS Word32

def :: MonadError Halt m => Defined a -> m a
def = defined (throwError $ Err $ "not defined") return

coerceS_ :: forall a . WordX a => Prism' (MemPieceS a) (Defined a)
coerceS_ = memPieceS . memBitChunks . bitChunks

coerceS' :: WordX a => String -> Iso' (MemPieceS a) a
coerceS' e = coerceS_' . iso (fromDefined' e) Defined

coerceS'' x = defined (throwError $ Err "coerceS''") return $ x ^. coerceS_' 

-- is this OK?
coerceS_' :: forall a . WordX a => Iso' (MemPieceS a) (Defined a)
coerceS_' = prismToIso undef coerceS_


instance (WordX a) => Eq (MemPieceS a) where
    a == b = fromJust $ liftA2 (==) (a ^? coerceS_) (b ^? coerceS_)

fmap' :: (WordX a, WordX b) => (a -> b) -> MemPieceS a -> MemPieceS b
fmap' f =  (^. re coerceS_) . fmap f . fromJust . (^? coerceS_)

fromRom :: MemPiece -> [Defined Word8]
fromRom = map f . (^. memBitChunks . convChunks)
  where
    f (BitChunk 8 x) = x

{-
instance Functor MemPieceS where
    fmap = error "functor coerceS"
-}
annMap :: (WordX a, WordX b) => BS.ByteString -> (a -> b) -> MemPieceS a -> MemPieceS b
annMap _ = fmap'

noAnn :: (WordX a) => a -> MemPieceS a
noAnn = (^. re coerceS_) . Defined -- MemPieceS NoAnnot

(@:) :: (WordX a) => BS.ByteString -> a -> MemPieceS a
b @: x = Defined x ^. re coerceS_ --MemPieceS (Annot b) x
infix 5 @:

showA :: (WordX a) => (a -> String) -> MemPieceS a -> String
showA f s = maybe "?A" (defined (showBits (repeat '_') $ s ^. memPieceS) f) $ s ^? coerceS_

allocateMem :: Int -> MemPiece -> (Int, MemPiece)
allocateMem req' f = (r + 16 ^. byte, f & memSlice r (req' + 16 ^. byte) .~ memAllocated (memUndefined' req'))
  where
    l = flattenMemPiece keepGroup keepMemSlice keepMemTimes f
    r = head $ concat $ mapWithPositions g l
    g addr _ (MemUndefined s) | s' >= (req' + 16 ^. byte) = [addr']
      where
        addr' = bitAlign 4 addr
        s' = s - (addr' - addr)
    g _ _ _ = []

--allocateMem' :: MonadState MemPiece m => Word16 -> m Word16
allocateMem' x = state $ allocateMem x

viewl :: MemPiece -> Maybe (MemPiece, MemPiece)
viewl (MemPacked b) = case F.viewl b of
    F.EmptyL -> Nothing
    x F.:< y -> Just (x, memPacked y)
viewl b = Just (b, mempty)

modifyAllocated :: Int -> Int -> MemPiece -> Either Int MemPiece
modifyAllocated addr req f = memSlice (addr - 16 ^. byte) (req + 16 ^. byte) tr f where
    tr (viewl -> Just (MemGroup gr blk, follow))
        | all >= req
            = Right $ (MemGroup gr $ blk `mappend` memUndefined' (req - blk'))
                `mappend` memUndefined (all - req)
                `mappend` c
        | otherwise = Left all
      where
        blk' = measure blk - 16 ^. byte
        all = blk' + len'
        (len', c) = case viewl follow of
            Just (MemUndefined len', c) -> (len', c)
            _ -> (0, follow)

    tr _ = error "modifyAllocated"
--        x F.:< c -> error $ "modifyAllocated 2: " ++ showMemPiece x
--        F.EmptyL -> error "end of mem 2"

low', high' :: Lens' MemPiece16 MemPiece8
low' = memPieceS . memSlice 0 8 . from memPieceS
high' = memPieceS . memSlice 8 8 . from memPieceS

memSlice :: Int -> Int -> Lens' MemPiece MemPiece
memSlice 0 l tr mp | l == measure mp = tr mp
memSlice off l tr mp
    | off + l > measure mp || l < 0 || off < 0 = error $ unwords ["memSlice ", showAddr off, showAddr l, showMemPiece mp]
--writeMemPiece off p (MemPacked f) = memComposed $ flip execState f $ runErrorT $ do
--    when (off + l > getSum (F.measure f)) $ throwError $ Err "end of mem"
memSlice _ 0 tr mp = tr mempty <&> const mp  -- ??
memSlice off l tr mp = case mp of
    --             |  a  | b0|bs| c0| cs |
    --             |  off  |   l  |
    --                   |x|v|  |y|z|
    MemPacked (fSplit off -> (a, x, fSplit (x + l) -> (b, y, c))) ->

        case F.viewl b of
            F.EmptyL -> case F.viewl c of
                          -- | a | c0 | c |   -- p is in c0
                c0 F.:< c -> memSlice x l tr c0 <&> \c0 -> memPacked a `mappend` c0 `mappend` memPacked c
                _ -> error "impossible"
            b0 F.:< b
                         --  | a | b0 | c |   -- p is in b0
                | F.null b && y == 0 -> memSlice x l tr b0 <&> \b0 -> memPacked a `mappend` b0 `mappend` memPacked c
                | otherwise -> case F.viewl c of
                         --  | a | b0+b |   -- p is in b0+b
                    F.EmptyL -> tr ((b0 ^. memSlice x v) `mappend` memPacked b)
                        <&> \b -> memPacked a `mappend` (b0 ^. memSlice 0 x) `mappend` b
                         --  | a | b0+bs+c0 | cs |   -- p is in b+c0
                    c0 F.:< c -> tr ((b0 ^. memSlice x v) `mappend` memPacked b `mappend` (c0 ^. memSlice 0 y))
                        <&> \new -> memPacked a `mappend` (b0 ^. memSlice 0 x) `mappend` new `mappend` (c0 ^. memSlice y z) `mappend` memPacked c
                      where
                        z = measure c0 - y
              where
                v = measure b0 - x

    MemUndefined i -> tr (memUndefined l) <&> \x -> memUndefined off `mappend` x `mappend` memUndefined (i - (off + l))
    MemBits i w -> tr (memBits off l w) <&> \x -> memBits 0 off w `mappend` x `mappend` memBits (off + l) (i - (off + l)) w
    MemRom w -> tr (memRom off l w)
            <&> \x -> memRom 0 off w `mappend` x `mappend` memRom (off + l) (measure mp - (off + l)) w
    MemRam w -> tr (memRam off l w) <&> f
      where
        f x = memRam 0 off w `mappend` x `mappend` memRam (off + l) (measure mp - (off + l)) w
    MemGroup gi g -> memSlice off l (tr {- . MemGroup {-TODO: denote subgroup-}gi-}) g <&> MemGroup gi
    MemReserved i -> error "memRes"
    MemTimes i f
        | d == d' -> memSlice m (m' - m) tr f <&> \new -> memTimes d f `mappend` new `mappend` memTimes (i - d' - 1) f
        | otherwise -> tr ((f ^. memSlice m (s - m)) `mappend` memTimes (d' - d - 1) f `mappend` (f ^. memSlice 0 m'))
            <&> \new -> memTimes d f `mappend` (f ^. memSlice 0 m) `mappend` 
                   new `mappend` (f ^. memSlice m' (s - m')) `mappend` memTimes (i - d' - 1) f
      where
        s = measure f
        (d, m) = divMod off s
        (d', m'_) = divMod (off+l-1) s
        m' = m'_ + 1

------------------------------

type Flags = MemPiece16

showFlags :: Flags -> String
showFlags = showBits "____oditsz_a_p_c" . (^. memPieceS)

wordToFlags :: Word16 -> Flags
wordToFlags w = MemPieceS $ mconcat
    [ memBits 0 8 w'
    , MemUndefined 1
    , memBits 9 3 w'
    , MemUndefined 4
    ]
 where
    w' = fromIntegral $ (w .&. 0xed3) .|. 0x2

-----------------------

bytesAt :: Int -> Int -> Lens' MemPiece [Defined Word8]
bytesAt i j = memSlice (checkAlign 3 i) (j ^. byte)
    . iso (f . (^. memBitChunks . convChunks)) (toRam . map (defined (error "bytesAt") id) . pad (error "pad") j . take j)
  where
    f = map $ \(BitChunk 8 x) -> x
    g = map $ BitChunk 8

byteAt :: Int -> Lens' MemPiece (Defined Word8)
byteAt i = byteAt' i . coerceS_'

byteAt' :: Int -> Lens' MemPiece MemPiece8
byteAt' i = memSlice (checkAlign 3 i) 8 . from memPieceS

wordAt :: Int -> Lens' MemPiece (Defined Word16)
wordAt i = wordAt' i . coerceS_'

wordAt' :: Int -> Lens' MemPiece MemPiece16
wordAt' i = memSlice (checkAlign 3 i) 16 . from memPieceS

dwordAt :: Int -> Lens' MemPiece (Defined Word32)
dwordAt i = dwordAt' i . coerceS_'

dwordAt' :: Int -> Lens' MemPiece MemPiece32
dwordAt' i = memSlice (checkAlign 3 i) 32 . from memPieceS


-- size in bits
type Size = Int

data Key
    = KReg Size Int
    | Flag Char
    | Flags
    | Heap Size Int
        deriving (Eq, Ord)

reg8names = ["al","ah","dl","dh","bl","bh","cl","ch"]
reg16names = ["ax","dx","bx","cx", "si","di", "cs","ss","ds","es", "ip","sp","bp"]

combineKey (Heap s i: ks) = run (i + s) ks
  where
    run i (Heap s' i': ks) | i==i' && s==s' = run (i + s) ks
    run i' ks = Heap (i'-i) i: combineKey ks
combineKey (k:ks) = k: combineKey ks
combineKey [] = []

instance Show Key where
    show (Heap _ i) = "[" ++ showAddr i ++ "]"
    show (Flag c) = [c]
    show Flags = "flags"
    show (KReg 8 i) = reg8names !! (i ^. from byte)
    show (KReg 16 i) = reg16names !! ((i ^. from byte) `div` 2)
    show (KReg 32 0) = "dx:ax"

data Config_ = Config_
    { _numOfDisasmLines :: Int
    , _disassStart      :: Int
    , _verboseLevel     :: Int
    , _termLength       :: Int  -- width of terminal
    , _videoMVar        :: MVar (Int -> Int -> Word8)
    , _instPerSec       :: Int

    , _stackTrace       :: [Int]
    , _stepsCounter     :: Int

    , _counter          :: Maybe Int -- counter to count down
    , _counter'         :: [Int]
    , _speaker          :: Word8     -- 0x61 port
    }

$(makeLenses ''Config_)

defConfig = Config_
    { _numOfDisasmLines = 3
    , _disassStart  = 0
    , _verboseLevel = 2
    , _termLength   = 149
    , _instPerSec   = 710000
    , _videoMVar    = undefined --return $ \_ _ -> 0

    , _stackTrace   = []
    , _stepsCounter = 0

    , _counter = Nothing
    , _counter' = []
    , _speaker = 0x30 -- ??
    }

data MachineState = MachineState
    { _flags_   :: Flags
    , _regs     :: MemPiece
    , _heap     :: MemPiece

    , _hist     :: Set.Set Key
    , _traceQ   :: [String]
    , _config   :: Config_
    , _cache    :: IM.IntMap (Machine ())
    , _labels   :: IM.IntMap BS.ByteString
    , _files    :: IM.IntMap (FilePath, BS.ByteString, Int)  -- filename, file, position
    , _dta      :: Int
    , _retrace  :: [Word16]
    , _intMask  :: Word8
    }

emptyState = MachineState
    { _flags_   = wordToFlags 0xf202
    , _regs     = toRam $ replicate (2*26) 0 --  mconcat $ replicate 26 $ memBits 0 16 0
    , _heap     = mconcat []

    , _hist     = Set.empty
    , _traceQ   = []
    , _config   = defConfig
    , _cache    = IM.empty
    , _labels   = IM.empty
    , _files    = IM.empty
    , _dta      = 0
    , _retrace  = cycle [1,9,0,8] --     [1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0]
    , _intMask  = 0xf8
    }

type Machine = ExceptT Halt (State MachineState)
type MachinePart a = Lens' MachineState a

$(makeLenses ''MachineState)

setCounter = do
    trace_ "setCounter"
    v <- use $ config . instPerSec
    config . counter .= Just (v `div` 24)

getRetrace = do
    x <- head <$> use retrace
    retrace %= tail
    return x


trace_ :: String -> Machine ()
trace_ s = traceQ %= (s:)

steps = config . numOfDisasmLines

clearHist = do
    hi <- use hist
    hist .= Set.empty
    h <- use traceQ
    traceQ .= []
    return (hi, intercalate "; " $ reverse h)

addHist :: Key -> MachinePart a -> MachinePart a
addHist sh k = lens (^. k) $ \s a -> hist %~ Set.insert sh $ set k a s

[overflowF',directionF',interruptF',signF',zeroF',adjustF',parityF',carryF'] =
    [ memPieceS . memSlice i 1 . from memPieceS . coerceS_' . mapping bit0  :: Lens' Flags (Defined Bool)
    | i <- [11,10,9,7,6,4,2,0]
    ]

[overflowF,directionF,interruptF,signF,zeroF,adjustF,parityF,carryF] =
    [ addHist (Flag $ reverse "____oditsz_a_p_c" !! i) $ flags . memPieceS . memSlice i 1 . from memPieceS . coerceS_' . mapping bit0  :: MachinePart (Defined Bool)
    | i <- [11,10,9,7,6,4,2,0]
    ]

reg16Lenses@[ax,dx,bx,cx, si,di, cs,ss,ds,es, ip,sp,bp]
    = [ addHist (KReg 16 i) $ regs . wordAt i | i <- map (^. byte) [0,2..24] ]
reg8Lenses@[al,ah,dl,dh,bl,bh,cl,ch]
    = [ addHist (KReg 8 i) $ regs . byteAt i | i <- map (^. byte) [0..7] ]
dxax = addHist (KReg 32 0) $ regs . dwordAt' 0

-- experimental
reg16Lenses'@[ax',dx',bx',cx', si',di', cs',ss',ds',es', ip',sp',bp']
    = [ addHist (KReg 16 i) $ regs . wordAt' i | i <- map (^. byte) [0,2..24] ]
[al',ah',dl',dh',bl',bh',cl',ch']
    = [ addHist (KReg 8 i) $ regs . byteAt' i | i <- map (^. byte) [0..7] ]

segAddr_ :: MachinePart (Defined Word16) -> Getter MachineState (Defined Word16) -> Getter MachineState (Defined Int)
segAddr_ seg off = to $ \s -> liftA2 segAddr (s ^. seg) (s ^. off)

ips = segAddr_ cs ip
sps = segAddr_ ss sp

xx :: MachinePart (MemPiece16)
xx = lens (const $ error "xx") $ \s _ -> s

fs, gs :: MachinePart (Defined Word16)
fs = lens (const $ Defined 0) $ \s _ -> s
gs = lens (const $ Defined 0) $ \s _ -> s


flags = flags_ . memPieceS . iso id ((memSlice 12 4 .~ memUndefined 4) . (memSlice 1 1 .~ memBits 0 1 1) . (memSlice 3 1 .~ memBits 0 1 0) . (memSlice 5 1 .~ memBits 0 1 0)) . from memPieceS

heap8  i = addHist (Heap 8 i) $ heap . byteAt' i
heap16 i = addHist (Heap 16 i) $ heap . wordAt' i

----------------------

instance Show MachineState where
    show s = intercalate "\n" $
        [ "  Flags: " ++ showFlags (s ^. flags)
        , ("  "++) $ unwords $ zipWith showReg ["AX","BX","CX","DX"] [ax,bx,cx,dx]
        , ("  "++) $ unwords $ zipWith showReg ["SI","DI","IP","SP","BP"] [si,di,ip,sp,bp]
        , ("  "++) $ unwords $ zipWith showReg ["DS","ES","CS","SS"] [ds,es,cs,ss]
{- TODO
        , (\(a,b)->a ++ "\n" ++ b) $ (("Stack: " ++) . unwords) *** (("       " ++) . unwords) $ unzip
            $ take 20
            $ zip (map (showHex' 4) [s ^. sp, s ^. sp + 2..0xffff] ++ repeat "####")
                    (take 20 . map ff . everyNth 2 $ map (maybe "##" (showHex' 2. (^. coerceS)) . (readByte_ heap_)) [s ^. sps ..])
-}
        , "Code: "
        ] ++ map (take $ s ^. config . termLength) (takeCont [] ["..."] (s ^. config . numOfDisasmLines) $ showCode (initQueue s) s)
      where
        ff [a,b] = b ++ a
        heap_ = s ^. heap
        showReg c k = c ++ ":" ++ showHex' 4 (s ^. k)

        -- TODO: elim this
        takeCont :: [a] -> [a] -> Int -> [a] -> [a]
        takeCont as bs n xs = take n xs ++ f (drop n xs) where
            f [] = as
            f _  = bs



infixr 5 .++, +.+

"" .++ b = b
a .++ b = a ++ " " ++ b

b +.+ "" = b
"" +.+ b = b
a +.+ b = a ++ "+" ++ b

showInst s Metadata{mdLength = len, mdInst = Inst{..}}
        = showPrefix (filter nonSeg inPrefixes)
        .++ (if inOpcode `elem` [Ixlatb] then segOverride else "")
        .++ showOpcode inOpcode
        .++ intercalate ", " (map showOp inOperands)
  where
    showOpcode op = tail $ show op

    segOverride = case [s | Seg s <- inPrefixes] of
        [] -> ""
        [s] -> showSeg s ++ ":"

    showPrefix = \case
        [Rep, RepE]
            | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw] -> "repe"
            | otherwise -> "rep"
        [RepNE] -> "repne"
        [] -> ""

    showSeg = \case
        ES -> val16 es' "es"
        DS -> val16 ds' "ds"
        SS -> val16 ss' "ss"
        CS -> val16 cs' "cs"

    val8 k n = n ++ "{" ++ showA (showHex' 2) (s ^. k) ++ "}"
    val16 k n = n ++ "{" ++ showA (showHex' 4) (s ^. k) ++ "}"

    showReg = \case
        Reg8 r L -> case r of
            RAX -> val8 al' "al"
            RBX -> val8 bl' "bl"
            RCX -> val8 cl' "cl"
            RDX -> val8 dl' "dl"
        Reg8 r H -> case r of
            RAX -> val8 ah' "ah"
            RBX -> val8 bh' "bh"
            RCX -> val8 ch' "ch"
            RDX -> val8 dh' "dh"
        Reg16 r -> case r of
            RBP -> val16 bp' "bp"
            RSP -> val16 sp' "sp"
            RAX -> val16 ax' "ax"
            RBX -> val16 bx' "bx"
            RCX -> val16 cx' "cx"
            RDX -> val16 dx' "dx"
            RSI -> val16 si' "si"
            RDI -> val16 di' "di"
        RegSeg r -> showSeg r
        RegIP -> val16 ip' "ip"
        RegNone -> ""

    showSign v | v < 0 = "-"
               | otherwise = ""

    showOp x = case x of
        Reg r -> showReg r
        Imm (Immediate s v) -> case s of
            Bits8 -> showHex' 2 v ++ "h"
            Bits16 -> showHex' 4 v ++ "h"
        Jump (Immediate size v) -> showAdd (fromDefined (s ^. ips) + fromIntegral len + fromIntegral v) $ case size of
            Bits8 -> showSign v ++ showHex' 2 (abs v) ++ "h"
            Bits16 -> showSign v ++ showHex' 4 (abs v) ++ "h"
        Hdis86.Const (Immediate Bits0 0) -> "1" -- !!! ?
        Ptr (Pointer seg (Immediate Bits16 off)) -> showHex' 4 seg ++ ":" ++ showHex' 4 (fromIntegral off)
        Mem (Memory s b i 0 off)
            -> "[" ++ segOverride ++ (showReg b +.+ showReg i +.+ showImm off) ++ "]"

    showAdd v i = maybe i BSC.unpack $ IM.lookup v (s ^. labels)

    showImm (Immediate s v) = case s of
        Bits0 -> ""
        Bits8 -> showHex' 2 (fromIntegral v :: Word8) ++ "h"
        Bits16 -> showHex' 4 (fromIntegral v :: Word16) ++ "h"


showInst' s Metadata{mdLength = len, mdInst = i@Inst{..}}
        = take 55 $ pad ' ' 5 (showPrefix (filter nonSeg inPrefixes)
        .++ (if inOpcode `elem` [Ixlatb] then segOverride else "")
        .++ showOpcode inOpcode
        ) .++ intercalate "," (map showOp inOperands)
        .++ "  " .++ intercalate "  " (map showOp' inOperands)
  where
    showOpcode op = correct $ tail $ show op
    correct = \case
        "jae" -> "jnc"
        "jb"  -> "jc"
        "jz"  -> "je"
        "jnz" -> "jne"
        "popfw" -> "popf"
        "iretw" -> "iret"
        x -> x

    segmentPrefix = case [s | Seg s <- inPrefixes] of
        [s] -> Just s
        [] -> Nothing
    segOverride = case [s | Seg s <- inPrefixes] of
        [] -> ""
        [s] -> showSeg s ++ ":"

    showPrefix = \case
        [Rep, RepE] -> "repe"
        [RepNE] -> "repne"
        [] -> ""

    showSeg = \case
        ES -> "es"
        DS -> "ds"
        SS -> "ss"
        CS -> "cs"

    showReg = \case
        Reg8 r L -> case r of
            RAX -> "al"
            RBX -> "bl"
            RCX -> "cl"
            RDX -> "dl"
        Reg8 r H -> case r of
            RAX -> "ah"
            RBX -> "bh"
            RCX -> "ch"
            RDX -> "dh"
        Reg16 r -> case r of
            RBP -> "bp"
            RSP -> "sp"
            RAX -> "ax"
            RBX -> "bx"
            RCX -> "cx"
            RDX -> "dx"
            RSI -> "si"
            RDI -> "di"
        RegSeg r -> showSeg r
        RegIP -> "ip"
        RegNone -> ""

    showSign v | v < 0 = "-"
               | otherwise = ""

    showOp x = case x of
        Reg r -> showReg r
        Imm (Immediate s v) -> case s of
            Bits8 -> showHex''' 2 v
            Bits16 -> showHex''' 4 v
        Jump (Immediate size v) -> case size of
            Bits8 -> showSign v ++ showHex''' 2 (abs v)
            Bits16 -> showSign v ++ showHex''' 4 (abs v)
        Hdis86.Const (Immediate Bits0 0) -> "1" -- !!! ?
        Ptr (Pointer seg (Immediate Bits16 off)) -> showHex''' 4 seg ++ ":" ++ showHex''' 4 off
        Mem (Memory s b i 0 off)
            -> segOverride ++ "[" ++ (showReg b +.+ showReg i +.+ showImm off) ++ "]"

    showOp' x = case x of
{-
        Jump (Immediate size v) -> showAdd (fromDefined (s ^. ips) + fromIntegral len + fromIntegral v) $ case size of
            Bits8 -> showSign v ++ showHex' 2 (abs v) ++ "h"
            Bits16 -> showSign v ++ showHex' 4 (abs v) ++ "h"
        Hdis86.Const (Immediate Bits0 0) -> "1" -- !!! ?
        Ptr (Pointer seg (Immediate Bits16 off)) -> showHex' 4 seg ++ ":" ++ showHex' 4 (fromIntegral off)
-}
{-
        Mem m
            -> segOverride ++ "[" ++ showHex' 4 (s ^. addressOf' m) ++ "]=" ++ (case sizeByte_ i of
                1 -> defined "?" (showHex''' 2) $ s ^. byteOperand segmentPrefix x . coerceS_'
                2 -> defined "?" (showHex''' 4) $ s ^. wordOperand segmentPrefix x . coerceS_')
-}
        _   -> ""

--    showAdd v i = maybe i BSC.unpack $ IM.lookup v (s ^. labels)

    showImm (Immediate s v) = case s of
        Bits0 -> ""
        Bits8 -> showHex''' 2 (fromIntegral v :: Word8)
        Bits16 -> showHex''' 4 (fromIntegral v :: Word16)


ifff "" = []
ifff x = [x]

type Queue = [MachineState]

initQueue :: MachineState -> Queue
initQueue s = [s]
addQueue :: MachineState -> Queue -> Queue
addQueue s q = length q' `seq` q'
  where
    q' = take 30 $ s: q
getQueueLast :: Queue -> MachineState
getQueueLast = last

--runTillHalt st = flip evalState st . runErrorT $ do

mkSteps :: MachineState -> (Halt, MachineState)
mkSteps s = either (\x -> (x, s')) (const $ either (\x -> (x, s')) (const $ mkSteps s') b) a
  where
    (ju, a, b, s') = mkStep $ hijack s

addressOf a b = evalExp $ Edsl.addressOf a b
addressOf' a = evalExp $ Edsl.addressOf' a
byteOperand a b = evalPart $ Edsl.byteOperand a b
wordOperand a b = evalPart $ Edsl.wordOperand a b


askCounter = do
    c <- use $ config . counter'
    case c of
      [] -> do
        cc <- use $ config . counter
        if maybe False (<=0) cc
          then do
            trace_ "timer now"            
            config . counter .= Nothing
            --setCounter
            return True
          else do
            config . counter %= fmap (+(-1)) --pred
            return False
      (c:cc) -> do
        ns <- use $ config . stepsCounter
        if c <= ns then do
            config . counter' %= tail
            return True
          else do
            return False

hijack :: MachineState -> MachineState
hijack s = flip execState s $ runExceptT{-!!!-} $ do
    mask <- use intMask
    when (not (mask ^. bit 0)) $ do
        cc <- askCounter
        when cc $ do
            trace_ "timer"
            interrupt_ 0x08


mkStep
  :: MachineState
     -> ( Bool
        , Either Halt (Either Metadata String)
        , Either Halt (Set.Set Key, String)
        , MachineState
        )
mkStep s = (ju, either Left (Right . fst) <$> x__, y, s') where
    (x__, s_) = flip runState s $ runExceptT $ do
        md <- fetchInstr
        _ <- clearHist
        return md

    (ju, (y, s')) = case x__ of
        Right (Right (_, m)) -> (True, flip runState s_ $ runExceptT $ m >> clearHist)
        Right (Left md) -> (,) ju $ flip runState s_ $ runExceptT $ do
            m
            config . stepsCounter %= succ
            clearHist
          where (ju, m) = execInstruction md
        Left _ -> (True, error "mkStep")
        


verboseLevel' s
    = if s ^. disassStart == 0 then 3 else if s ^. stepsCounter >= s ^. disassStart then 2 else s ^. verboseLevel
    

cachedStep :: Machine ()
cachedStep = do
    Defined ips <- use ips
    c <- use cache
    case IM.lookup ips c of
      Just m -> m
      _ -> do
        let collect = do
                md <- fetchInstr
                ip' <- use ip
                let (jump, m_) = case md of
                        Left md -> execInstruction md
                        Right (_, m) -> (True, m)
                    m = ip .= ip' >> m_
                m_
                (m >>) <$> if jump
                  then return (return ())
                  else collect

        m <- collect
        cache %= IM.insert ips m

showCode q s = showCodeH q $ hijack s
{-
showCodeHC :: Queue -> MachineState -> [String]
showCodeHC q s = case IM.lookup addr (s ^. cache) of
    Just f -> case f q s of (str, q, s) -> str ++ showCode q s
    Nothing -> showCode q' (s' & cache %~ IM.insert addr f)
  where
    Defined addr = s ^. ips

    (f, (q', s')) = collect q s

    collect q s =

        showCode_ q s

    collect = do
        md <- fetchInstr
        ip' <- use ip
        let (jump, m_) = case md of
                Left md -> execInstruction md
                Right (_, m) -> (True, m)
            m = ip .= ip' >> m_
        m_
        (m >>) <$> if jump
          then return (return ())
          else collect

 case showCode_ q s of
    (_, str, Left e) -> str ++ showErr q s e
    (_, str, Right (q, s)) -> str ++ showCode q s
-}
showCodeH :: Queue -> MachineState -> [String]
showCodeH q s = case showCode_ q s of
    (_, str, Left e) -> str ++ showErr q s e
    (_, str, Right (q, s)) -> str ++ showCode q s

showErr q s e = case verboseLevel' $ s ^. config of
  1 -> showCode (initQueue s'') s''
  _ -> show e: []
 where
    s'' = getQueueLast q & config . verboseLevel .~ 2


showCode_ :: Queue -> MachineState -> (Bool, [String], Either Halt (Queue, MachineState))
showCode_ q s = case x_ of
    Left e -> (ju, [], Left e)
    Right q -> next $ case q of
     Right x -> case verboseLevel' $ s ^. config of
      3 -> []
      _ -> ifff traces
        ++ [vid | ns `mod` ((s ^. config . instPerSec) `div` 25) == 0]
     Left x -> case verboseLevel' $ s ^. config of 
      1 -> ifff traces
        ++ [vid | ns `mod` ((s ^. config . instPerSec) `div` 25) == 0]
      2 -> dbstyle x
      4 ->
        maybeToList (BSC.unpack <$> IM.lookup (fromDefined $ s ^. ips) (s ^. labels))
         ++
         ["  " ++ pad ' ' 14 (map toUpper $ mdHex x)
         ++ " "++ pad ' ' 27 (showInst s x)
         ++ "" ++ traces
         ++ (if inOpcode (mdInst x) `elem` [Icall] then " " ++ intercalate "/" (map BSC.unpack . catMaybes . map (`IM.lookup` (s ^. labels)) $ s ^. config . stackTrace) else "")
         ++ "  " ++ unwords (map shKey $ combineKey $ Set.toList hist_)]
        
{-
      3 -> case s ^. config . stepsCounter of
            c | c `mod` 10000 == 0 -> show c: next
            _ -> next
-}
      3 -> dbstyle x
      _ -> []
 where
    dbstyle x = [unwords (
        [ showReg' (showHex'' 4 (s ^. cs)) ip
        , " " ++ pad ' ' 54 (showInst' s x)
        ]
        ++ zipWith showReg' ["EAX","EBX","ECX","EDX","ESI","EDI","EBP","ESP"] [ax,bx,cx,dx,si,di,bp,sp]
        ++ zipWith showReg ["DS","ES","FS","GS","SS"] [ds,es,fs,gs,ss]
        ++ zipWith showFlag "CZSOAPI" [carryF, zeroF, signF, overflowF, adjustF, parityF, interruptF]
        )]


    showReg c k = c ++ ":" ++ showHex'' 4 (s ^. k)
    showReg' c k = c ++ ":" ++ showHex'' 8 (s ^. k)
    showFlag c k = c : "F:" ++ defined "?" (show . fromEnum) (s ^. k)

    ns = s ^. config . stepsCounter

    vid = unsafePerformIO $ do
        let gs = 0xa0000 --0x30000 -- x ^. heap16 0x6 . coerceS . paragraph
            v = s ^. heap . memSlice (gs ^. byte) ((320 * 200) ^. byte)
        putMVar (s ^. config . videoMVar) $ \x y -> defined 0x80 id $ v ^. byteAt' ((320 * y + x) ^. byte) . coerceS_'
        return $ show ns ++ "; mem: " ++ showMemPiece (s ^. heap)
                               --      show (length $ flattenMemPiece unGroup keepMemSlice keepMemTimes (s ^. heap))

    (hist_, traces) = case y of
        Left e -> (Set.empty, "lost history because " ++ show e)
        Right s -> s

    next xs = (ju, xs, case y of
        Left e -> Left e
        Right _ -> q' `seq` Right (q', s'))
    q' = addQueue s' q

    (ju, x_, y, s') = mkStep s

    shKey k = case k of
        Heap 8 i  -> diff (sh'' 1) $ heap . byteAt' i
        Heap 16 i  -> diff (sh'' 2) $ heap . wordAt' i
        Heap n i  -> "[" ++ showAddr i ++ "-" ++ showAddr (i+n) ++ "]"
        Flag n  -> diff (sf [n]) $ flags . (case n of
            'c' -> carryF'
            'p' -> parityF'
            'a' -> adjustF'
            'z' -> zeroF'
            's' -> signF'
            'i' -> interruptF'
            'd' -> directionF'
            'o' -> overflowF'
            )
        Flags     -> diff showFlags flags
        KReg 8 i  -> diff (sh'' 1) $ regs . byteAt' i
        KReg 16 i  -> diff (sh'' 2) $ regs . wordAt' i
        KReg 32 i  -> diff (sh'' 4) $ regs . dwordAt' i
      where
        diff :: Eq a => (a -> String) -> Lens' MachineState a -> String
        diff f l = par (v == v') $ f v'
          where
            v = s ^. l
            v' = s' ^. l

        lok i def = maybe def (\s -> "[" ++ BSC.unpack s ++ "]") $ IM.lookup i (s ^. labels)

        sh :: (Show a, Integral a) => Int -> a -> String
        sh i v = show k ++ ":" ++ showHex' (2*i) v

        sh'' :: (Show a, WordX a) => Int -> MemPieceS a -> String
        sh'' i v = lok i (show k) ++ ":" ++ showA (showHex' (2*i)) v

        sf k (Defined True) = map toUpper k
        sf k (Defined False) = k
        sf k Undefined = k ++ "?"

        par True a = "(" ++ a ++ ")"
        par False a = a

immLens :: a -> Lens' b a
immLens c = lens (const c) $ \_ _ -> error "can't update immediate value"


fetchInstr :: Machine (Either Metadata (String, Machine ()))
fetchInstr = do
    Defined cs_ <- use cs
    Defined ip_ <- use ip
    case M.lookup (cs_, ip_) origInterrupt of
      Just (i, m) -> return $ Right ("interrupt " ++ showHex' 2 i ++ "h", m)
      Nothing -> do
        Defined ips <- use ips
        Just (md, _) <- disassembleOne disasmConfig . BS.pack . getDef . fromRom <$> use (heap . memSlice ips (maxInstLength ^. byte))
        ip %= (+ fromIntegral (mdLength md))
        return $ Left md

getDef (Defined a: as) = a: getDef as
getDef _ = []

maxInstLength = 7

disasmConfig = Config Intel Mode16 SyntaxIntel 0


execInstruction :: Metadata -> (Bool, Machine ())
execInstruction m = (True, evalExp $ execInstruction' m)

useD k = do
    x <- use k
    defined (throwError $ Err "useD") return x

evalPart :: Part a -> (MachinePart a -> Machine e) -> Machine e
evalPart p cont = evalPart' p $ \x -> cont $ x . iso fromDefined Defined

evalPart' :: Part a -> (MachinePart (Defined a) -> Machine e) -> Machine e
evalPart' p cont = case p of
    Heap8 e -> evalExp e >>= \i -> cont $ heap8 i . coerceS_'
    Heap16 e -> evalExp e >>= \i -> cont $ heap16 i . coerceS_'
    Immed e -> evalExp e >>= \i -> cont $ immLens $ Defined i
    _ -> cont $ evalPart_ p

evalPart_ :: Part a -> MachinePart (Defined a)
evalPart_ = \case
    IP -> ip
    AX -> ax
    BX -> bx
    CX -> cx
    DX -> dx
    SI -> si
    DI -> di
    BP -> bp
    SP -> sp
    Es -> es
    Ds -> ds
    Ss -> ss
    Cs -> cs
    Low x -> evalPart_ x . from coerceS_' . low' . coerceS_'
    High x -> evalPart_ x . from coerceS_' . high' . coerceS_'
    CF -> carryF
    PF -> parityF
    AF -> adjustF
    ZF -> zeroF
    SF -> signF
    IF -> interruptF
    DF -> directionF
    OF -> overflowF
    Edsl.Flags -> flags . coerceS_'
    DXAX -> dxax . coerceS_'
    XX -> xx . coerceS_'

evalExp :: Exp a -> Machine a
evalExp = \case
    C a -> return a

    Get p -> evalPart p $ \k -> use k
    Set p e -> evalPart p $ \k -> (k .=) =<< evalExp e

    If b x y -> evalExp b >>= \b -> evalExp $ if b then x else y
    Eq x y -> liftM2 (==) (evalExp x) (evalExp y)

    Not a -> complement <$> evalExp a
    ShiftL a -> (`shiftL` 1) <$> evalExp a
    ShiftR a -> (`shiftR` 1) <$> evalExp a
    RotateL a -> (`rotateL` 1) <$> evalExp a
    RotateR a -> (`rotateR` 1) <$> evalExp a
    Sub a b -> liftM2 (-) (evalExp a) (evalExp b)
    Add a b -> liftM2 (+) (evalExp a) (evalExp b)
    Mul a b -> liftM2 (*) (evalExp a) (evalExp b)
    And a b -> liftM2 (.&.) (evalExp a) (evalExp b)
    Or  a b -> liftM2 (.|.) (evalExp a) (evalExp b)
    Xor a b -> liftM2 xor (evalExp a) (evalExp b)

    QuotRem a b c f -> do
        x <- evalExp a
        y <- evalExp b
        case quotRemSafe x y of
            Nothing -> evalExp c
            Just (z,v) -> evalExp $ f (C z, C v)

    Bit i e -> (^. bit i) <$> evalExp e
    SetBit i e f -> liftM2 (\a b -> b & bit i .~ a) (evalExp e) (evalExp f)
    HighBit e -> (^. highBit) <$> evalExp e
    SetHighBit e f -> liftM2 (\a b -> b & highBit .~ a) (evalExp e) (evalExp f)
    EvenParity e -> even . popCount <$> evalExp e

    Signed e -> asSigned <$> evalExp e    
    Extend e -> extend <$> evalExp e    
    SegAddr e f -> liftM2 segAddr (evalExp e) (evalExp f)
    Convert e -> fromIntegral <$> evalExp e    

    Let e f -> evalExp e >>= evalExp . f . C
    Seq a b -> evalExp a >> evalExp b
    Tuple a b -> liftM2 (,) (evalExp a) (evalExp b)
    Fst p -> fst <$> evalExp p
    Snd p -> snd <$> evalExp p

    Iterate n f a -> evalExp n >>= \i -> evalExp $ iterate f a !! i
    Replicate n e -> evalExp n >>= \i -> replicateM_ i $ evalExp e
    Input a -> evalExp a >>= fmap (^. coerceS' "1368") . input
    Output a b -> evalExp a >>= \x -> evalExp b >>= \y -> output' x y

    Error h -> throwError h
    Interrupt e -> evalExp e >>= evalExp . interrupt

    Trace a -> trace_ a

execInstructionBody m = (True {-TODO-}, evalExp $ compileInst m)


input :: Word16 -> Machine (MemPiece16)
input v = do
    case v of
        0x21 -> do
            x <- use intMask
            trace_ $ "get interrupt mask " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x60 -> do
            trace_ "keyboard"
            return $ "???" @: 0
        0x61 -> do
            x <- use $ config . speaker
            trace_ $ "get internal speaker: " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x03da -> do
            r <- getRetrace
            trace_ $ "VGA hardware " ++ showHex' 4 r
            return $ "Vretrace | DD" @: r
        _ -> throwError $ Err $ "input #" ++ showHex' 4 v

output' :: Word16 -> Word16 -> Machine ()
output' v x = do
    case v of
        0x20 -> do
            trace_ $ "int resume " ++ showHex' 2 x  -- ?
            case x of
              0x20 -> setCounter
        0x21 -> do
            trace_ $ "set interrupt mask " ++ showHex' 2 x  -- ?
            intMask .= fromIntegral x
            when (not $ x ^. bit 0) setCounter
        0x40 -> do
            trace_ $ "set timer frequency " ++ showHex' 2 x --show (1193182 / fromIntegral x) ++ " HZ"
        0x41 -> do
            trace_ $ "timer chip 41 " ++ showHex' 2 x  -- ?
        0x42 -> do
            trace_ $ "timer chip 42 " ++ showHex' 2 x
        0x43 -> do
            trace_ $ "set timer control " ++ showHex' 2 x
            case x of
                0x36  -> trace_ "set timer frequency lsb+msb, square wave"
                0xb6  -> trace_ "set speaker frequency lsb+msb, square wave"
        0x61 -> do
            config . speaker .= fromIntegral x
            trace_ $ "set internal speaker: " ++ showHex' 2 x
        0xf100 -> do
            trace_ "implemented for jmpmov test"
        _ -> throwError $ Err $ "output #" ++ showHex' 4 v ++ " 0x" ++ showHex' 4 x

--------------------------------------------------------

imMax m | IM.null m = 0
        | otherwise = succ . fst . IM.findMax $ m
{-
origInt v = case v of
    0x08 -> return ()
    _ -> throwError $ Err $ "origInt " ++ showHex' 2 v
-}
interrupt_ :: Word8 -> Machine ()
interrupt_ n = do
    i <- useD interruptF
    if i then evalExp (interrupt n)
         else trace_ $ "interrupt cancelled " ++ showHex' 2 n

{-# NOINLINE unsafePerformIO' #-}
unsafePerformIO' :: Monad m => IO a -> m a
unsafePerformIO' x = return $! unsafePerformIO x

origInterrupt :: M.Map (Word16, Word16) (Word8, Machine ())
origInterrupt = M.fromList

  [ item 0x00 (0xf000,0x1060) $ do
    trace_ "divison by zero interrupt"
    throwError $ Err $ "int 00"

  , item 0x08 (0xf000,0xfea5) $ do     -- 
    trace_ "timer interrupt again"
    output' 0x20 0x20

  , item 0x09 (0xf000,0xe987) $ do     -- 09
    trace_ "keyboard interrupt again"
    throwError $ Err $ "int 09"

  , item 0x10 (0xf000,0x1320) $ do     -- 10h
    trace_ "Video Services"
    v <- use ah
    case v of
        0x00 -> do
            video_mode_number <- use al
            trace_ $ "Set Video Mode #" ++ showHex' 2 video_mode_number
            case video_mode_number of
                0x00 -> do
                    trace_ "text mode"
                0x03 -> do
                    trace_ "mode 3"
                0x13 -> do
                    bx .= 0  -- 4  -- ???
                _ -> throwError $ Err $ "#" ++ showHex' 2 video_mode_number
        0x0b -> do
            trace_ "Select Graphics Palette or Text Border Color"
        0x0e -> do
            a <- use al
            unsafePerformIO' $ putChar $ chr . fromIntegral $ a
            trace_ $ "Write Character as TTY: " ++ showHex' 2 a
            
--            traceM $ (:[]) . chr . fromIntegral $ a
        0x0f -> do
            trace_ "Get Current Video Mode"
            al' .= "text mode" @: 3
            ah' .= "width of screen, in character columns" @: 80
            bh' .= "current active video page (0-based)" @: 0x00 --b8
        0x10 -> do
            trace_ "Set/Get Palette Registers (EGA/VGA)"
            f <- use al
            case f of
              0x12 -> do
                trace_ "set block of DAC color registers"

              v -> throwError $ Err $ "interrupt #10,#10,#" ++ showHex' 2 f

        v  -> throwError $ Err $ "interrupt #10,#" ++ showHex' 2 v

  , item 0x15 (0xf000,0x11e0) $ do     -- 15h
    trace_ "Misc System Services"
    v <- use ah
    case v of
--      0x00 -> do
--        trace_ "Turn on casette driver motor"
      0xc2 -> do
        trace_ "Pointing device BIOS interface"
        w <- use al
        case w of
          0x01 -> do
            trace_ "Reset Pointing device"
            ah .= 0 -- ?
            bl .= 0xaa -- ?
            carryF .= Defined False
      v  -> throwError $ Err $ "interrupt #15,#" ++ showHex' 2 v

  , item 0x16 (0xf000,0x1200) $ do     -- 16h
    trace_ "Keyboard Services"
    v <- use ah
    case v of
        0x00 -> do
            trace_ "Read (Wait for) Next Keystroke"
            ah' .= "Esc scan code" @: 0x39
            al' .= "Esc ASCII code" @: 0x1b
        0x01 -> do
            trace_ "Query Keyboard Status / Preview Key"
            zeroF .= Defined False  -- no keys in buffer
        v  -> throwError $ Err $ "interrupt #16,#" ++ showHex' 2 v

{-
  0x20 -> do
    trace_ "interrupt halt"
    throwError CleanHalt
-}

  , item 0x21 (0xf000,0x14c0) $ do     -- 21h
    trace_ "DOS rutine"
    v <- use ah
    case v of
        0x00 -> do
            trace_ "dos Program terminate"
            throwError CleanHalt

        0x1a -> do
            trace_ "Set Disk Transfer Address (DTA)"
            addr <- addressOf Nothing (memIndex RDX)
            dta .= addr

        0x25 -> do
            v <- fromIntegral <$> use al     -- interrupt vector number
            trace_ $ "Set Interrupt Vector " ++ showHex' 2 v
            use dx' >>= (heap16 (4*v ^. byte) .=)     -- DS:DX = pointer to interrupt handler
            use ds' >>= (heap16 (4*v ^. byte + 16) .=)

        0x30 -> do
            trace_ "Get DOS version"
            al' .= "major version number" @: 0x05      --  (2-5)
            ah' .= "minor version number" @: 0x00      --  (in hundredths decimal)
            bh' .= "MS-DOS" @: 0xff
            do              -- 24 bit OEM serial number
                bl' .= "OEM serial number (high bits)" @: 0
                cx' .= "OEM serial number (low bits)" @: 0

        0x35 -> do
            v <- fromIntegral <$> use al     -- interrupt vector number
            trace_ $ "Get Interrupt Vector " ++ showHex' 2 v
            use (heap16 (4*v ^. byte)) >>= (bx' .=)
            use (heap16 (4*v ^. byte + 16)) >>= (es' .=)   -- ES:BX = pointer to interrupt handler

        0x3d -> do
            trace_ "Open File Using Handle"
            open_access_mode <- use al
--            v <- use dx
            case open_access_mode of
              0 -> do   -- read mode
                addr <- addressOf Nothing $ memIndex RDX
                fname <- use $ heap . bytesAt addr 20
                let f = map (toUpper . chr . fromIntegral . defined (error "fname") id) $ takeWhile (/=0) fname
                trace_ $ "File: " ++ show f
                let fn = "../original/" ++ f
                let s = unsafePerformIO $ do
                        b <- doesFileExist fn
                        if b then Just <$> BS.readFile fn else return Nothing
                case s of
                  Nothing -> do
                    trace_ $ "not found"
                    ax' .= "File not found" @: 0x02
                    carryF .= Defined True
                  Just s -> do
        --            ax .= 02  -- File not found
                    handle <- max 5 . imMax <$> use files
                    trace_ $ "handle " ++ showHex' 4 handle
                    files %= IM.insert handle (fn, s, 0)
                    ax' .= "file handle" @: fromIntegral handle
                    carryF .= Defined False

        0x3e -> do
            trace_ "Close file"
            handle <- fromIntegral <$> use bx
            trace_ $ "handle " ++ showHex' 4 handle
            x <- IM.lookup handle <$> use files
            case x of
              Just (fn, _, _) -> do
                trace_ $ "file: " ++ fn
                files %= IM.delete handle
                carryF .= Defined False

        0x3f -> do
            handle <- fromIntegral <$> use bx
            fn <- (^. _1) . (IM.! handle) <$> use files
            num <- fromIntegral <$> use cx
            trace_ $ "Read " ++ showHex' 4 handle ++ ":" ++ fn ++ " " ++ showHex' 4 num
            loc <- addressOf Nothing $ memIndex RDX
            s <- BS.take num . (\(fn, s, p) -> BS.drop p s) . (IM.! handle) <$> use files
            let len = BS.length s
            files %= flip IM.adjust handle (\(fn, s, p) -> (fn, s, p+len))
            heap . bytesAt loc len .= map Defined (BS.unpack s)
            ax' .= "length" @: fromIntegral len
            carryF .= Defined False

        0x40 -> do
            handle <- fromIntegral <$> use bx
            trace_ $ "Write to " ++ showHex' 4 handle
            num <- fromIntegral <$> use cx
            loc <- addressOf Nothing $ memIndex RDX
            case handle of
              1 -> trace_ . ("STDOUT: " ++) . map (chr . fromIntegral . defined (error "stdout") id) =<< use (heap . bytesAt loc num)
              2 -> trace_ . ("STDERR: " ++) . map (chr . fromIntegral . defined (error "stderr") id) =<< use (heap . bytesAt loc num)
              _ -> return ()
            carryF .= Defined False

        0x42 -> do
            handle <- fromIntegral <$> use bx
            fn <- (^. _1) . (IM.! handle) <$> use files
            mode <- use al
            pos <- fromIntegral . asSigned <$> use (uComb cx dx . combine)
            trace_ $ "Seek " ++ showHex' 4 handle ++ ":" ++ fn ++ " to " ++ show mode ++ ":" ++ showHex' 8 pos
            files %= (flip IM.adjust handle $ \(fn, s, p) -> case mode of
                0 -> (fn, s, pos)
                1 -> (fn, s, p + pos)
                2 -> (fn, s, BS.length s + pos)
                )
            pos' <- (^. _3) . (IM.! handle) <$> use files
            (uComb dx ax . combine) .= fromIntegral pos'
            carryF .= Defined False

        0x44 -> do
            trace_ "I/O Control for Devices (IOCTL)"
            0x44 <- use ah
            function_value <- use al
{-
            file_handle <- use bx
            logical_device_number <- use bl -- 0=default, 1=A:, 2=B:, 3=C:, ...
            number_of_bytes_to_read_or_write <- use cx
            data_or_buffer <- use dx
-}
            case function_value of
              0x00 -> do
                handle <- use bx
                trace_ $ "Get Device Information of " ++ show handle 
                let v = case handle of
                      4 -> 0x80A0        --  0010 1000 00 000100   no D: drive
                      3 -> 0x80D3        --  0010 1000 00 000011   no C: drive
                      2 -> 0x80D3        --  0010 1000 00 000011    B: drive
                      1 -> 0x80D3        --  0010 1000 00 000011    A: drive
                      0 -> 0x80D3        --  0010 1000 00 000011    default drive
                dx .= v
                ax .= v
            carryF .= Defined False

        0x48 -> do
            memory_paragraphs_requested <- def =<< use bx
            trace_ $ "Allocate Memory " ++ showHex' 5 (memory_paragraphs_requested ^. paragraph)
            x <- zoom heap $ allocateMem' (memory_paragraphs_requested ^. paragraph ^. byte)
            ax' .= "segment address of allocated memory block" @: (x ^. from (paragraph . byte)) -- (MCB + 1para)
            use heap >>= trace_ . showMemPiece
            carryF .= Defined False

        0x4a -> do
            new_requested_block_size_in_paragraphs <- def =<< use bx
            trace_ $ "Modify allocated memory blocks to " ++ showHex' 4 new_requested_block_size_in_paragraphs
            segment_of_the_block <- def =<< use es      -- (MCB + 1para)
--            throwError $ Err $ showRom rom
            h <- use heap
            case modifyAllocated (segment_of_the_block ^. paragraph . byte) (new_requested_block_size_in_paragraphs ^. paragraph . byte) h of
              Left x -> do
                ax' .= "Insufficient memory error" @: 8
                bx' .= "maximum block size possible" @: (x ^. from (paragraph . byte))
                trace_ $ "insufficient, max possible: " ++ showHex' 4 (x ^. from (paragraph . byte))
                carryF .= Defined True
              Right h -> do
                ds <- use ds'
                ax' .= ds  -- why???
                heap .= h
                use heap >>= trace_ . showMemPiece
                carryF .= Defined False

        0x4c -> do
            code <- use al
            trace_ $ "Terminate Process With Return Code #" ++ showHex' 2 code
            throwError CleanHalt

        0x4e -> do
            attribute_used_during_search <- use cx
            addr <- addressOf Nothing $ memIndex RDX
            fname <- use $ heap . bytesAt addr 20
            let f_ = map (chr . fromIntegral . defined (error "fname'") id) $ takeWhile (/=0) fname
            trace_ $ "Find file " ++ show f_
            ad <- use dta
--            throwError Halt

            let s = unsafePerformIO $ do
                    b <- globDir1 (compile $ map toUpper f_) "../original"
                    case b of
                        (f:_) -> Just . (,) f <$> BS.readFile f
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
                heap . bytesAt (0 ^. byte) 0x1a .= map (error . ("undefined byte " ++) . showHex' 2) [0..]
                heap8 (0x00 ^. byte) .= "attribute of serach" @: fromIntegral attribute_used_during_search
                heap8 (0x01 ^. byte) .= "disk used during search" @: 2  -- C:
                heap . bytesAt (0x02 ^. byte) 11 .= pad 0 11 fname
                heap . dwordAt (ad + 0x1a ^. byte) .= fromIntegral (BS.length s)
                heap . bytesAt (ad + 0x1e ^. byte) 13 .= pad 0 13 (map (fromIntegral . ord) (takeFileName f) ++ [0])
                ax .= 0 -- ?
                carryF .= Defined False
              Nothing -> do
                trace_ $ "not found"
                ax .= 02  -- File not found
                carryF .= Defined True

        0x62 -> do
            trace_ "Get PSP address (DOS 3.x)"
            bx' .= "segment address of current process" @: 0x1fe  -- hack!!!  !!!
            carryF .= Defined False

        _    -> throwError $ Err $ "dos function #" ++ showHex' 2 v

  , item 0x24 (0x0118,0x0110) $ do     -- 24h
    trace_ "critical error handler interrupt"
    throwError $ Err $ "int 24"

  , item 0x33 (0xc7ff,0x0010) $ do     -- 33h
    trace_ "Mouse Services"
    v <- use ax
    case v of
        0x00 -> do
            trace_ "Mouse Reset/Get Mouse Installed Flag"
            ax' .= "mouse?" @: 0xffff -- "mouse driver not installed" @: 0x0000
            bx' .= "number of buttons" @: 3 -- 0
        0x03 -> do
            trace_ "Get Mouse position and button status"
            cx' .= "mouse X" @: 0
            dx' .= "mouse Y" @: 0
            bx' .= "button status" @: 0
        0x07 -> do
            trace_ "Set Mouse Horizontal Min/Max Position"
            minimum_horizontal_position <- use cx'
            maximum_horizontal_position <- use dx'
            return ()
        0x08 -> do
            trace_ "Set Mouse Vertical Min/Max Position"
            minimum_vertical_position <- use cx'
            maximum_vertical_position <- use dx'
            return ()
        0x0f -> do
            trace_ "Set Mouse Mickey Pixel Ratio"
        _    -> throwError $ Err $ "Int 33h, #" ++ showHex' 2 v
  ]
  where 
    item :: Word8 -> (Word16, Word16) -> Machine () -> ((Word16, Word16), (Word8, Machine ()))
    item a k m = (k, (a, m >> evalExp iret))


----------------------------------------------
{-
infixl 9 @.
m @. i = push_ i >> m

class PushVal a where
    push_ :: a -> Machine ()
instance PushVal Word16 where
    push_ = push . noAnn
-}
----------------------------------------------

prelude1, prelude :: [Word8]
prelude1
     = [error $ "interruptTable " ++ showHex' 2 (i `div` 4) | i <- [0..1023]]
    ++ replicate 172 (error "BIOS communication area")
    ++ replicate 68 (error "reserved by IBM")
    ++ replicate 16 (error "user communication area")
    ++ replicate 256 (error "DOS communication area")
    ++ [error $ "dos area " ++ showHex' 2 i | i <- [0x600 ..0x700-1]]
prelude
     = prelude1
    ++ [error $ "dos area " ++ showHex' 2 i | i <- [length prelude1..0x1f40-1]]

origTimer =
    [0x50, 0xb0, 0x20, 0xe6, 0x20, 0x58, 0xcf]       -- push ax; mov al, 20h; out 20h, al; pop ax; iret
    ++ replicate (maxInstLength - 1) 0  -- hack for fetchinstruction

loadTest :: BS.ByteString -> MachineState
loadTest com = flip execState emptyState $ do
    heap .= mconcat
        [ memTimes 0xf0000 $ memBits 0 8 0
        , toRam $ BS.unpack com ++ replicate 64 0 -- extra bytes for decoding
        ]
    cs .= loadSegment
    ds .= loadSegment
    es .= loadSegment
    ip .= 0xfff0
    ax .= 0
    bx .= 0
    cx .= 1
    di .= 0
    si .= 0

    ds .= 0
    ss .= stackSegment
    sp .= 0

--    flags .= 0x0017
--    carryF .= False
--    interruptF .= False
--    heap8 0x410 .= noAnn 0x41   -- ???

    clearHist
  where
    loadSegment = 0xf000
    stackSegment = 0 --0xe000

loadCom :: BS.ByteString -> MachineState
loadCom com = flip execState emptyState $ do
    heap .= toRam (concat
        [ prelude
        , replicate (loadSegment ^. paragraph - length prelude + 0x100) 0
        , BS.unpack com
        , replicate (l' - l + stacksize + 2^16) 0
        ])

    cs .= Defined loadSegment
    ds .= Defined loadSegment
    es .= Defined loadSegment
    ip .= 0x0100
    ax .= 0
    bx .= 0
    cx .= 1
    di .= 0xfffe
    si .= 0x0100

    forM_ [0xfff4..0xffff] $ \i -> do
        heap8 (segAddr gs i) .= "junk" @: 1
    heap8 (segAddr gs 0x20cd) .= "junk" @: 1

    ss .= Defined (l' ^. from paragraph)
    sp .= fromIntegral stacksize
    heap16 (4 ^. byte) .= "???" @: 0
    heap16 (6 ^. byte) .= "segment" @: gs

    clearHist
  where
    l = BS.length com + loadSegment ^. paragraph
    l' = bitAlign 4 l
    gs = (l' + stacksize) ^. from paragraph

    stacksize = 2^8 :: Int

    loadSegment = 0x1000

programSegmentPrefix :: Word16 -> Word16 -> BS.ByteString -> MemPiece
programSegmentPrefix envseg endseg args = flip execState (toRam $ map (error . ("psp uninitialized byte: " ++) . showHex' 2) [0..0xff] :: MemPiece) $ do

    wordAt' (0x00 ^. byte) .= "CP/M exit, always contain code 'int 20h'" @: 0x20CD
    wordAt' (0x02 ^. byte) .= "Segment of the first byte beyond the memory allocated to the program" @: endseg
--    bytesAt 0x05 5 .= [0xea, 0xff, 0xff, 0xad, 0xde]   -- FAR call to MSDOS function dispatcher (int 21h)?
--    dwordAt 0x0a .= 0xf00020c8    -- Terminate address of previous program (old INT 22h)
--    dwordAt 0x0e .= 0x01180000    -- Break address of previous program (old INT 23h)
--    dwordAt 0x12 .= 0x01180110    -- Critical error address of previous program (old INT 24h)
--    wordAt 0x16 .= 0x0118    -- Caller's PSP segment (usually COMMAND.COM - internal)

    -- Job File Table (JFT) (internal)
--    bytesAt 0x18 20 .= [0x01, 0x01, 0x01, 0x00, 0x02, 0x03] ++ repeat 0xff

    wordAt' (0x2c ^. byte) .= "Environment segment" @: envseg
--    dwordAt 0x2e .= 0x0192ffe6 -- SS:SP on entry to last INT 21h call (internal)

--    wordAt 0x32 .= 0x0014 -- JFT size (internal)
--    dwordAt 0x34 .= 0x01920018-- Pointer to JFT (internal)
--    dwordAt 0x38 .= 0xffffffff -- Pointer to previous PSP (only used by SHARE in DOS 3.3 and later)
    -- 3Ch-3Fh     4 bytes     Reserved
--    wordAt 0x40 .= 0x0005 -- DOS version to return (DOS 4 and later, alterable via SETVER in DOS 5 and later)
    -- 42h-4Fh     14 bytes     Reserved
    bytesAt (0x50 ^. byte) 3 .= [0xcd, 0x21, 0xcb] -- (code) Far call to DOS (always contain INT 21h + RETF)
    -- 53h-54h     2 bytes     Reserved
    -- 55h-5Bh     7 bytes     Reserved (can be used to make first FCB into an extended FCB)

    -- 5Ch-6Bh     16 bytes     Unopened Standard FCB 1
    -- 6Ch-7Fh     20 bytes     Unopened Standard FCB 2 (overwritten if FCB 1 is opened)
--    bytesAt 0x5c (16 + 20) .= repeat 0

    byteAt' (0x80 ^. byte) .= "args length" @: fromIntegral (min maxlength $ BS.length args)
    bytesAt (0x81 ^. byte) (maxlength + 1) .= pad 0 (maxlength + 1) (take maxlength (map Defined $ BS.unpack args) ++ [0x0D])  -- Command line string
--    byteAt 0xff .= 0x36   -- dosbox specific?
  where
    maxlength = 125

pspSize = 256 :: Int


--
envvars :: [Word8]
                                                                              
envvars = map (fromIntegral . ord) "PATH=Z:\\\NULCOMSPEC=Z:\\COMMAND.COM\NULBLASTER=A220 I7 D1 H5 T6\0\0\1\0C:\\GAME.EXE" ++
 replicate 20 0
--envvars = map (fromIntegral . ord) "COMSPEC=C:\\cmd.exe\NULPATH=C:\NULPROMPT=$P\NUL\NUL\NULC:\\game.exe\NUL" ++ replicate 20 0

--envvars = [0,0,0,0,0] --"\NUL\NUL\NUL\NUL\NUL\NUL" -- BS.concat (map (`BS.append` "\NUL") ["PATH="]) `BS.append` "\NUL"

replicate' n _ | n < 0 = error "replicate'"
replicate' n x = replicate n x

loadExe :: IM.IntMap BS.ByteString -> Word16 -> BS.ByteString -> MachineState
loadExe labs loadSegment gameExe = flip execState emptyState $ do
    heap .= mconcat
            [ rom2
            , memUndefined' $ 0xa0000 ^. byte - measure rom2 - 16 ^. byte -- ???
            , toRam $ replicate 16 $ error "unknown reserved"
            , memUndefined' $ 0x10000 ^. byte
            , memUndefined' $ 0x50000 ^. byte
            ]
    ss .= Defined (ssInit + loadSegment)
    sp .= Defined spInit
    cs .= Defined (csInit + loadSegment)
    ip .= Defined ipInit
    ds .= Defined pspSegment
    es .= Defined pspSegment
    cx .= Defined 0x00ff -- why?
    dx .= Defined pspSegment -- why?
    bp .= Defined 0x091c -- why?
    si .= Defined 0x0012 -- why?
    di .= Defined 0x1f40 -- why?
    labels .= IM.fromDistinctAscList (map (((^. byte) . (+ reladd)) *** id) $ IM.toList labs)

    mapM_ inter [(fromIntegral a, b) | (b, (a, _)) <- M.toList origInterrupt]

    heap16 (0x410 ^. byte) .= "equipment word" @: 0xd426 --- 0x4463   --- ???
    heap8  (0x417 ^. byte) .= "keyboard shift flag 1" @: 0x20

--    heap . bytesAt ((0xf000 ^. paragraph + 0xfea5) ^. byte) (length origTimer) .= origTimer

--    heap8 ((0x3b590 + 0x0498) ^. byte) .= "?" @: 0 -- !!! !!! !!!

    clearHist
  where
    rom = mconcat
            [ toRam prelude
            , toRam envvars
            , toRam $ replicate' (loadSegment ^. paragraph - length prelude - length envvars - measure psp ^. from byte - 16) $ error "dos internals 2"
            ]
    rom2 = mconcat
        [ rom
        , memAllocated $ mconcat
            [ psp
            , toRom $ relocate relocationTable loadSegment $ BS.drop headerSize gameExe
            , memUndefined' $ additionalMemoryAllocated ^. paragraph . byte
            ]
        ]

    psp = programSegmentPrefix (length prelude ^. from paragraph) endseg ""

    inter (i, (hi, lo)) = do
        heap16 (4*i ^. byte) .= "interrupt lo" @: lo
        heap16 (4*i ^. byte + 16) .= "interrupt hi" @: hi

    reladd = loadSegment ^. paragraph

    pspSegment = loadSegment - (pspSize ^. from paragraph)
    endseg = loadSegment + executableSize ^. from paragraph + additionalMemoryAllocated

    additionalMemoryAllocated = additionalMemoryNeeded
        -- could be anything between additionalMemoryNeeded and maxAdditionalMemoryNeeded

    (0x5a4d: bytesInLastPage: pagesInExecutable: relocationEntries:
     paragraphsInHeader: additionalMemoryNeeded: maxAdditionalMemoryNeeded: ssInit:
     spInit: checksum: ipInit: csInit:
     firstRelocationItemOffset: overlayNumber: headerLeft)
        = map (\[low, high] -> (high, low) ^. combine) $ everyNth 2 $ BS.unpack $ gameExe

    headerSize = paragraphsInHeader ^. paragraph
    executableSize = (fromIntegral pagesInExecutable `shiftL` 9)
            + (if (bytesInLastPage > 0) then fromIntegral bytesInLastPage - 0x200 else 0)
            - 0x22f0  -- ???
            :: Int

    relocationTable = sort $ take (fromIntegral relocationEntries)
        $ map (\[a,b]-> segAddr b a ^. from byte) $ everyNth 2 $ drop (fromIntegral firstRelocationItemOffset `div` 2 - 14) headerLeft

relocate :: [Int] -> Word16 -> BS.ByteString -> BS.ByteString
relocate table loc exe = BS.concat $ fst: map add (bss ++ [last])
  where
    (last, fst: bss) = mapAccumL (flip go) exe $ zipWith (-) table $ 0: table

    go r (BS.splitAt r -> (xs, ys)) = (ys, xs)

    add (BS.uncons -> Just (x, BS.uncons -> Just (y, xs))) = BS.cons x' $ BS.cons y' xs
        where (y',x') = combine %~ (+ loc) $ (y,x)

