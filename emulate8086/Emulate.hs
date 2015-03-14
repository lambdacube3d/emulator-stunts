{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
module Emulate where

import Numeric
import Numeric.Lens
import Data.Function
import Data.Word
import Data.Int
import Data.Bits hiding (bit)
import qualified Data.Bits as Bits
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Typeable
--import qualified Data.FingerTree as F
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Sequence as S
import qualified Data.Set as Set
import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as V
import qualified Data.Vector.Storable as US
import qualified Data.Vector.Storable.Mutable as U
import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Control.Lens as Lens
import Control.Concurrent
import Control.Exception (evaluate)
import System.Directory
import System.FilePath (takeFileName)
import "Glob" System.FilePath.Glob
--import Data.IORef
import Sound.ALUT (play, stop, sourceGain, pitch, ($=))

import Unsafe.Coerce
import Debug.Trace

import Hdis86 hiding (wordSize)
import Hdis86.Pure

import Helper
import Edsl hiding (Flags, trace_, ips, sps, segAddr_, addressOf, (>>), when, return, Info)
import qualified Edsl (addressOf, Part_(Flags))
import MachineState

---------------------------------------------- memory allocation

takeEvery n [] = []
takeEvery n xs = take n xs: takeEvery n (drop n xs)

allocateMem :: Int -> MemPiece -> (Int, MemPiece)
allocateMem req' (alloc, end) = (r + 16, (alloc ++ [(r, r + req' + 16)], end))
  where
    r = bitAlign 4 $ snd $ last alloc

modifyAllocated :: Int -> Int -> MemPiece -> Either Int MemPiece
modifyAllocated addr req (alloc, endf) = head $ concatMap f $ getOut $ zip alloc $ tail $ map fst alloc ++ [endf]
  where
    getOut xs = zip (inits xs) (tails xs)

    f (ys, ((beg,end),max): xs) | beg == addr - 16
        = [ if req > max - beg - 16
            then Left $ max - beg - 16
            else Right (map fst ys ++ (beg, beg + req + 16): map fst xs, endf)
          ]
    f _ = []

--------------------------------------

(@:) :: (WordX a) => BS.ByteString -> a ->  a
b @: x = x
infix 5 @:

haltWith = error
halt = error "CleanHalt"

ax = regs . ax_
bx = regs . bx_
cx = regs . cx_
dx = regs . dx_
si = regs . si_
di = regs . di_
cs = regs . cs_
ss = regs . ss_
ds = regs . ds_
es = regs . es_
ip = regs . ip_
sp = regs . sp_
bp = regs . bp_

uRead :: MachineState -> Int -> IO Word8
uRead h i = do
    when (h ^. config . showReads') $ do
        let off = h ^. config . showOffset
        let j = i - off
        when (0 <= j && j < 320 * 200) $ do
            let v = h ^. config . showBuffer
            x <- U.unsafeRead v j
            U.unsafeWrite v j $ x .|. 0x0000ff00
    fromIntegral <$> U.unsafeRead (h ^. heap'') i

uWrite :: Int -> Word8 -> Machine ()
uWrite i v = do
    h <- use heap''
    x <- liftIO $ U.unsafeRead h i
    liftIO $ U.unsafeWrite h i $ (x .&. 0xff00) .|. fromIntegral v
    b <- use $ config . showReads
    when b $ do
        off <- use $ config . showOffset
        let j = i - off
        when (0 <= j && j < 320 * 200) $ do
            v <- use $ config . showBuffer
            liftIO $ do
                x <- U.unsafeRead v j
                U.unsafeWrite v j $ x .|. 0x00ff0000
    let info = x `shiftR` 8
        n = info
    when (info /= 0) $ do
        trace_ $ "invalid cache at " ++ showHex' 5 i
        trace_ $ "#" ++ show info
        adjustCache
        ch <- use cache
        let 
            f :: Word16 -> Cache -> Cache -> Machine ()
            f 0 ch _ = cache .= ch
            f n ch ch' = case IM.findMax ch' of
                (i', Compiled _ _ e _) | i `inRegions` e -> do
                    zipWithM_ (uModInfo h) (regionsToList e) $ repeat (+(-1))
                    f (n-1) (at i' .~ Just (DontCache 0) $ ch) (IM.delete i' ch')
                (i', _) -> f n ch (IM.delete i' ch')
        f n ch $ fst $ IM.split (i+1) ch

uModInfo :: UVec -> Int -> (Word8 -> Word8) -> Machine ()
uModInfo h i f = liftIO $ do
    x <- U.unsafeRead h i
    U.unsafeWrite h i $ high %~ f $ x

bytesAt__ :: Int -> Int -> MachinePart' [Word8]
bytesAt__ i' j' = (get_, set)
  where
    set ws = zipWithM_ uWrite [i'..]
        $ (pad (error "pad") j' . take j') ws
    get_ = get >>= \h -> liftIO $ mapM (uRead h) [i'..i'+j'-1]

byteAt__ :: Int -> Machine Word8
byteAt__ i = get >>= \h -> liftIO $ uRead h i

getByteAt i = view _2 >>= \h -> liftIO $ uRead h i

setByteAt :: Int -> Word8 -> Machine ()
setByteAt i v = uWrite i v

wordAt__ :: Int -> Machine Word16
wordAt__ i = get >>= \h -> liftIO $ liftM2 (\hi lo -> fromIntegral hi `shiftL` 8 .|. fromIntegral lo) (uRead h (i+1)) (uRead h i)

getWordAt i = view _2 >>= \h -> liftIO $ liftM2 (\hi lo -> fromIntegral hi `shiftL` 8 .|. fromIntegral lo) (uRead h (i+1)) (uRead h i)

setWordAt :: Int -> Word16 -> Machine ()
setWordAt i v = uWrite i (fromIntegral v) >> uWrite (i+1) (fromIntegral $ v `shiftR` 8)

dwordAt__ :: Int -> MachinePart' Word32
dwordAt__ i = ( liftM2 (\hi lo -> fromIntegral hi `shiftL` 16 .|. fromIntegral lo) (wordAt__ $ i+2) (wordAt__ i)
             , \v -> setWordAt (i) (fromIntegral v) >> setWordAt (i+2) (fromIntegral $ v `shiftR` 16))


flags :: MachinePart Word16
flags = flags_ . iso id wordToFlags

getSender = do
    v <- use $ config . interruptRequest
    return $ \r -> modifyMVar_ v $ return . (++ [r])

setCounter = do
    config . counter %= (+1)
    c <- use $ config . counter
    v <- use $ config . instPerSec
    send <- getSender
    liftIO $ void $ forkIO $ do
        threadDelay $ round $ 1000000 / v
        send $ AskTimerInterrupt c

-- TODO
getRetrace = do
    x <- head <$> use retrace
    retrace %= tail
    return x


trace_ :: String -> Machine ()
trace_ s = liftIO $ putStr $ " | " ++ s

[overflowF,directionF,interruptF,signF,zeroF,adjustF,parityF,carryF] =
    [ flags_ . lens (`testBit` i) (\x b -> if b then setBit x i else clearBit x i) :: MachinePart (Bool)
    | i <- [11,10,9,7,6,4,2,0]
    ]

al = ax . low :: MachinePart Word8
ah = ax . high:: MachinePart Word8
dl = dx . low :: MachinePart Word8
dh = dx . high:: MachinePart Word8
bl = bx . low :: MachinePart Word8
bh = bx . high:: MachinePart Word8
cl = cx . low :: MachinePart Word8
ch = cx . high:: MachinePart Word8

----------------------

ifff "" = []
ifff x = [x]

addressOf a b = evalExp' $ Edsl.addressOf a b

cacheFile = "dontcache.txt"

adjustCache = do
    ch <- use cache
    let p (DontCache _) = True
        p _ = False
    liftIO $ do
        cf <- read <$> readFile cacheFile
        evaluate $ length cf
        writeFile cacheFile $ show $ merge cf $ map fst $ filter (p . snd) $ IM.toList ch

merge (x:xs) (y:ys) = case compare x y of
    EQ  -> x: merge xs ys
    GT  -> y: merge (x:xs) ys
    LT  -> x: merge xs (y:ys)
merge xs ys = xs ++ ys

regionsToList :: Regions -> [Int]
regionsToList = concatMap $ \(a, b) -> [a..b-1]

inRegions :: Int -> Regions -> Bool
inRegions i = any $ \(a, b) -> a <= i && i < b

getFetcher :: Machine (Int -> Metadata)
getFetcher = do
    h <- use heap''
    v <- liftIO $ US.unsafeFreeze h
    return $ head . disassembleMetadata disasmConfig . BS.pack . map fromIntegral . US.toList . (\ips -> US.slice ips maxInstLength v)

fetchBlock :: Machine CacheEntry
fetchBlock = do
    (n, r, e) <- liftM3 fetchBlock_ getFetcher (use cs) (use ip)
    return $ Compiled 0 n r $ do
        evalExpM e
        b <- use $ config . showReads
        when b $ do
            v <- use $ config . showBuffer
            off <- use $ config . showOffset
            liftIO $ forM_ r $ \(beg, end) -> forM_ [max 0 $ beg - off .. min (320 * 200 - 1) $ end - 1 - off] $ \i -> do
                x <- U.unsafeRead v i
                U.unsafeWrite v i $ x .|. 0xff000000

mkStep :: Machine Int
mkStep = do
    ip_ <- use ip
    cs_ <- use cs

    let ips = segAddr cs_ ip_
    cv <- use $ cache . at ips
    case cv of
     Just v -> case v of
      Compiled _ n len m -> do
--        let n' = n + 1
 --       cache . _1 . at ips .= (n' `seq` Just (n', len, m))
        m
        return n
      BuiltIn m -> do
        m
        return 1
      DontCache _ -> do
        Compiled _ n _ ch <- fetchBlock
        ch
        return n
     Nothing -> do
        entry@(Compiled _ n reg ch) <- fetchBlock
        h <- use heap''
        zipWithM_ (uModInfo h) (regionsToList reg) $ map (+) [1,1..]
        when (cacheOK ips) $ cache %= IM.insert ips entry
        ch
        return n

-- ad-hoc hacking for stunts!
cacheOK ips = ips < 0x39000 || isp >= 0x3a700

maxInstLength = 7

disasmConfig = Config Intel Mode16 SyntaxIntel 0

type MachinePart' a = (Machine a, a -> Machine ())

evalPart_ :: Part_ e a -> MachinePart a
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
    Low x -> evalPart_ x . low
    High x -> evalPart_ x . high
    CF -> carryF
    PF -> parityF
    AF -> adjustF
    ZF -> zeroF
    SF -> signF
    IF -> interruptF
    DF -> directionF
    OF -> overflowF
    Edsl.Flags -> flags
    DXAX -> uComb dx ax . combine


data List a = Con a (List a) | Nil

data Var :: List * -> * -> * where
    VarZ :: Var (Con a e) a
    VarS :: Var e a -> Var (Con b e) a

data EExp :: List * -> * -> * where
    Var' :: Var e a -> EExp e a

    C' :: a -> EExp e a
    Let' :: EExp e a -> EExp (Con a e) b -> EExp e b
    Iterate' :: EExp e Int -> EExp (Con a e) a -> EExp e a -> EExp e a

    Tuple' :: EExp e a -> EExp e b -> EExp e (a, b)
    Fst' :: EExp e (a, b) -> EExp e a
    Snd' :: EExp e (a, b) -> EExp e b
    If' :: EExp e Bool -> EExp e a -> EExp e a -> EExp e a

    Get' :: Part_ (EExp e) a -> EExp e a

    Eq' :: Eq a => EExp e a -> EExp e a -> EExp e Bool
    Sub', Add', Mul' :: Num a => EExp e a -> EExp e a -> EExp e a
    And', Or', Xor' :: Bits a => EExp e a -> EExp e a -> EExp e a
    Not', ShiftL', ShiftR', RotateL', RotateR' :: Bits a => EExp e a -> EExp e a
    Bit' :: Bits a => Int -> EExp e a -> EExp e Bool
    SetBit' :: Bits a => Int -> EExp e Bool -> EExp e a -> EExp e a
    HighBit' :: FiniteBits a => EExp e a -> EExp e Bool
    SetHighBit' :: FiniteBits a => EExp e Bool -> EExp e a -> EExp e a
    EvenParity' :: EExp e Word8 -> EExp e Bool

    Signed' :: AsSigned a => EExp e a -> EExp e (Signed a)
    Extend' :: Extend a => EExp e a -> EExp e (X2 a)
    Convert' :: (Integral a, Num b) => EExp e a -> EExp e b
    SegAddr' :: Part_ (EExp e) Word16 -> EExp e Word16 -> EExp e Int

data EExpM :: List * -> * -> * where
    LetM' :: EExp e a -> EExpM (Con a e) b -> EExpM e b
    QuotRem' :: Integral a => EExp e a -> EExp e a -> EExpM e b -> EExpM (Con (a,a) e) b -> EExpM e b
    Input' :: EExp e Word16 -> EExpM (Con Word16 e) () -> EExpM e ()

    Seq' :: EExpM e b -> EExpM e c -> EExpM e c
    IfM' :: EExp e Bool -> EExpM e a -> EExpM e a -> EExpM e a
    Replicate' :: EExp e Int -> EExpM e () -> EExpM e ()
    Cyc2' :: EExp e Bool -> EExp e Bool -> EExpM e () -> EExpM e ()

    Nop' :: EExpM e ()
    Trace' :: String -> EExpM e ()
    Set' :: Part_ (EExp e) a -> EExp e a -> EExpM e ()
    Output' :: EExp e Word16 -> EExp e Word16 -> EExpM e ()

data Env :: List * -> * where
  Empty :: Env Nil
  Push  :: { getPushEnv :: Env env, getPushVal :: t } -> Env (Con t env)

prj :: Var env t -> Env env -> t
prj VarZ = getPushVal
prj (VarS ix) = prj ix . getPushEnv

data Layout :: List * -> List * -> * where
  EmptyLayout :: Layout env Nil
  PushLayout  :: {-Typeable t 
              => -}Layout env env' -> Var env t -> Layout env (Con t env')

size :: Layout env env' -> Int
size EmptyLayout        = 0
size (PushLayout lyt _) = size lyt + 1

inc :: Layout env env' -> Layout (Con t env) env'
inc EmptyLayout         = EmptyLayout
inc (PushLayout lyt ix) = PushLayout (inc lyt) (VarS ix)

prjIx :: Int -> Layout env env' -> Var env t
prjIx _ EmptyLayout       = error "Convert.prjIx: internal error"
prjIx 0 (PushLayout _ ix) = unsafeCoerce ix --fromJust (gcast ix)
                              -- can't go wrong unless the library is wrong!
prjIx n (PushLayout l _)  = prjIx (n - 1) l

interrupt'' n = flip runReaderT (Push Empty n) $ evalEExpM int
   where
    int :: EExpM (Con Word8 Nil) ()
    int = case convExpM $ LetM (C (0 :: Word8)) interrupt of
        LetM' _ i -> unsafeCoerce i

convExp :: Exp a -> EExp Nil a
convExp = convExp_ EmptyLayout

convExp_ :: forall a e . Layout e e -> Exp a -> EExp e a
convExp_ lyt = g where
      h :: forall a e . Layout e e -> Exp a -> EExp e a
      h = convExp_

      g :: forall a . Exp a -> EExp e a
      g = \case
        Var sz -> Var' (prjIx (size lyt - sz - 1) lyt)

        C a -> C' a
        Let e f -> Let' (g e) $ h (inc lyt `PushLayout` VarZ) $ f $ Var (size lyt)
        Iterate n f e -> Iterate' (g n) (h (inc lyt `PushLayout` VarZ) $ f $ Var (size lyt)) (g e)

        Tuple a b -> Tuple' (g a) (g b)
        Fst a -> Fst' $ g a
        Snd a -> Snd' $ g a
        If a b c -> If' (g a) (g b) (g c)

        Get p -> Get' (convPart lyt p)

        Eq a b -> Eq' (g a) (g b)
        Sub a b -> Sub' (g a) (g b)
        Add a b -> Add' (g a) (g b)
        Mul a b -> Mul' (g a) (g b)
        And a b -> And' (g a) (g b)
        Or a b -> Or' (g a) (g b)
        Xor a b -> Xor' (g a) (g b)
        SetBit i a b -> SetBit' i (g a) (g b)
        SetHighBit a b -> SetHighBit' (g a) (g b)
        SegAddr a b -> SegAddr' (convPart lyt a) (g b)
        Not a -> Not' (g a)
        ShiftL a -> ShiftL' (g a)
        ShiftR a -> ShiftR' (g a)
        RotateL a -> RotateL' (g a)
        RotateR a -> RotateR' (g a)
        Bit i a -> Bit' i (g a)
        HighBit a -> HighBit' (g a)
        EvenParity a -> EvenParity' (g a)
        Signed a -> Signed' (g a)
        Extend a -> Extend' (g a)
        Convert a -> Convert' (g a)

convExpM :: ExpM a -> EExpM Nil a
convExpM = f EmptyLayout where
    h :: forall a e . Layout e e -> Exp a -> EExp e a
    h = convExp_

    f :: forall e a . Layout e e -> ExpM a -> EExpM e a
    f lyt = k where
      q :: forall a . Exp a -> EExp e a
      q = h lyt

      k :: forall a . ExpM a -> EExpM e a
      k = \case
        LetM e g -> LetM' (q e) $ f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)
        QuotRem a b x g -> QuotRem' (q a) (q b) (k x) $ f (inc lyt `PushLayout` VarZ) $ g $ unTup $ Var (size lyt)
        Input e g -> Input' (q e) $ f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)

        Seq a b -> Seq' (k a) (k b)
        IfM a b c -> IfM' (q a) (k b) (k c)
        Replicate n a -> Replicate' (q n) (k a)
        Cyc2 e f a -> Cyc2' (q e) (q f) (k a)
        Nop -> Nop'
        Trace s -> Trace' s
        Set p e -> Set' (convPart lyt p) (q e)
        Output a b -> Output' (q a) (q b)

convPart :: Layout e e -> Part_ Exp a -> Part_ (EExp e) a
convPart lyt = mapPart (convExp_ lyt)

type Machine' e = ReaderT (Env e) Machine

iterateM 0 _ a = return a
iterateM n f a = f a >>= iterateM (n-1) f

iff x y True = x
iff x y _ = y

evalExp' :: Exp a -> Machine a
evalExp' e = flip runReaderT Empty $ evalExp (convExp e)

evalExp :: EExp e a -> Machine' e a
evalExp x = ReaderT $ \e -> get >>= \st -> liftIO $ runReaderT (evalExp_ x) (e, st)

type Machine'' e = ReaderT (Env e, MachineState) IO

pushVal' :: Machine'' (Con b e) a -> b -> Machine'' e a
pushVal' m v = ReaderT $ \(e, x) -> runReaderT m (e `Push` v, x)

evalExp_ :: EExp e a -> Machine'' e a
evalExp_ = evalExp where
  evalExp :: EExp e a -> Machine'' e a
  evalExp = \case
    Var' ix -> reader $ prj ix . fst
    Let' e f -> evalExp e >>= pushVal' (evalExp f)
    Iterate' n f a -> evalExp n >>= \i -> evalExp a >>= iterateM i (pushVal' (evalExp f))

    C' a -> return a
    Get' p -> case p of
        Heap16 e -> evalExp e >>= getWordAt
        Heap8 e -> evalExp e >>= getByteAt
        p -> view $ _2 . evalPart_ p

    If' b x y -> evalExp b >>= iff (evalExp x) (evalExp y)
    Eq' x y -> liftM2 (==) (evalExp x) (evalExp y)

    Not' a -> complement <$> evalExp a
    ShiftL' a -> (`shiftL` 1) <$> evalExp a
    ShiftR' a -> (`shiftR` 1) <$> evalExp a
    RotateL' a -> (`rotateL` 1) <$> evalExp a
    RotateR' a -> (`rotateR` 1) <$> evalExp a
    Sub' a b -> liftM2 (-) (evalExp a) (evalExp b)
    Add' a b -> liftM2 (+) (evalExp a) (evalExp b)
    Mul' a b -> liftM2 (*) (evalExp a) (evalExp b)
    And' a b -> liftM2 (.&.) (evalExp a) (evalExp b)
    Or'  a b -> liftM2 (.|.) (evalExp a) (evalExp b)
    Xor' a b -> liftM2 xor (evalExp a) (evalExp b)

    Bit' i e -> (`testBit` i) <$> evalExp e
    SetBit' i e f -> liftM2 (bit i .~) (evalExp e) (evalExp f)
    HighBit' e -> (^. highBit) <$> evalExp e
    SetHighBit' e f -> liftM2 (highBit .~) (evalExp e) (evalExp f)
    EvenParity' e -> even . popCount <$> evalExp e

    Signed' e -> asSigned <$> evalExp e    
    Extend' e -> extend <$> evalExp e    
    SegAddr' e f -> liftM2 segAddr (view $ _2 . evalPart_ e) (evalExp f)
    Convert' e -> fromIntegral <$> evalExp e    

    Tuple' a b -> liftM2 (,) (evalExp a) (evalExp b)
    Fst' p -> fst <$> evalExp p
    Snd' p -> snd <$> evalExp p

evalEExpM :: EExpM e a -> Machine' e a
evalEExpM = evalExpM where

  evalExpM :: EExpM e a -> Machine' e a
  evalExpM = \case
    LetM' e f -> evalExp e >>= pushVal (evalEExpM f)
    Seq' a b -> evalExpM a >> evalExpM b
    Set' p e' -> case p of 
        Heap16 e -> join $ lift <$> liftM2 setWordAt (evalExp e) (evalExp e')
        Heap8 e -> join $ lift <$> liftM2 setByteAt (evalExp e) (evalExp e')
        p -> evalExp e' >>= (evalPart_ p .=)
    Nop' -> return ()

    IfM' b x y -> evalExp b >>= iff (evalExpM x) (evalExpM y)

    Input' a f -> evalExp a >>= lift . input >>= pushVal (evalEExpM f)
    QuotRem' a b c f -> do
        x <- evalExp a
        y <- evalExp b
        case quotRemSafe x y of
            Nothing -> evalExpM c
            Just (z,v) -> pushVal (evalEExpM f) (z, v)


    Replicate' n e -> join $ liftM2 replicateM_ (evalExp n) (return $ evalExpM e)
    Cyc2' a b e -> cyc2 (evalExp a) (evalExp b) (evalExpM e)

    Output' a b -> join $ lift <$> liftM2 output' (evalExp a) (evalExp b)

    Trace' a -> lift $ trace_ a

cyc2 a b m = do
    x <- a
    when x $ do
        m
        y <- b
        when y $ cyc2 a b m

pushVal :: Machine' (Con b e) a -> b -> Machine' e a
pushVal m v = ReaderT $ runReaderT m . (`Push` v)

evalExpM :: ExpM a -> Machine a
evalExpM e = flip runReaderT Empty $ evalEExpM (convExpM e)

checkInt n = do
  ns <- use $ config . stepsCounter
  let !ns' = ns + n
  config . stepsCounter .= ns'
  let ma = complement 0x3ff
  when (ns' .&. ma /= ns .&. ma) $ do
    i <- use interruptF
    when i $ do
        mask <- use intMask
        ivar <- use $ config . interruptRequest
        ints <- liftIO $ takeMVar ivar
        let ibit = \case
                AskTimerInterrupt{} -> 0
                AskKeyInterrupt{}   -> 1
            (now, later) = partition (not . testBit mask . ibit) ints
        liftIO $ putMVar ivar later
        forM_ now $ \case
           AskTimerInterrupt id -> do
              cc <- use $ config . counter
              when (id == cc) $ interrupt'' 0x08
           AskKeyInterrupt scancode -> do
              config . keyDown .= scancode
              interrupt'' 0x09

{-
       PrintFreqTable wait -> do
        (c1, c2) <- use cache
        let f (k, (x, y)) = showHex' 5 k ++ "   " ++ pad ' ' 20 (maybe "" (\(a,b,_)->pad ' ' 10 (show a) ++ pad ' ' 10 (show $ b - k + 1)) x) ++ pad ' ' 10 (maybe "" show y)
        let t = unlines $ map f $ sortBy (compare `on` (fmap (\(a,_,_)->a) . fst . snd)) $
                  IM.toList $ IM.unionWith (\(a,b) (c,d) -> (maybe a Just c, maybe b Just d))
                    (IM.map (\x -> (Just x, Nothing)) c1) (IM.map (\x -> (Nothing, Just x)) c2)
        liftIO $ do
--            writeFile "freqTable.txt" t
--            putStrLn t
--            threadDelay 1000000
            putMVar wait ()
-}



input :: Word16 -> Machine (Word16)
input v = do
    case v of
        0x21 -> do
            x <- use intMask
            trace_ $ "get interrupt mask " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x60 -> do
            k <- use $ config . keyDown
            trace_ $ "keyboard scan code: " ++ showHex' 4 k
            return $ "???" @: k
        0x61 -> do
            x <- use $ config . speaker
            when ((x .&. 0xfc) /= 0x30) $ trace_ $ "speaker -> " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x03da -> do
            r <- getRetrace
            trace_ $ "VGA hardware " ++ showHex' 4 r
            return $ "Vretrace | DD" @: r
        _ -> haltWith $ "input #" ++ showHex' 4 v

output' :: Word16 -> Word16 -> Machine ()
output' v x = do
    case v of
        0x20 -> do
--            trace_ $ "int resume " ++ showHex' 2 x  -- ?
            case x of
              0x20 -> setCounter
--              v -> trace_ "int resume " ++ show
        0x21 -> do
            trace_ $ "set interrupt mask " ++ showHex' 2 x  -- ?
            intMask .= fromIntegral x
            when (not $ testBit x 0) setCounter
        0x40 -> do
            trace_ $ "set timer frequency " ++ showHex' 2 x --show (1193182 / fromIntegral x) ++ " HZ"
        0x41 -> do
            trace_ $ "ch #41 " ++ showHex' 2 x  -- ?
        0x42 -> do
--            trace_ $ "ch #42 " ++ showHex' 2 x
            config . frequency %= (.|. (x `shiftL` 8)) . (`shiftR` 8)
            f <- use $ config . frequency
            source <- use $ config . soundSource
            liftIO $ when (fromIntegral f >= 128) $ pitch source $= 2711 / fromIntegral f
        0x43 -> do
            trace_ $ "set timer control " ++ showHex' 2 x
            case x of
                0x36  -> trace_ "set timer frequency lsb+msb, square wave"
                0xb6  -> trace_ "set speaker frequency lsb+msb, square wave"
        0x61 -> do
            x' <- use $ config . speaker
            source <- use $ config . soundSource
            config . speaker .= fromIntegral x
            when (x .&. 0xfc /= 0x30) $ trace_ $ "speaker <- " ++ showHex' 2 x
            liftIO $ do
                when (testBit x 0 /= testBit x' 0) $ sourceGain source $= if testBit x 0 then 0.1 else 0
                when (testBit x 1 /= testBit x' 1) $ (if testBit x 1 then play else stop) [source]
        0xf100 -> do
            trace_ "implemented for jmpmov test"
        _ -> haltWith $ "output #" ++ showHex' 4 v ++ " 0x" ++ showHex' 4 x

--------------------------------------------------------

imMax m | IM.null m = 0
        | otherwise = succ . fst . IM.findMax $ m

origInterrupt :: M.Map (Word16, Word16) (Word8, Machine ())
origInterrupt = M.fromList

  [ item 0x00 (0xf000,0x1060) $ do
    trace_ "divison by zero interrupt"
    haltWith $ "int 00"

  , item 0x08 (0xf000,0xfea5) $ do
--    trace_ "orig timer"
    output' 0x20 0x20

  , item 0x09 (0xf000,0xe987) $ do
    trace_ "orig keyboard interrupt"
    haltWith $ "int 09"

  , item 0x10 (0xf000,0x1320) $ do
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
                _ -> haltWith $ "#" ++ showHex' 2 video_mode_number
        0x0b -> do
            trace_ "Select Graphics Palette or Text Border Color"
        0x0e -> do
            a <- use al
            liftIO $ putChar $ chr . fromIntegral $ a
            trace_ $ "Write Character as TTY: " ++ showHex' 2 a
            
--            traceM $ (:[]) . chr . fromIntegral $ a
        0x0f -> do
            trace_ "Get Current Video Mode"
            al .= "text mode" @: 3
            ah .= "width of screen, in character columns" @: 80
            bh .= "current active video page (0-based)" @: 0x00 --b8
        0x10 -> do
            trace_ "Set/Get Palette Registers (EGA/VGA)"
            f <- use al
            case f of
              0x12 -> do
                trace_ "set block of DAC color registers"
                first_DAC_register <- use bx -- (0-00ffH)
                number_of_registers <- use cx -- (0-00ffH)
                -- ES:DX addr of a table of R,G,B values (it will be CX*3 bytes long)
                addr <- addressOf (Just ES) $ memIndex RDX
                colors <- fst $ bytesAt__ addr $ 3 * fromIntegral number_of_registers
                config . palette %= \cs -> cs V.//
                    zip [fromIntegral first_DAC_register .. fromIntegral (first_DAC_register + number_of_registers - 1)]
                        -- shift 2 more positions because there are 64 intesity levels
                        [ fromIntegral r `shiftL` 26 .|. fromIntegral g `shiftL` 18 .|. fromIntegral b `shiftL` 10
                        | [r, g, b] <- takeEvery 3 $ colors]

              v -> haltWith $ "interrupt #10,#10,#" ++ showHex' 2 f

        v  -> haltWith $ "interrupt #10,#" ++ showHex' 2 v

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
            returnOK
      v  -> haltWith $ "interrupt #15,#" ++ showHex' 2 v

  , item 0x16 (0xf000,0x1200) $ do
    trace_ "Keyboard Services"
    v <- use ah
    case v of
        0x00 -> do
            trace_ "Read (Wait for) Next Keystroke"
            ah .= "Esc scan code" @: 0x39
            al .= "Esc ASCII code" @: 0x1b
        0x01 -> do
            trace_ "Query Keyboard Status / Preview Key"
            zeroF .= False  -- no keys in buffer
        v  -> haltWith $ "interrupt #16,#" ++ showHex' 2 v

  , item 0x20 (0x0000, 0x0000) $ do
    trace_ "interrupt halt"
    halt

  , item 0x21 (0xf000,0x14c0) $ do
    trace_ "DOS rutine"
    v <- use ah
    case v of
        0x00 -> do
            trace_ "dos Program terminate"
            halt

        0x1a -> do
            trace_ "Set Disk Transfer Address (DTA)"
            addr <- addressOf Nothing (memIndex RDX)
            dta .= addr

        0x25 -> do
            v <- fromIntegral <$> use al     -- interrupt vector number
            trace_ $ "Set Interrupt Vector " ++ showHex' 2 v
            use dx >>= setWordAt (4*v)     -- DS:DX = pointer to interrupt handler
            use ds >>= setWordAt (4*v + 2)

        0x30 -> do
            trace_ "Get DOS version"
            al .= "major version number" @: 0x05      --  (2-5)
            ah .= "minor version number" @: 0x00      --  (in hundredths decimal)
            bh .= "MS-DOS" @: 0xff
            do              -- 24 bit OEM serial number
                bl .= "OEM serial number (high bits)" @: 0
                cx .= "OEM serial number (low bits)" @: 0

        0x35 -> do
            v <- fromIntegral <$> use al
            trace_ $ "Get Interrupt Vector " ++ showHex' 2 v
            wordAt__ (4*v) >>= (bx .=)
            wordAt__ (4*v + 2) >>= (es .=)   -- ES:BX = pointer to interrupt handler

        0x3c -> do
            trace_ "Create File"
            (f, fn) <- getFileName
            attributes <- use cx
            b <- liftIO $ doesFileExist fn
            if b then dosFail 0x05 -- access denied
              else do
                liftIO $ writeFile fn ""
                newHandle fn
        0x3d -> do
            trace_ "Open File Using Handle"
            open_access_mode <- use al
            case open_access_mode of
              0 -> do   -- read mode
                (f,fn) <- getFileName
                checkExists fn $ newHandle fn

        0x3e -> do
            trace_ "Close file"
            handle <- fromIntegral <$> use bx
            trace_ $ "handle " ++ showHex' 4 handle
            x <- IM.lookup handle <$> use files
            case x of
              Just (fn, _) -> do
                trace_ $ "file: " ++ fn
                files %= IM.delete handle
                returnOK

        0x3f -> do
            handle <- fromIntegral <$> use bx
            (fn, seek) <- (IM.! handle) <$> use files
            num <- fromIntegral <$> use cx
            trace_ $ "Read " ++ showHex' 4 handle ++ ":" ++ fn ++ " " ++ showHex' 4 num
            loc <- addressOf Nothing $ memIndex RDX
            s <- liftIO $ BS.take num . BS.drop seek <$> BS.readFile fn
            let len = BS.length s
            files %= flip IM.adjust handle (\(fn, p) -> (fn, p+len))
            snd (bytesAt__ loc len) (BS.unpack s)
            ax .= "length" @: fromIntegral len
            returnOK

        0x40 -> do
            handle <- fromIntegral <$> use bx
            trace_ $ "Write to " ++ showHex' 4 handle
            num <- fromIntegral <$> use cx
            loc <- addressOf Nothing $ memIndex RDX
            case handle of
              1 -> trace_ . ("STDOUT: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              2 -> trace_ . ("STDERR: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              _ -> return ()
            returnOK

        0x41 -> do
            trace_ "Delete File"
            (f,fn) <- getFileName
            checkExists fn $ do
                liftIO $ removeFile fn
                returnOK

        0x42 -> do
            handle <- fromIntegral <$> use bx
            fn <- (^. _1) . (IM.! handle) <$> use files
            mode <- use al
            pos <- fromIntegral . asSigned <$> use (uComb cx dx . combine)
            trace_ $ "Seek " ++ showHex' 4 handle ++ ":" ++ fn ++ " to " ++ show mode ++ ":" ++ showHex' 8 pos
            s <- liftIO $ BS.readFile fn
            files %= (flip IM.adjust handle $ \(fn, p) -> case mode of
                0 -> (fn, pos)
                1 -> (fn, p + pos)
                2 -> (fn, BS.length s + pos)
                )
            pos' <- (^. _2) . (IM.! handle) <$> use files
            (uComb dx ax . combine) .= fromIntegral pos'
            returnOK

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
            returnOK

        0x48 -> do
            memory_paragraphs_requested <- use bx
            trace_ $ "Allocate Memory " ++ showHex' 5 (memory_paragraphs_requested ^. paragraph)
            x <- zoom heap $ state $ allocateMem (memory_paragraphs_requested ^. paragraph)
            ax .= "segment address of allocated memory block" @: (x ^. from paragraph) -- (MCB + 1para)
            returnOK

        0x4a -> do
            new_requested_block_size_in_paragraphs <- use bx
            trace_ $ "Modify allocated memory blocks to " ++ showHex' 4 new_requested_block_size_in_paragraphs
            segment_of_the_block <- use es      -- (MCB + 1para)
            h <- use heap
            case modifyAllocated (segment_of_the_block ^. paragraph) (new_requested_block_size_in_paragraphs ^. paragraph) h of
              Left x -> do
                bx .= "maximum block size possible" @: (x ^. from paragraph)
                trace_ $ "insufficient, max possible: " ++ showHex' 4 (x ^. from paragraph)
                dosFail 0x08 -- insufficient memory
              Right h -> do
                ds <- use ds
                ax .= ds  -- why???
                heap .= h
                returnOK

        0x4c -> do
            code <- use al
            trace_ $ "Terminate Process With Return Code #" ++ showHex' 2 code
            halt

        0x4e -> do
            trace_ $ "Find file"
            (f_,_) <- getFileName
            attribute_used_during_search <- use cx
            ad <- use dta
            s <- liftIO $ do
                    b <- globDir1 (compile $ map toUpper f_) "../original"
                    case b of
                        (f:_) -> Just . (,) f <$> BS.readFile f
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
                snd (bytesAt__ (ad + 0x02) 13 {- !!! -}) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f_) ++ [0])
                setByteAt (ad + 0x15) $ "attribute of matching file" @: fromIntegral attribute_used_during_search
                setWordAt (ad + 0x16) $ "file time" @: 0 -- TODO
                setWordAt (ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                setByteAt (ad + 0x00) 1
                ax .= 0 -- ?
                returnOK
              Nothing -> dosFail 0x02  -- File not found

        0x4f -> do
            ad <- use dta
            fname <- fst $ bytesAt__ (ad + 0x02) 13
            let f_ = map (chr . fromIntegral) $ takeWhile (/=0) fname
            trace_ $ "Find next matching file " ++ show f_
            n <- byteAt__ $ ad + 0x00
            s <- do
                    b <- liftIO $ globDir1 (compile $ map toUpper f_) "../original"
                    case drop (fromIntegral n) b of
                        filenames@(f:_) -> do
                            trace_ $ "alternatives: " ++ show filenames
                            Just . (,) f <$> liftIO (BS.readFile f)
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
                setWordAt (ad + 0x16) $ "file time" @: 0 -- TODO
                setWordAt (ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                setByteAt (ad + 0x00) $ n+1
                ax .= 0 -- ?
                returnOK
              Nothing -> dosFail 0x02

        0x62 -> do
            trace_ "Get PSP address (DOS 3.x)"
            bx .= "segment address of current process" @: 0x1fe  -- hack!!!  !!!
            returnOK

        _    -> haltWith $ "dos function #" ++ showHex' 2 v

  , item 0x24 (0x0118,0x0110) $ do     -- 24h
    trace_ "critical error handler interrupt"
    haltWith $ "int 24"

  , item 0x33 (0xc7ff,0x0010) $ do     -- 33h
--    trace_ "Mouse Services"
    v <- use ax
    case v of
        0x00 -> do
            trace_ "Mouse Reset/Get Mouse Installed Flag"
            ax .= {- "mouse?" @: 0xffff -} "mouse driver not installed" @: 0x0000
            bx .= "number of buttons" @: 0 -- 3
        0x03 -> do
--            trace_ "Get Mouse position and button status"
            cx .= "mouse X" @: 0
            dx .= "mouse Y" @: 0
            bx .= "button status" @: 0
        0x07 -> do
            trace_ "Set Mouse Horizontal Min/Max Position"
            minimum_horizontal_position <- use cx
            maximum_horizontal_position <- use dx
            return ()
        0x08 -> do
            trace_ "Set Mouse Vertical Min/Max Position"
            minimum_vertical_position <- use cx
            maximum_vertical_position <- use dx
            return ()
        0x0f -> do
            trace_ "Set Mouse Mickey Pixel Ratio"
        _    -> haltWith $ "Int 33h, #" ++ showHex' 2 v
  ]
  where 
    item :: Word8 -> (Word16, Word16) -> Machine () -> ((Word16, Word16), (Word8, Machine ()))
    item a k m = (k, (a, m >> iret'))
    iret' = evalExpM iret

    newHandle fn = do
        handle <- max 5 . imMax <$> use files
        files %= IM.insert handle (fn, 0)
        trace_ $ "handle " ++ showHex' 4 handle
        ax .= "file handle" @: fromIntegral handle
        returnOK

    getFileName = do
        addr <- addressOf Nothing $ memIndex RDX
        fname <- fst $ bytesAt__ addr 40
        let f = map (toUpper . chr . fromIntegral) $ takeWhile (/=0) fname
        trace_ f
        let fn = "../original/" ++ f
        return (f, fn)

    checkExists fn cont = do
        b <- liftIO $ doesFileExist fn
        if b then cont else dosFail 0x02

    returnOK = carryF .= False

    dosFail errcode = do
        trace_ $ showerr errcode
        ax .= errcode
        carryF .= True
      where
        showerr = \case
            0x01  -> "Invalid function number"
            0x02  -> "File not found"
            0x03  -> "Path not found"
            0x04  -> "Too many open files (no handles left)"
            0x05  -> "Access denied"
            0x06  -> "Invalid handle"
            0x07  -> "Memory control blocks destroyed"
            0x08  -> "Insufficient memory"
            0x09  -> "Invalid memory block address"
            0x0A  -> "Invalid environment"
            0x0B  -> "Invalid format"
            0x0C  -> "Invalid access mode (open mode is invalid)"

strip = reverse . dropWhile (==' ') . reverse . dropWhile (==' ')

----------------------------------------------

prelude1'
     = [error' $ "interruptTable " ++ showHex' 2 (i `div` 4) | i <- [0..1023]]
    ++ replicate 172 (error' "BIOS communication area")
    ++ replicate 68 (error' "reserved by IBM")
    ++ replicate 16 (error' "user communication area")
    ++ replicate 256 (error' "DOS communication area")
    ++ [error' $ "dos area " ++ showHex' 2 i | i <- [0x600 ..0x700-1]]
prelude'
     = prelude1'
    ++ [error' $ "dos area " ++ showHex' 2 i | i <- [length prelude1'..0x1f40-1]]

error' :: String -> Word8
error' _ = 0
memUndefined'' i = replicate i 0


type MemPiece' = IM.IntMap Word8

bytesAt_ :: Int -> Int -> Lens' MemPiece' [Word8]
bytesAt_ i' j' = lens get set
  where
    set s m = IM.unions [s1, (IM.fromList . zip [i' ..] . pad (error "pad") j' . take j') m, s2] where
        (s1, s') = IM.split i' s
        (_, s2) = IM.split (i' + j' - 1) s'
    get = IM.elems . fst . IM.split (i' + j') . snd . IM.split (i'-1)

byteAt_ :: Int -> Lens' (IM.IntMap Word8) Word8
byteAt_ i = lens (IM.! i') $ flip $ IM.insert i' where i' = i

wordAt_ :: Int -> Lens' (IM.IntMap Word8) Word16
wordAt_ i = uComb (byteAt_ (i + 1)) (byteAt_ i) . combine

dwordAt_ :: Int -> Lens' (IM.IntMap Word8) Word32
dwordAt_ i = uComb (wordAt_ (i + 2)) (wordAt_ i) . combine


programSegmentPrefix' :: Word16 -> Word16 -> BS.ByteString -> [Word8]
programSegmentPrefix' envseg endseg args = IM.elems $ flip execState (IM.fromList $ zip [0..] $ map (error' . ("psp uninitialized byte: " ++) . showHex' 2) [0..0xff] :: MemPiece') $ do

    wordAt_ 0x00 .= "CP/M exit, always contain code 'int 20h'" @: 0x20CD
    wordAt_ 0x02 .= "Segment of the first byte beyond the memory allocated to the program" @: endseg
--    bytesAt 0x05 5 .= [0xea, 0xff, 0xff, 0xad, 0xde]   -- FAR call to MSDOS function dispatcher (int 21h)?
--    dwordAt 0x0a .= 0xf00020c8    -- Terminate address of previous program (old INT 22h)
--    dwordAt 0x0e .= 0x01180000    -- Break address of previous program (old INT 23h)
--    dwordAt 0x12 .= 0x01180110    -- Critical error address of previous program (old INT 24h)
--    wordAt 0x16 .= 0x0118    -- Caller's PSP segment (usually COMMAND.COM - internal)

    -- Job File Table (JFT) (internal)
--    bytesAt 0x18 20 .= [0x01, 0x01, 0x01, 0x00, 0x02, 0x03] ++ repeat 0xff

    wordAt_ 0x2c .= "Environment segment" @: envseg
--    dwordAt 0x2e .= 0x0192ffe6 -- SS:SP on entry to last INT 21h call (internal)

--    wordAt 0x32 .= 0x0014 -- JFT size (internal)
--    dwordAt 0x34 .= 0x01920018-- Pointer to JFT (internal)
--    dwordAt 0x38 .= 0xffffffff -- Pointer to previous PSP (only used by SHARE in DOS 3.3 and later)
    -- 3Ch-3Fh     4 bytes     Reserved
--    wordAt 0x40 .= 0x0005 -- DOS version to return (DOS 4 and later, alterable via SETVER in DOS 5 and later)
    -- 42h-4Fh     14 bytes     Reserved
    bytesAt_ 0x50 3 .= [0xcd, 0x21, 0xcb] -- (code) Far call to DOS (always contain INT 21h + RETF)
    -- 53h-54h     2 bytes     Reserved
    -- 55h-5Bh     7 bytes     Reserved (can be used to make first FCB into an extended FCB)

    -- 5Ch-6Bh     16 bytes     Unopened Standard FCB 1
    -- 6Ch-7Fh     20 bytes     Unopened Standard FCB 2 (overwritten if FCB 1 is opened)
--    bytesAt 0x5c (16 + 20) .= repeat 0

    byteAt_ 0x80 .= "args length" @: fromIntegral (min maxlength $ BS.length args)
    bytesAt_ 0x81 (maxlength + 1) .= pad 0 (maxlength + 1) (take maxlength (BS.unpack args) ++ [0x0D])  -- Command line string
--    byteAt 0xff .= 0x36   -- dosbox specific?
  where
    maxlength = 125

pspSize = 256 :: Int

envvars :: [Word8]
envvars = map (fromIntegral . ord) "PATH=Z:\\\NULCOMSPEC=Z:\\COMMAND.COM\NULBLASTER=A220 I7 D1 H5 T6\0\0\1\0C:\\GAME.EXE" ++
 replicate 20 0

replicate' n _ | n < 0 = error "replicate'"
replicate' n x = replicate n x

loadExe :: Word16 -> BS.ByteString -> Machine ()
loadExe loadSegment gameExe = do
    heap .= ( [(length rom', length rom2')], 0xa0000 - 16)
    zipWithM_ setByteAt [0..] rom2'
    ss .=  (ssInit + loadSegment)
    sp .=  spInit
    cs .=  (csInit + loadSegment)
    ip .=  ipInit
    ds .=  pspSegment
    es .=  pspSegment
    cx .=  0x00ff -- why?
    dx .=  pspSegment -- why?
    bp .=  0x091c -- why?
    si .=  0x0012 -- why?
    di .=  0x1f40 -- why?
    labels .= mempty

    liftIO $ print $ showHex' 5 $ loadSegment ^. paragraph
    liftIO $ print $ showHex' 5 headerSize

    forM_ [(fromIntegral a, b, m) | (b, (a, m)) <- M.toList origInterrupt] $ \(i, (hi, lo), m) -> do
        setWordAt (4*i) $ "interrupt lo" @: lo
        setWordAt (4*i + 2) $ "interrupt hi" @: hi
        cache %= IM.insert (segAddr hi lo) (BuiltIn m)

    cf <- liftIO $ read <$> readFile cacheFile
    cache %= IM.union (IM.fromList $ zip cf $ repeat $ DontCache 0)

    setWordAt (0x410) $ "equipment word" @: 0xd426 --- 0x4463   --- ???
    setByteAt (0x417) $ "keyboard shift flag 1" @: 0x20
  where
    rom' = concat
            [ prelude'
            , envvars
            , replicate' (loadSegment ^. paragraph - length prelude' - length envvars - length psp' - 16) 0
            ]
    rom2' = concat
        [ rom'
        , concat
            [ replicate 16 0
            , psp'
            , BS.unpack $ relocate relocationTable loadSegment $ BS.drop headerSize gameExe
            , memUndefined'' $ additionalMemoryAllocated ^. paragraph
            ]
        ]

    psp' = programSegmentPrefix' (length prelude' ^. from paragraph) endseg ""

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
        $ map (\[a,b]-> segAddr b a) $ everyNth 2 $ drop (fromIntegral firstRelocationItemOffset `div` 2 - 14) headerLeft

relocate :: [Int] -> Word16 -> BS.ByteString -> BS.ByteString
relocate table loc exe = BS.concat $ fst: map add (bss ++ [last])
  where
    (last, fst: bss) = mapAccumL (flip go) exe $ zipWith (-) table $ 0: table

    go r (BS.splitAt r -> (xs, ys)) = (ys, xs)

    add (BS.uncons -> Just (x, BS.uncons -> Just (y, xs))) = BS.cons x' $ BS.cons y' xs
        where (y',x') = combine %~ (+ loc) $ (y,x)

