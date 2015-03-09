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
--import qualified Data.FingerTree as F
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Sequence as S
import qualified Data.Set as Set
import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as V
import qualified Data.Vector.Storable.Mutable as U
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
--import Data.IORef

import Debug.Trace

import Hdis86 hiding (wordSize)
import Hdis86.Incremental

import Helper
import Edsl hiding (Flags, trace_, ips, sps, segAddr_, addressOf, addressOf', (>>))
import qualified Edsl (addressOf, addressOf', Part(Flags))
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

haltWith = throwError . Err
halt = throwError CleanHalt

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

uRead :: UVec -> Int -> IO Word8
uRead h i = fromIntegral <$> U.read h i

uWrite, uWriteInfo :: UVec -> Int -> Word8 -> Machine ()
uWrite h i v = do
    x <- liftIO $ U.read h i
    liftIO $ U.write h i $ fromIntegral v
    let info = x `shiftR` 8
        n = info .&. 0x7f
    when (info /= 0) $ do
        liftIO $ putStr "#"
        when (n > 1) $ trace_ $ show info
        when (info == 0xff) $ error "system area written"
        ch <- use cache
        let (ch', beg, end) = f n ch i i $ fst $ IM.split (i+1) ch
            f :: Word16 -> Cache -> Int -> Int -> Cache -> (Cache, Int, Int)
            f 0 ch beg end _ = (ch, beg, end)
            f n ch beg end ch' = f (n-1) (IM.delete i' ch) (min beg i') (max end $ e) (IM.delete i' ch')
              where
                (i', (e,_)) = IM.findMax ch'
        zipWithM_ (uWriteInfo h) [beg..end] [0,0..]
        cache .= ch'
uWriteInfo h i v = liftIO $ do
    x <- U.read h i
    U.write h i $ high .~ v $ x
uModInfo :: UVec -> Int -> (Word8 -> Word8) -> Machine ()
uModInfo h i f = liftIO $ do
    x <- U.read h i
    U.write h i $ high %~ f $ x

bytesAt__ :: Int -> Int -> MachinePart' [Word8]
bytesAt__ i' j' = (get, set)
  where
    set ws = use heap'' >>= \h -> zipWithM_ (uWrite h) [i'..]
        $ (pad (error "pad") j' . take j') ws
    get = use heap'' >>= \h -> liftIO $ mapM (uRead h) [i'..i'+j'-1]

byteAt__ :: Int -> MachinePart' Word8
byteAt__ i = (use heap'' >>= \h -> liftIO $ uRead h i, \v -> use heap'' >>= \h -> uWrite h i v)

wordAt__ :: Int -> MachinePart' Word16
wordAt__ i = ( use heap'' >>= \h -> liftIO $ liftM2 (\hi lo -> fromIntegral hi `shiftL` 8 .|. fromIntegral lo) (uRead h (i+1)) (uRead h i)
             , \v -> use heap'' >>= \h -> uWrite h i (fromIntegral v) >> uWrite h (i+1) (fromIntegral $ v `shiftR` 8))

dwordAt__ :: Int -> MachinePart' Word32
dwordAt__ i = ( liftM2 (\hi lo -> fromIntegral hi `shiftL` 16 .|. fromIntegral lo) (fst $ wordAt__ $ i+2) (fst $ wordAt__ i)
             , \v -> snd (wordAt__ i) (fromIntegral v) >> snd (wordAt__ $ i+2) (fromIntegral $ v `shiftR` 16))


flags :: MachinePart Word16
flags = flags_ . iso id wordToFlags

setCounter = do
    trace_ "setCounter"
    v <- use $ config . instPerSec
    config . counter .= Just (v `div` 24)

-- TODO
getRetrace = do
    x <- head <$> use retrace
    retrace %= tail
    return x


trace_ :: String -> Machine ()
trace_ s = traceQ %= (s:)

steps = config . numOfDisasmLines

clearHist = do
    h <- use traceQ
    traceQ .= []
    return (intercalate "; " $ reverse h)

[overflowF,directionF,interruptF,signF,zeroF,adjustF,parityF,carryF] =
    [ flags_ . bit i  :: MachinePart (Bool)
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

segAddr_ :: MachinePart (Word16) -> Getter MachineState ( Word16) -> Getter MachineState (Int)
segAddr_ seg off = to $ \s -> segAddr (s ^. seg) (s ^. off)

ips = segAddr_ cs ip
sps = segAddr_ ss sp

----------------------

ifff "" = []
ifff x = [x]
{-
mkSteps :: MachineState -> (Halt, MachineState)
mkSteps s = either (\x -> (x, s')) (const $ either (\x -> (x, s')) (const $ mkSteps s') b) a
  where
    (ju, a, b, s') = mkStep $ hijack s
-}
addressOf a b = evalExp $ Edsl.addressOf a b
addressOf' a = evalExp $ Edsl.addressOf' a

askCounter n = do
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
            config . counter %= fmap (+(-n))
            return False
      (c:cc) -> do
        ns <- use $ config . stepsCounter
        if c <= ns then do
            config . counter' %= drop 1
            return True
          else do
            return False

verboseLevel' s
    = if s ^. disassStart == 0 then 3 else if s ^. stepsCounter >= s ^. disassStart then 2 else s ^. verboseLevel
    
showErr e = show e: []

immLens :: a -> Lens' b a
immLens c = lens (const c) $ \_ _ -> error "can't update immediate value"

showCode = catchError (forever mkStep) $ \case
    Interr -> showCode
    e -> do
        liftIO $ print e
        throwError e

mkStep :: Machine ()
mkStep = do
    ip_ <- use ip
    cs_ <- use cs
    let ips = segAddr cs_ ip_
    info <- readInfo ips
    case info of
      Builtin -> do
        case M.lookup (cs_, ip_) origInterrupt of
          Just (i, m) -> do
            m -- return $ Right ("interrupt " ++ showHex' 2 i ++ "h", m)
            showHist
      OneByte -> do
        Just (_, m) <- use $ cache . at ips
        m
        showHist
      _ -> do
        let mkInst ip' inst = do
                let ips = segAddr cs_ ip'
                Just (md, _) <- disassembleOne disasmConfig . BS.pack <$> fst (bytesAt__ ips maxInstLength)
                let ch = Set IP (Add (C $ fromIntegral $ mdLength md) (Get IP))
                      <> execInstruction' md
                      <> CheckInterrupt 1
                    ch' = inst <> ch
                case nextAddr ch ip' of
                    Just ip_' | ip_' > ip' -> mkInst ip_' ch'
                    _ -> return (ips + fromIntegral (mdLength md) - 1, ch')
        (end, reorderExp -> ch) <- mkInst ip_ mempty
        h <- use heap''
        zipWithM_ (uModInfo h) [ips..] $ map mergeInfo $ 0x81: replicate (end-ips) 1
        let ch_ = evalExpM ch
        cache %= IM.insert ips (end, ch_)
        ch_
        showHist

showHist = do
    hist <- clearHist
    when (not $ null hist) $ liftIO $ putStr $ " | " ++ hist

data Info
    = Builtin
    | OneByte
    | NoInfo

mergeInfo :: Word8 -> Word8 -> Word8
mergeInfo a b = (a + b) .|. (a .&. 0x80) .|. (b .&. 0x80)

readInfo :: Int -> Machine Info
readInfo i = do
    h <- use heap''
    info <- liftIO $ U.read h i
    case info of
      0xff00 -> return Builtin
      _ | testBit info 15 -> return OneByte
      _ -> return NoInfo

bytesToInt :: [Word8] -> Int
bytesToInt = foldl (\s b -> fromIntegral b .|. (s `shiftL` 8)) 0
intToBytes :: Int -> Int -> [Word8]
intToBytes 0 0 = []
intToBytes n i = (fromIntegral $ i .&. 0xff): intToBytes (n-1) (i `shiftR` 8)


getDef ( a: as) = a: getDef as
getDef _ = []

maxInstLength = 7

disasmConfig = Config Intel Mode16 SyntaxIntel 0

type MachinePart' a = (Machine a, a -> Machine ())

evalPart :: Part a -> (MachinePart' a -> Machine e) -> Machine e
evalPart p cont = case p of
    Heap16 e -> evalExp e >>= cont . wordAt__
    Heap8 e -> evalExp e >>= cont . byteAt__
    _ -> cont (use $ evalPart_ p, (evalPart_ p .=))

evalPart_ :: Part a -> MachinePart ( a)
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

evalExpM :: ExpM a -> Machine a
evalExpM = \case
    Seq a b -> evalExpM a >> evalExpM b
    LetM e f -> evalExp e >>= evalExpM . f . C

    Set p e -> evalPart p $ \(_, k) -> k =<< evalExp e
--    Mod p f -> evalPart p $ \(g, s) -> g >>= evalExp . f . C >>= s
    Nop -> return ()

    IfM b x y -> evalExp b >>= \b -> evalExpM $ if b then x else y
    Replicate n e -> evalExp n >>= \i -> replicateM_ i $ evalExpM e

    Input a f -> evalExp a >>= input >>= evalExpM . f . C
    Output a b -> evalExp a >>= \x -> evalExp b >>= \y -> output' x y

    QuotRem a b c f -> do
        x <- evalExp a
        y <- evalExp b
        case quotRemSafe x y of
            Nothing -> evalExpM c
            Just (z,v) -> evalExpM $ f (C z, C v)

    Trace a -> trace_ a
    Error h -> throwError h
    Interrupt e -> evalExp e >>= evalExpM . interrupt >> throwError Interr
    CheckInterrupt n -> do
      ivar <- use $ config . interruptRequest
      int <- liftIO $ readMVar ivar
      case int of
       Just int -> do
        mask <- use intMask
        when (not (testBit mask 0)) $ do
          liftIO $ modifyMVar_ ivar $ const $ return Nothing
          interrupt_ int
       Nothing -> do
        ns <- use $ config . stepsCounter
        let ns' = ns + n
        config . stepsCounter .= ns'
        ips <- use $ config . instPerSec
        let ips' = ips `div` 5
        when (ns' `div` ips' > ns `div` ips') $ do
          v <- use heap''
          var <- use $ config . videoMVar
          liftIO $ do
            let gs = 0xa0000
            putMVar var v 
          trace_ $ show ns
        mask <- use intMask
        when (not (testBit mask 0)) $ do
            cc <- askCounter n
            when cc $ do
                trace_ "timer"
                interrupt_ 0x08


evalExp :: Exp a -> Machine a
evalExp = \case
    C a -> return a

    Get p -> evalPart p $ \(k, _) -> k

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

    Bit i e -> (`testBit` i) <$> evalExp e
    SetBit i e f -> liftM2 (\a b -> b & bit i .~ a) (evalExp e) (evalExp f)
    HighBit e -> (^. highBit) <$> evalExp e
    SetHighBit e f -> liftM2 (\a b -> b & highBit .~ a) (evalExp e) (evalExp f)
    EvenParity e -> even . popCount <$> evalExp e

    Signed e -> asSigned <$> evalExp e    
    Extend e -> extend <$> evalExp e    
    SegAddr e f -> liftM2 segAddr (evalExp e) (evalExp f)
    Convert e -> fromIntegral <$> evalExp e    

    Let e f -> evalExp e >>= evalExp . f . C
    Tuple a b -> liftM2 (,) (evalExp a) (evalExp b)
    Fst p -> fst <$> evalExp p
    Snd p -> snd <$> evalExp p

    Iterate n f a -> evalExp n >>= \i -> evalExp $ iterate f a !! i


execInstructionBody m = (True {-TODO-}, evalExpM $ compileInst m)


input :: Word16 -> Machine (Word16)
input v = do
    case v of
        0x21 -> do
            x <- use intMask
            trace_ $ "get interrupt mask " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x60 -> do
            kvar <- use $ config . keyDown
            k <- liftIO $ readMVar kvar
            trace_ $ "keyboard scan code: " ++ showHex' 4 k
            return $ "???" @: k
        0x61 -> do
            x <- use $ config . speaker
            trace_ $ "get speaker: " ++ showHex' 2 x
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
            trace_ $ "int resume " ++ showHex' 2 x  -- ?
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
            trace_ $ "channel #41 " ++ showHex' 2 x  -- ?
        0x42 -> do
            trace_ $ "channel #42 " ++ showHex' 2 x
        0x43 -> do
            trace_ $ "set timer control " ++ showHex' 2 x
            case x of
                0x36  -> trace_ "set timer frequency lsb+msb, square wave"
                0xb6  -> trace_ "set speaker frequency lsb+msb, square wave"
        0x61 -> do
            config . speaker .= fromIntegral x
            trace_ $ "set speaker: " ++ showHex' 2 x
        0xf100 -> do
            trace_ "implemented for jmpmov test"
        _ -> haltWith $ "output #" ++ showHex' 4 v ++ " 0x" ++ showHex' 4 x

--------------------------------------------------------

imMax m | IM.null m = 0
        | otherwise = succ . fst . IM.findMax $ m

interrupt_ :: Word8 -> Machine ()
interrupt_ n = do
    i <- use interruptF
    if i then evalExpM (interrupt n) >> throwError Interr
         else do
            trace_ $ "interrupt cancelled " ++ showHex' 2 n
            when (n == 0x08) $ config . counter .= Just 0

origInterrupt :: M.Map (Word16, Word16) (Word8, Machine ())
origInterrupt = M.fromList

  [ item 0x00 (0xf000,0x1060) $ do
    trace_ "divison by zero interrupt"
    haltWith $ "int 00"

  , item 0x08 (0xf000,0xfea5) $ do     -- 
    trace_ "timer interrupt again"
    output' 0x20 0x20

  , item 0x09 (0xf000,0xe987) $ do     -- 09
    trace_ "keyboard interrupt again"
    haltWith $ "int 09"

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
                pmvar <- use $ config . palette
                liftIO $ modifyMVar_ pmvar $ \cs -> return $ cs V.//
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
            carryF .= False
      v  -> haltWith $ "interrupt #15,#" ++ showHex' 2 v

  , item 0x16 (0xf000,0x1200) $ do     -- 16h
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

{-
  0x20 -> do
    trace_ "interrupt halt"
    halt
-}

  , item 0x21 (0xf000,0x14c0) $ do     -- 21h
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
            use dx >>= (snd $ wordAt__ (4*v))     -- DS:DX = pointer to interrupt handler
            use ds >>= (snd $ wordAt__ (4*v + 2))

        0x30 -> do
            trace_ "Get DOS version"
            al .= "major version number" @: 0x05      --  (2-5)
            ah .= "minor version number" @: 0x00      --  (in hundredths decimal)
            bh .= "MS-DOS" @: 0xff
            do              -- 24 bit OEM serial number
                bl .= "OEM serial number (high bits)" @: 0
                cx .= "OEM serial number (low bits)" @: 0

        0x35 -> do
            v <- fromIntegral <$> use al     -- interrupt vector number
            trace_ $ "Get Interrupt Vector " ++ showHex' 2 v
            fst (wordAt__ (4*v)) >>= (bx .=)
            fst (wordAt__ (4*v + 2)) >>= (es .=)   -- ES:BX = pointer to interrupt handler

        0x3d -> do
            trace_ "Open File Using Handle"
            open_access_mode <- use al
--            v <- use dx
            case open_access_mode of
              0 -> do   -- read mode
                addr <- addressOf Nothing $ memIndex RDX
                fname <- fst $ bytesAt__ addr 20
                let f = map (toUpper . chr . fromIntegral) $ takeWhile (/=0) fname
                trace_ $ "File: " ++ show f
                let fn = "../original/" ++ f
                s <- liftIO $ do
                        b <- doesFileExist fn
                        if b then Just <$> BS.readFile fn else return Nothing
                case s of
                  Nothing -> do
                    trace_ $ "not found"
                    ax .= "File not found" @: 0x02
                    carryF .= True
                  Just s -> do
        --            ax .= 02  -- File not found
                    handle <- max 5 . imMax <$> use files
                    trace_ $ "handle " ++ showHex' 4 handle
                    files %= IM.insert handle (fn, s, 0)
                    ax .= "file handle" @: fromIntegral handle
                    carryF .=  False

        0x3e -> do
            trace_ "Close file"
            handle <- fromIntegral <$> use bx
            trace_ $ "handle " ++ showHex' 4 handle
            x <- IM.lookup handle <$> use files
            case x of
              Just (fn, _, _) -> do
                trace_ $ "file: " ++ fn
                files %= IM.delete handle
                carryF .=  False

        0x3f -> do
            handle <- fromIntegral <$> use bx
            fn <- (^. _1) . (IM.! handle) <$> use files
            num <- fromIntegral <$> use cx
            trace_ $ "Read " ++ showHex' 4 handle ++ ":" ++ fn ++ " " ++ showHex' 4 num
            loc <- addressOf Nothing $ memIndex RDX
            s <- BS.take num . (\(fn, s, p) -> BS.drop p s) . (IM.! handle) <$> use files
            let len = BS.length s
            files %= flip IM.adjust handle (\(fn, s, p) -> (fn, s, p+len))
            snd (bytesAt__ loc len) (BS.unpack s)
            ax .= "length" @: fromIntegral len
            carryF .=  False

        0x40 -> do
            handle <- fromIntegral <$> use bx
            trace_ $ "Write to " ++ showHex' 4 handle
            num <- fromIntegral <$> use cx
            loc <- addressOf Nothing $ memIndex RDX
            case handle of
              1 -> trace_ . ("STDOUT: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              2 -> trace_ . ("STDERR: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              _ -> return ()
            carryF .=  False

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
            carryF .=  False

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
            carryF .=  False

        0x48 -> do
            memory_paragraphs_requested <- use bx
            trace_ $ "Allocate Memory " ++ showHex' 5 (memory_paragraphs_requested ^. paragraph)
            x <- zoom heap $ state $ allocateMem (memory_paragraphs_requested ^. paragraph)
            ax .= "segment address of allocated memory block" @: (x ^. from paragraph) -- (MCB + 1para)
            carryF .=  False

        0x4a -> do
            new_requested_block_size_in_paragraphs <- use bx
            trace_ $ "Modify allocated memory blocks to " ++ showHex' 4 new_requested_block_size_in_paragraphs
            segment_of_the_block <- use es      -- (MCB + 1para)
            h <- use heap
            case modifyAllocated (segment_of_the_block ^. paragraph) (new_requested_block_size_in_paragraphs ^. paragraph) h of
              Left x -> do
                ax .= "Insufficient memory error" @: 8
                bx .= "maximum block size possible" @: (x ^. from paragraph)
                trace_ $ "insufficient, max possible: " ++ showHex' 4 (x ^. from paragraph)
                carryF .=  True
              Right h -> do
                ds <- use ds
                ax .= ds  -- why???
                heap .= h
                carryF .=  False

        0x4c -> do
            code <- use al
            trace_ $ "Terminate Process With Return Code #" ++ showHex' 2 code
            halt

        0x4e -> do
            attribute_used_during_search <- use cx
            addr <- addressOf Nothing $ memIndex RDX
            fname <- fst $ bytesAt__ addr 20
            let f_ = map (chr . fromIntegral) $ takeWhile (/=0) fname
            trace_ $ "Find file " ++ show f_
            ad <- use dta
            s <- liftIO $ do
                    b <- globDir1 (compile $ map toUpper f_) "../original"
                    case b of
                        (f:_) -> Just . (,) f <$> BS.readFile f
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
{-
                snd (bytesAt__ 0 0x1a) $ map (error' . ("undefined byte " ++) . showHex' 2) [0..]
                snd (byteAt__ 0x00) $ "attribute of serach" @: fromIntegral attribute_used_during_search
                snd (byteAt__ 0x01) $ "disk used during search" @: 2  -- C:
                snd (bytesAt__ 0x02 11) $ pad 0 11 fname
-}
                snd (bytesAt__ (ad + 0x02) 13 {- !!! -}) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f_) ++ [0])
                snd (byteAt__ $ ad + 0x15) $ "attribute of matching file" @: fromIntegral attribute_used_during_search
                snd (wordAt__ $ ad + 0x16) $ "file time" @: 0 -- TODO
                snd (wordAt__ $ ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                snd (byteAt__ $ ad + 0x00) 1
                ax .= 0 -- ?
                carryF .=  False
              Nothing -> do
                trace_ $ "not found"
                ax .= 02  -- File not found
                carryF .=  True

        0x4f -> do
            ad <- use dta
            fname <- fst $ bytesAt__ (ad + 0x02) 13
            -- addr <- addressOf Nothing $ memIndex RDX
            -- fname' <- fst $ bytesAt__ addr 20  -- wrong
            let f_ = map (chr . fromIntegral) $ takeWhile (/=0) fname
            trace_ $ "Find next matching file " ++ show f_
            n <- fst (byteAt__ $ ad + 0x00)
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
--                snd (byteAt__ $ ad + 0x15) $ "attribute of matching file" @: fromIntegral attribute_used_during_search
                snd (wordAt__ $ ad + 0x16) $ "file time" @: 0 -- TODO
                snd (wordAt__ $ ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                snd (byteAt__ $ ad + 0x00) $ n+1
                ax .= 0 -- ?
                carryF .=  False
              Nothing -> do
                trace_ $ "not found"
                ax .= 02  -- File not found
                carryF .=  True

        0x62 -> do
            trace_ "Get PSP address (DOS 3.x)"
            bx .= "segment address of current process" @: 0x1fe  -- hack!!!  !!!
            carryF .=  False

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
            ax .= "mouse?" @: 0xffff -- "mouse driver not installed" @: 0x0000
            bx .= "number of buttons" @: 3 -- 0
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
    item a k m = (k, (a, m >> evalExpM iret))

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
    h <- liftIO $ U.new 0x100000
    heap'' .= h
    zipWithM_ (snd . byteAt__) [0..] $ concat
            [ rom2'
            , memUndefined'' $ 0x100000 - length rom2'
            ]
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

    forM_ [(fromIntegral a, b) | (b, (a, _)) <- M.toList origInterrupt] $ \(i, (hi, lo)) -> do
        snd (wordAt__ $ 4*i) $ "interrupt lo" @: lo
        snd (wordAt__ $ 4*i + 2) $ "interrupt hi" @: hi
        h <- use heap''
        uWriteInfo h (segAddr hi lo) 0xff


    snd (wordAt__ 0x410) $ "equipment word" @: 0xd426 --- 0x4463   --- ???
    snd (byteAt__ 0x417) $ "keyboard shift flag 1" @: 0x20

    void $ clearHist
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

