{-# LANGUAGE OverloadedStrings #-}
module Dos where

import Data.Word
import Data.Int
import Data.Bits hiding (bit)
import Data.Char
import Data.List
import Data.Monoid
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector.Storable as V
import Control.Applicative
import Control.Monad.State
import Control.Lens as Lens
import Control.Concurrent
import System.Directory
import System.FilePath (takeFileName)
import System.FilePath.Glob
import Sound.ALUT (play, stop, sourceGain, pitch, ($=))
import Prelude

import Helper
import MachineState

---------------------------------------------- memory allocation

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

(@:) :: BS.ByteString -> a ->  a
b @: x = x
infix 5 @:

combine :: Iso' (Word8, Word8) Word16
combine = iso (\(hi,lo) -> fromIntegral hi `shiftL` 8 .|. fromIntegral lo) (\d -> (fromIntegral $ d `shiftR` 8, fromIntegral d))

haltWith = error
halt = error "CleanHalt"

getSender = do
    v <- use'' interruptRequest
    return $ \r -> modifyMVar_ v $ return . (++ [r])

setCounter = do
    counter ..%= (+1)
    c <- use'' counter
    v <- use'' instPerSec
    send <- getSender
    void $ forkIO $ do
        threadDelay $ round $ 1000000 / v
        send $ AskTimerInterrupt c

--------------------------------------------------------------------------------

input :: Word16 -> Machine (Word16)
input v = do
    case v of
        0x21 -> do
            x <- use'' intMask
            trace_ $ "get interrupt mask " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x60 -> do
            k <- use'' keyDown
            trace_ $ "keyboard scan code: " ++ showHex' 4 k
            return $ "???" @: k
        0x61 -> do
            x <- use'' speaker
            when ((x .&. 0xfc) /= 0x30) $ trace_ $ "speaker -> " ++ showHex' 2 x
            return $ "???" @: fromIntegral x
        0x03da -> do
            -- TODO
            r <- head <$> use'' retrace
            retrace ..%= tail
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
            intMask ...= fromIntegral x
            when (not $ testBit x 0) setCounter
        0x40 -> do
            trace_ $ "set timer frequency " ++ showHex' 2 x --show (1193182 / fromIntegral x) ++ " HZ"
        0x41 -> do
            trace_ $ "ch #41 " ++ showHex' 2 x  -- ?
        0x42 -> do
--            trace_ $ "ch #42 " ++ showHex' 2 x
            frequency ..%= (.|. (x `shiftL` 8)) . (`shiftR` 8)
            f <- use'' frequency
            source <- use'' soundSource
            when (fromIntegral f >= 128) $ pitch source $= 2711 / fromIntegral f
        0x43 -> do
            trace_ $ "set timer control " ++ showHex' 2 x
            case x of
                0x36  -> trace_ "set timer frequency lsb+msb, square wave"
                0xb6  -> trace_ "set speaker frequency lsb+msb, square wave"
        0x61 -> do
            x' <- use'' speaker
            source <- use'' soundSource
            speaker ...= fromIntegral x
            when (x .&. 0xfc /= 0x30) $ trace_ $ "speaker <- " ++ showHex' 2 x
            do
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
    v <- use' ah
    case v of
        0x00 -> do
            video_mode_number <- use' al
            trace_ $ "Set Video Mode #" ++ showHex' 2 video_mode_number
            case video_mode_number of
                0x00 -> do
                    trace_ "text mode"
                0x03 -> do
                    trace_ "mode 3"
                0x13 -> do
                    bx ..= 0  -- 4  -- ???
                _ -> haltWith $ "#" ++ showHex' 2 video_mode_number
        0x0b -> do
            trace_ "Select Graphics Palette or Text Border Color"
        0x0e -> do
            a <- use' al
            putChar $ chr . fromIntegral $ a
            trace_ $ "Write Character as TTY: " ++ showHex' 2 a
            
--            traceM $ (:[]) . chr . fromIntegral $ a
        0x0f -> do
            trace_ "Get Current Video Mode"
            al ..= "text mode" @: 3
            ah ..= "width of screen, in character columns" @: 80
            bh ..= "current active video page (0-based)" @: 0x00 --b8
        0x10 -> do
            trace_ "Set/Get Palette Registers (EGA/VGA)"
            f <- use' al
            case f of
              0x12 -> do
                trace_ "set block of DAC color registers"
                first_DAC_register <- use' bx -- (0-00ffH)
                number_of_registers <- use' cx -- (0-00ffH)
                -- Es:DX addr of a table of R,G,B values (it will be CX*3 bytes long)
                addr <- dxAddr'
                colors <- fst $ bytesAt__ addr $ 3 * fromIntegral number_of_registers
                palette ..%= \cs -> cs V.//
                    zip [fromIntegral first_DAC_register .. fromIntegral (first_DAC_register + number_of_registers - 1)]
                        -- shift 2 more positions because there are 64 intesity levels
                        [ fromIntegral r `shiftL` 26 .|. fromIntegral g `shiftL` 18 .|. fromIntegral b `shiftL` 10
                        | [r, g, b] <- everyNth 3 $ colors]

              v -> haltWith $ "interrupt #10,#10,#" ++ showHex' 2 f

        v  -> haltWith $ "interrupt #10,#" ++ showHex' 2 v

  , item 0x15 (0xf000,0x11e0) $ do     -- 15h
    trace_ "Misc System Services"
    v <- use' ah
    case v of
--      0x00 -> do
--        trace_ "Turn on casette driver motor"
      0xc2 -> do
        trace_ "Pointing device BIOS interface"
        w <- use' al
        case w of
          0x01 -> do
            trace_ "Reset Pointing device"
            ah ..= 0 -- ?
            bl ..= 0xaa -- ?
            returnOK
      v  -> haltWith $ "interrupt #15,#" ++ showHex' 2 v

  , item 0x16 (0xf000,0x1200) $ do
    trace_ "Keyboard Services"
    v <- use' ah
    case v of
        0x00 -> do
            trace_ "Read (Wait for) Next Keystroke"
            ah ..= "Esc scan code" @: 0x39
            al ..= "Esc ASCII code" @: 0x1b
        0x01 -> do
            trace_ "Query Keyboard Status / Preview Key"
            zeroF ..= False  -- no keys in buffer
        v  -> haltWith $ "interrupt #16,#" ++ showHex' 2 v

  , item 0x20 (0x0000, 0x0000) $ do
    trace_ "interrupt halt"
    halt

  , item 0x21 (0xf000,0x14c0) $ do
    trace_ "DOS rutine"
    v <- use' ah
    case v of
        0x00 -> do
            trace_ "dos Program terminate"
            halt

        0x1a -> do
            trace_ "Set Disk Transfer Address (DTA)"
            addr <- dxAddr
            dta ...= addr

        0x25 -> do
            v <- fromIntegral <$> use' al     -- interrupt vector number
            trace_ $ "Set Interrupt Vector " ++ showHex' 2 v
            use' dx >>= setWordAt System (4*v)     -- DS:DX = pointer to interrupt handler
            use' ds >>= setWordAt System (4*v + 2)

        0x30 -> do
            trace_ "Get DOS version"
            al ..= "major version number" @: 0x05      --  (2-5)
            ah ..= "minor version number" @: 0x00      --  (in hundredths decimal)
            bh ..= "MS-DOS" @: 0xff
            do              -- 24 bit OEM serial number
                bl ..= "OEM serial number (high bits)" @: 0
                cx ..= "OEM serial number (low bits)" @: 0

        0x35 -> do
            v <- fromIntegral <$> use' al
            trace_ $ "Get Interrupt Vector " ++ showHex' 2 v
            wordAt__ System (4*v) >>= (bx ..=)
            wordAt__ System (4*v + 2) >>= (es ..=)   -- Es:BX = pointer to interrupt handler

        0x3c -> do
            trace_ "Create File"
            (f, fn) <- getFileName
            attributes <- use' cx
            b <- doesFileExist fn
            if b then dosFail 0x05 -- access denied
              else do
                writeFile fn ""
                newHandle fn
        0x3d -> do
            trace_ "Open File Using Handle"
            open_access_mode <- use' al
            case open_access_mode of
              0 -> do   -- read mode
                (f,fn) <- getFileName
                checkExists fn $ newHandle fn

        0x3e -> do
            trace_ "Close file"
            handle <- fromIntegral <$> use' bx
            trace_ $ "handle " ++ showHex' 4 handle
            x <- IM.lookup handle <$> use'' files
            case x of
              Just (fn, _) -> do
                trace_ $ "file: " ++ fn
                files ..%= IM.delete handle
                returnOK

        0x3f -> do
            handle <- fromIntegral <$> use' bx
            (fn, seek) <- (IM.! handle) <$> use'' files
            num <- fromIntegral <$> use' cx
            trace_ $ "Read " ++ showHex' 4 handle ++ ":" ++ fn ++ " " ++ showHex' 4 num
            loc <- dxAddr
            s <- BS.take num . BS.drop seek <$> BS.readFile fn
            let len = BS.length s
            files ..%= flip IM.adjust handle (\(fn, p) -> (fn, p+len))
            snd (bytesAt__ loc len) (BS.unpack s)
            ax ..= "length" @: fromIntegral len
            returnOK

        0x40 -> do
            handle <- fromIntegral <$> use' bx
            trace_ $ "Write to " ++ showHex' 4 handle
            num <- fromIntegral <$> use' cx
            loc <- dxAddr
            case handle of
              1 -> trace_ . ("STDOUT: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              2 -> trace_ . ("STDERR: " ++) . map (chr . fromIntegral) =<< fst (bytesAt__ loc num)
              _ -> return ()
            returnOK

        0x41 -> do
            trace_ "Delete File"
            (f,fn) <- getFileName
            checkExists fn $ do
                removeFile fn
                returnOK

        0x42 -> do
            handle <- fromIntegral <$> use' bx
            fn <- (^. _1) . (IM.! handle) <$> use'' files
            mode <- use' al
            pos <- fromIntegral . (fromIntegral :: Word32 -> Int32) <$> use' cxdx
            trace_ $ "Seek " ++ showHex' 4 handle ++ ":" ++ fn ++ " to " ++ show mode ++ ":" ++ showHex' 8 pos
            s <- BS.readFile fn
            files ..%= (flip IM.adjust handle $ \(fn, p) -> case mode of
                0 -> (fn, pos)
                1 -> (fn, p + pos)
                2 -> (fn, BS.length s + pos)
                )
            pos' <- (^. _2) . (IM.! handle) <$> use'' files
            dxax ..= fromIntegral pos'
            returnOK

        0x44 -> do
            trace_ "I/O Control for Devices (IOCTL)"
            0x44 <- use' ah
            function_value <- use' al
{-
            file_handle <- use bx
            logical_device_number <- use bl -- 0=default, 1=A:, 2=B:, 3=C:, ...
            number_of_bytes_to_read_or_write <- use cx
            data_or_buffer <- use dx
-}
            case function_value of
              0x00 -> do
                handle <- use' bx
                trace_ $ "Get Device Information of " ++ show handle 
                let v = case handle of
                      4 -> 0x80A0        --  0010 1000 00 000100   no D: drive
                      3 -> 0x80D3        --  0010 1000 00 000011   no C: drive
                      2 -> 0x80D3        --  0010 1000 00 000011    B: drive
                      1 -> 0x80D3        --  0010 1000 00 000011    A: drive
                      0 -> 0x80D3        --  0010 1000 00 000011    default drive
                dx ..= v
                ax ..= v
            returnOK

        0x48 -> do
            memory_paragraphs_requested <- use' bx
            trace_ $ "Allocate Memory " ++ showHex' 5 (memory_paragraphs_requested ^. paragraph)
            h <- use'' heap
            let (x, h') = allocateMem (memory_paragraphs_requested ^. paragraph) h
            heap ...= h'
            ax ..= "segment address of allocated memory block" @: (x ^. from paragraph) -- (MCB + 1para)
            returnOK

        0x4a -> do
            new_requested_block_size_in_paragraphs <- use' bx
            trace_ $ "Modify allocated memory blocks to " ++ showHex' 4 new_requested_block_size_in_paragraphs
            segment_of_the_block <- use' es      -- (MCB + 1para)
            h <- use'' heap
            case modifyAllocated (segment_of_the_block ^. paragraph) (new_requested_block_size_in_paragraphs ^. paragraph) h of
              Left x -> do
                bx ..= "maximum block size possible" @: (x ^. from paragraph)
                trace_ $ "insufficient, max possible: " ++ showHex' 4 (x ^. from paragraph)
                dosFail 0x08 -- insufficient memory
              Right h -> do
                ds <- use' ds
                ax ..= ds  -- why???
                heap ...= h
                returnOK

        0x4c -> do
            code <- use' al
            trace_ $ "Terminate Process With Return Code #" ++ showHex' 2 code
            halt

        0x4e -> do
            trace_ $ "Find file"
            (f_,_) <- getFileName
            attribute_used_during_search <- use' cx
            ad <- use'' dta
            s <- do
                    b <- globDir1 (compile $ map toUpper f_) "../original"
                    case b of
                        (f:_) -> Just . (,) f <$> BS.readFile f
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
                snd (bytesAt__ (ad + 0x02) 13 {- !!! -}) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f_) ++ [0])
                setByteAt System (ad + 0x15) $ "attribute of matching file" @: fromIntegral attribute_used_during_search
                setWordAt System (ad + 0x16) $ "file time" @: 0 -- TODO
                setWordAt System (ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ System $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                setByteAt System (ad + 0x00) 1
                ax ..= 0 -- ?
                returnOK
              Nothing -> dosFail 0x02  -- File not found

        0x4f -> do
            ad <- use'' dta
            fname <- fst $ bytesAt__ (ad + 0x02) 13
            let f_ = map (chr . fromIntegral) $ takeWhile (/=0) fname
            trace_ $ "Find next matching file " ++ show f_
            n <- byteAt__ System $ ad + 0x00
            s <- do
                    b <- globDir1 (compile $ map toUpper f_) "../original"
                    case drop (fromIntegral n) b of
                        filenames@(f:_) -> do
                            trace_ $ "alternatives: " ++ show filenames
                            Just . (,) f <$> (BS.readFile f)
                        _ -> return Nothing
            case s of
              Just (f, s) -> do
                trace_ $ "found: " ++ show f
                setWordAt System (ad + 0x16) $ "file time" @: 0 -- TODO
                setWordAt System (ad + 0x18) $ "file date" @: 0 -- TODO
                snd (dwordAt__ System $ ad + 0x1a) $ fromIntegral (BS.length s)
                snd (bytesAt__ (ad + 0x1e) 13) $ pad 0 13 (map (fromIntegral . ord) (strip $ takeFileName f) ++ [0])
                setByteAt System (ad + 0x00) $ n+1
                ax ..= 0 -- ?
                returnOK
              Nothing -> dosFail 0x02

        0x62 -> do
            trace_ "Get PSP address (DOS 3.x)"
            bx ..= "segment address of current process" @: 0x1fe  -- hack!!!  !!!
            returnOK

        _    -> haltWith $ "dos function #" ++ showHex' 2 v

  , item 0x24 (0x0118,0x0110) $ do     -- 24h
    trace_ "critical error handler interrupt"
    haltWith $ "int 24"

  , item 0x33 (0xc7ff,0x0010) $ do     -- 33h
--    trace_ "Mouse Services"
    v <- use' ax
    case v of
        0x00 -> do
            trace_ "Mouse Reset/Get Mouse Installed Flag"
            ax ..= {- "mouse?" @: 0xffff -} "mouse driver not installed" @: 0x0000
            bx ..= "number of buttons" @: 0 -- 3
        0x03 -> do
--            trace_ "Get Mouse position and button status"
            cx ..= "mouse X" @: 0
            dx ..= "mouse Y" @: 0
            bx ..= "button status" @: 0
        0x07 -> do
            trace_ "Set Mouse Horizontal Min/Max Position"
            minimum_horizontal_position <- use' cx
            maximum_horizontal_position <- use' dx
            return ()
        0x08 -> do
            trace_ "Set Mouse Vertical Min/Max Position"
            minimum_vertical_position <- use' cx
            maximum_vertical_position <- use' dx
            return ()
        0x0f -> do
            trace_ "Set Mouse Mickey Pixel Ratio"
        _    -> haltWith $ "Int 33h, #" ++ showHex' 2 v
  ]
  where 
    item :: Word8 -> (Word16, Word16) -> Machine () -> ((Word16, Word16), (Word8, Machine ()))
    item a k m = (k, (a, m >> iret))

    newHandle fn = do
        handle <- max 5 . imMax <$> use'' files
        files ..%= IM.insert handle (fn, 0)
        trace_ $ "handle " ++ showHex' 4 handle
        ax ..= "file handle" @: fromIntegral handle
        returnOK

    getFileName = do
        addr <- dxAddr
        fname <- fst $ bytesAt__ addr 40
        let f = map (toUpper . chr . fromIntegral) $ takeWhile (/=0) fname
        trace_ f
        let fn = "../original/" ++ f
        return (f, fn)

    dxAddr = liftM2 segAddr (use' ds) (use' dx)
    dxAddr' = liftM2 segAddr (use' es) (use' dx)

    checkExists fn cont = do
        b <- doesFileExist fn
        if b then cont else dosFail 0x02

    returnOK = carryF ..= False

    dosFail errcode = do
        trace_ $ showerr errcode
        ax ..= errcode
        carryF ..= True
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

programSegmentPrefix' :: Int -> Word16 -> Word16 -> BS.ByteString -> Machine ()
programSegmentPrefix' base envseg endseg args = do

    wordAt_ 0x00 $ "CP/M exit, always contain code 'int 20h'" @: 0x20CD
    wordAt_ 0x02 $ "Segment of the first byte beyond the memory allocated to the program" @: endseg
--    bytesAt 0x05 5 .= [0xea, 0xff, 0xff, 0xad, 0xde]   -- FAR call to MSDOS function dispatcher (int 21h)?
--    dwordAt 0x0a .= 0xf00020c8    -- Terminate address of previous program (old INT 22h)
--    dwordAt 0x0e .= 0x01180000    -- Break address of previous program (old INT 23h)
--    dwordAt 0x12 .= 0x01180110    -- Critical error address of previous program (old INT 24h)
--    wordAt 0x16 .= 0x0118    -- Caller's PSP segment (usually COMMAND.COM - internal)

    -- Job File Table (JFT) (internal)
--    bytesAt 0x18 20 .= [0x01, 0x01, 0x01, 0x00, 0x02, 0x03] ++ repeat 0xff

    wordAt_ 0x2c $ "Environment segment" @: envseg
--    dwordAt 0x2e .= 0x0192ffe6 -- SS:SP on entry to last INT 21h call (internal)

--    wordAt 0x32 .= 0x0014 -- JFT size (internal)
--    dwordAt 0x34 .= 0x01920018-- Pointer to JFT (internal)
--    dwordAt 0x38 .= 0xffffffff -- Pointer to previous PSP (only used by SHARE in DOS 3.3 and later)
    -- 3Ch-3Fh     4 bytes     Reserved
--    wordAt 0x40 .= 0x0005 -- DOS version to return (DOS 4 and later, alterable via SETVER in DOS 5 and later)
    -- 42h-4Fh     14 bytes     Reserved
    bytesAt_ 0x50 3 [0xcd, 0x21, 0xcb] -- (code) Far call to DOS (always contain INT 21h + RETF)
    -- 53h-54h     2 bytes     Reserved
    -- 55h-5Bh     7 bytes     Reserved (can be used to make first FCB into an extended FCB)

    -- 5Ch-6Bh     16 bytes     Unopened Standard FCB 1
    -- 6Ch-7Fh     20 bytes     Unopened Standard FCB 2 (overwritten if FCB 1 is opened)
--    bytesAt 0x5c (16 + 20) .= repeat 0

    byteAt_ 0x80 $ "args length" @: fromIntegral (min maxlength $ BS.length args)
    bytesAt_ 0x81 (maxlength + 1) $ pad 0 (maxlength + 1) (take maxlength (BS.unpack args) ++ [0x0D])  -- Command line string
--    byteAt 0xff .= 0x36   -- dosbox specific?
  where
    wordAt_ i = setWordAt System (i+base)
    byteAt_ i = setByteAt System (i+base)
    bytesAt_ i l = snd (bytesAt__ (i+base) l) 

    maxlength = 125

pspSize = 256 :: Int

envvars :: [Word8]
envvars = map (fromIntegral . ord) "PATH=Z:\\\NULCOMSPEC=Z:\\COMMAND.COM\NULBLASTER=A220 I7 D1 H5 T6\0\0\1\0C:\\GAME.EXE" ++
 replicate 20 0

replicate' n _ | n < 0 = error "replicate'"
replicate' n x = replicate n x

loadExe :: Word16 -> BS.ByteString -> Machine (Int -> BSC.ByteString)
loadExe loadSegment gameExe = do
    flags ..= wordToFlags 0xf202

    heap ...= ( [(length rom', length rom2')], 0xa0000 - 16)
    zipWithM_ (setByteAt System) [0..] rom2'
    ss ..=  (ssInit + loadSegment)
    sp ..=  spInit
    cs ..=  (csInit + loadSegment)
    ip ..=  ipInit
    ds ..=  pspSegment
    es ..=  pspSegment
    cx ..=  0x00ff -- why?
    dx ..=  pspSegment -- why?
    bp ..=  0x091c -- why?
    si ..=  0x0012 -- why?
    di ..=  0x1f40 -- why?
    labels ...= mempty

    print $ showHex' 5 $ loadSegment ^. paragraph
    print $ showHex' 5 headerSize

    setWordAt System (0x410) $ "equipment word" @: 0xd426 --- 0x4463   --- ???
    setByteAt System (0x417) $ "keyboard shift flag 1" @: 0x20

    forM_ [(fromIntegral a, b, m) | (b, (a, m)) <- M.toList origInterrupt] $ \(i, (hi, lo), m) -> do
        setWordAt System (4*i) $ "interrupt lo" @: lo
        setWordAt System (4*i + 2) $ "interrupt hi" @: hi
        cache .%= IM.insert (segAddr hi lo) (BuiltIn m)

    programSegmentPrefix' (length rom' + 16) (length prelude' ^. from paragraph) endseg ""

    gameexe ...= (exeStart, relocatedExe)

    -- hack for stunts: skip the first few instructions to ensure constant ss value during run
    ip ..=  0x004f
    si ..=  0x0d20
    di ..=  0x2d85
    sp ..=  0xcc5e
    ss ..=  0x2d85
    
    return getInst

  where
    getInst i
        | j >= 0 && j < BS.length relocatedExe = BS.drop j relocatedExe
      where
        j = i - exeStart

    rom' = concat
            [ prelude'
            , envvars
            , replicate' (loadSegment ^. paragraph - length prelude' - length envvars - pspSize - 16) 0
            ]
    rom2' = concat
        [ rom'
        , replicate 16 0
        , replicate pspSize 0
        , BS.unpack $ relocatedExe
        , memUndefined'' $ additionalMemoryAllocated ^. paragraph
        ]

    exeStart = loadSegment ^. paragraph
    relocatedExe = relocate relocationTable loadSegment $ BS.drop headerSize gameExe

    pspSegment = loadSegment - (pspSize ^. from paragraph)
    endseg = loadSegment + executableSize ^. from paragraph + additionalMemoryAllocated

    additionalMemoryAllocated = additionalMemoryNeeded
        -- could be anything between additionalMemoryNeeded and maxAdditionalMemoryNeeded

    (0x5a4d: bytesInLastPage: pagesInExecutable: relocationEntries:
     paragraphsInHeader: additionalMemoryNeeded: _maxAdditionalMemoryNeeded: ssInit:
     spInit: _checksum: ipInit: csInit:
     firstRelocationItemOffset: _overlayNumber: headerLeft)
        = map (\[low, high] -> (high, low) ^. combine) $ everyNth 2 $ BS.unpack $ gameExe

    headerSize = paragraphsInHeader ^. paragraph
    executableSize = (fromIntegral pagesInExecutable `shiftL` 9)
            + (if (bytesInLastPage > 0) then fromIntegral bytesInLastPage - 0x200 else 0)
            - 0x22f0  -- ???
            :: Int

    relocationTable = sort $ take (fromIntegral relocationEntries)
        $ map (\[a,b]-> segAddr b a) $ everyNth 2 $ drop (fromIntegral firstRelocationItemOffset `div` 2 - 14) headerLeft

unique xs = length xs == length (nub xs)

relocate :: [Int] -> Word16 -> BS.ByteString -> BS.ByteString
relocate table loc exe = BS.concat $ fst: map add (bss ++ [last])
  where
    (last, fst: bss) = mapAccumL (flip go) exe $ zipWith (-) table $ 0: table

    go r (BS.splitAt r -> (xs, ys)) = (ys, xs)

    add (BS.uncons -> Just (x, BS.uncons -> Just (y, xs))) = BS.cons x' $ BS.cons y' xs
        where (y',x') = combine %~ (+ loc) $ (y,x)


---------------------------------


