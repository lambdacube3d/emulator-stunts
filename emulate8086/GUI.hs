module GUI
    ( drawWithFrameBuffer
    ) where

import Data.Bits
import Data.Word
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as Vec
import qualified Data.Vector.Storable as S
import qualified Data.Vector.Storable.Mutable as U
import Control.Monad as Prelude
import Control.Lens
import Control.Concurrent
import Graphics.Rendering.OpenGL.Raw.Core32
import Graphics.UI.GLFW as GLFW
import Foreign

import MachineState
import Helper
import Dos

------------------------------------------------

videoMem = 0xa0000
dof = 320 * 200

drawWithFrameBuffer :: (Machine () -> IO ()) -> (Request -> IO ()) -> IO () -> IO ()
drawWithFrameBuffer changeSt interrupt draw = do
    _ <- GLFW.init
    esds <- newMVar False
    vec2 <- U.new (320*200) :: IO (U.IOVector Word32)
    let winW = 960
        winH = 600
        sett r = changeSt $ instPerSec ..%= r
        setOVar f = showOffset .%= max 0 . min videoMem . f
    pos <- newMVar Nothing
    Just window <- GLFW.createWindow winW winH "Haskell Stunts" Nothing Nothing
    GLFW.makeContextCurrent $ Just window
    let posToAddr st x y = do
            offs <- use' showOffset
            let fb = heap''
                addr = offs + 320 * y + x
            val <- U.read fb addr
            return (addr, val)
    setCursorEnterCallback window $ Just $ \window -> \case
        CursorState'NotInWindow -> modifyMVar_ pos $ const $ return Nothing
        _ -> return ()
    setCursorPosCallback window $ Just $ \window x_ y_ -> do
        st <- use'' id
        let x = round x_ `div` 3
            y = round y_ `div` 3
        when (0 <= x && x < 320 && 0 <= y && y < 200) $ do
            modifyMVar_ pos $ const $ return $ Just ((x, y), Nothing)
    GLFW.setKeyCallback window $ Just $ \window key scancode action mods -> do
        let send (press, release) = case action of
                GLFW.KeyState'Pressed  -> interrupt $ AskKeyInterrupt press
                GLFW.KeyState'Released -> interrupt $ AskKeyInterrupt release
                _ -> return ()

        when (action /= GLFW.KeyState'Repeating) $ case key of
            Key'Escape  -> send (0x01, 0x81)
            Key'Space   -> send (0x39, 0xb9)
            Key'Enter   -> send (0xe01c, 0x9c)
            Key'C       -> send (0x2e, 0xae)
            Key'Left    -> send (0xe04b, 0xcb)
            Key'Right   -> send (0xe04d, 0xcd)
            Key'Up      -> send (0xe048, 0xc8)
            Key'Down    -> send (0xe050, 0xd0)
            _ -> return ()
        when (action /= GLFW.KeyState'Released) $ case key of
            Key'R -> setOVar $ const videoMem
            Key'A -> setOVar (+ dof)
            Key'S -> setOVar (+ (-dof))
            Key'X -> setOVar (+ 2*320)
            Key'Y -> setOVar (+ (-2*320))
            Key'B -> setOVar (+ 4)
            Key'V -> setOVar (+ (-4))
            Key'0 -> sett $ const 0.5
            Key'1 -> sett $ const 1
            Key'2 -> sett $ const 5
            Key'3 -> sett $ const 10
            Key'4 -> sett $ const 50
            Key'5 -> sett $ const 100
            Key'6 -> sett $ const 500
            Key'7 -> sett $ const 1000
            Key'8 -> sett $ const 5000
            Key'9 -> sett $ const 10000
            Key'N -> sett (* (1/1.1))
            Key'M -> sett (* 1.1)
            Key'Comma -> modifyMVar_ esds $ return . not
            Key'T -> showReads .%= not
            Key'I -> showReads' .%= not
            Key'U -> changeSt $ showCache ..%= not
            Key'P -> changeSt $ speed ..%= (3000 -)
            Key'W -> changeSt adjustCache
            Key'Q -> GLFW.setWindowShouldClose window True
            _ -> return ()

    -- create back buffer
    (tex,fbo) <- mkBackBuffer

    tv <- newEmptyMVar
    _ <- forkIO $ forever $ do
        threadDelay $ 1000000 `div` 20
        putMVar tv ()
    let
        mainLoop = do
            b <- GLFW.windowShouldClose window
            unless b $ do
                draw
                _ <- takeMVar tv
                st <- use'' id
                esds' <- readMVar esds
                offs <- use' showOffset
                let fb = heap''
                b <- use' showReads
                (vec, post) <- if b then do
                    return $ (,) showBuffer $ do
                        U.set showBuffer 0
                        when (st ^. showCache) $ do
                            ca <- use' cache
                            forM_ (IM.toList $ fst $ IM.split (offs + 320 * 200) $ snd $ IM.split (offs-1) ca) $ \case
                                (k, Compiled _ _ es ds _ r _) -> forM_ r $ \(beg, end) ->
                                    forM_ [max 0 $ beg - offs .. min (320 * 200 - 1) $ end - 1 - offs] $ \i -> do
--                                        x <- U.unsafeRead v i
                                        U.unsafeWrite showBuffer i $ maybe 0xffff0000 ((.|. 0x0000ff00) . (`shiftL` 16) . fromIntegral) (if esds' then es else ds) -- x .|. 0x3f000000
                                (k, DontCache _) -> do
                                    U.unsafeWrite showBuffer (k - offs) $ 0xffff0000
                                _ -> return ()
                  else do
                    let p = st ^. palette
                    v <- S.unsafeFreeze fb
                    vec2 <- S.unsafeThaw $ S.unsafeBackpermute p (S.map fromIntegral $ S.slice offs (320*200) v)
                    return (vec2, return ())
                p <- readMVar pos
                case p of
                    Nothing -> return ()
                    Just ((x, y), v) -> do
                        v'@(addr, val) <- posToAddr st x y
                        modifyMVar_ pos $ const $ return $ Just ((x, y), Just v')
                        when (v /= Just v') $ onScreen $ "[" ++ showHex' 5 addr ++ "] = " ++ showHex' 2 val
                        let drawPix x y = when (0 <= i && i < 320 * 200) $ U.write vec i 0xffffff00 where i = 320 * y + x
                        forM_ [5..8] $ \j -> do
                            drawPix (x + j) y
                            drawPix (x - j) y
                            drawPix x (y + j)
                            drawPix x (y - j)
                U.unsafeWith vec $ glTexSubImage2D gl_TEXTURE_2D 0 0 0 320 200 gl_RGBA gl_UNSIGNED_INT_8_8_8_8
                glBlitFramebuffer 0 200 320 0 0 0 (fromIntegral winW) (fromIntegral winH) gl_COLOR_BUFFER_BIT gl_NEAREST
                GLFW.swapBuffers window
                post
                GLFW.pollEvents
                mainLoop
    mainLoop

    -- free back buffer
    Foreign.with fbo $ glDeleteFramebuffers 1
    Foreign.with tex $ glDeleteTextures 1

    GLFW.destroyWindow window
    GLFW.terminate

-- TODO
onScreen str = putStrLn str

mkBackBuffer = do
  fbo <- alloca $! \pbo -> glGenFramebuffers 1 pbo >> peek pbo
  glBindFramebuffer gl_DRAW_FRAMEBUFFER fbo
  tex <- alloca $! \pto -> glGenTextures 1 pto >> peek pto
  glBindTexture gl_TEXTURE_2D tex
  glTexParameteri gl_TEXTURE_2D gl_TEXTURE_MAG_FILTER $ fromIntegral gl_NEAREST
  glTexParameteri gl_TEXTURE_2D gl_TEXTURE_MIN_FILTER $ fromIntegral gl_NEAREST
  glTexImage2D gl_TEXTURE_2D 0 (fromIntegral gl_RGBA) 320 200 0 (fromIntegral gl_RGBA) gl_UNSIGNED_BYTE nullPtr
  glFramebufferTexture2D gl_DRAW_FRAMEBUFFER gl_COLOR_ATTACHMENT0 gl_TEXTURE_2D tex 0
  status <- glCheckFramebufferStatus gl_FRAMEBUFFER
  if (status /= gl_FRAMEBUFFER_COMPLETE)
    then do
      putStrLn $ "incomplete framebuffer: " ++ show status
    else do
      glBindFramebuffer gl_READ_FRAMEBUFFER fbo
      glBindFramebuffer gl_DRAW_FRAMEBUFFER 0
  return (tex,fbo)

