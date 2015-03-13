{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
module DosBox
    ( drawWithFrameBuffer
    ) where

import Data.Bits
import Data.Word
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as Vec
import Data.Vector.Mutable as MVec
import qualified Data.Vector.Storable.Mutable as U
--import Data.Vector.Storable as SVec
import Control.Applicative
import Control.Monad as Prelude
import Control.Lens
import Control.Concurrent
import Graphics.Rendering.OpenGL.Raw.Core32
import Graphics.Rendering.OpenGL.Raw.Compatibility30
import "GLFW-b" Graphics.UI.GLFW as GLFW
import Foreign

import MachineState

videoMem = 0xa0000
dof = 320 * 200

drawWithFrameBuffer :: (Machine () -> IO ()) -> (Request -> IO ()) -> MVar MachineState -> IO () -> IO ()
drawWithFrameBuffer changeSt interrupt stvar draw = do
    GLFW.init
    vec2 <- U.new (320*200) :: IO (U.IOVector Word32)
    let winW = 960
        winH = 600
        sett r = changeSt $ config . instPerSec %= r
        setOVar f = changeSt $ config . showOffset %= max 0 . min videoMem . f
    Just window <- GLFW.createWindow winW winH "Haskell Stunts" Nothing Nothing
    GLFW.makeContextCurrent $ Just window
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
            Key'T -> changeSt $ config . showReads %= not
            Key'U -> changeSt $ config . showCache %= not
            Key'Q -> GLFW.setWindowShouldClose window True
            _ -> return ()

    -- create back buffer
    (tex,fbo) <- mkBackBuffer

    tv <- newEmptyMVar
    forkIO $ forever $ do
        threadDelay $ 1000000 `div` 20
        putMVar tv ()
    let
        mainLoop = do
            b <- GLFW.windowShouldClose window
            unless b $ do
                draw
                _ <- takeMVar tv
                st <- readMVar stvar
                let offs = st ^. config . showOffset
                (vec, post) <- if st ^. config . showReads then do
                    let v = st ^. config . showBuffer
                    return $ (,) v $ do
                        U.set v 0
                        when (st ^. config . showCache) $ do
                            forM_ (IM.toList $ fst $ IM.split (offs + 320 * 200) $ snd $ IM.split (offs-1) $ st ^. cache) $ \case
                                (k, Compiled _ _ r _) -> forM_ r $ \(beg, end) ->
                                    forM_ [max 0 $ beg - offs .. min (320 * 200 - 1) $ end - 1 - offs] $ \i -> do
                                        x <- U.unsafeRead v i
                                        U.unsafeWrite v i $ x .|. 0x0000ff00
                                (k, DontCache _) -> do
                                    U.unsafeWrite v (k - offs) $ 0xffffff00
                                _ -> return ()
                  else do
                    let fb = st ^. heap''
                        p = st ^. config . palette
                    forM_ [0..199] $ \y -> do
                      let y_ = offs + 320 * y
                          y' = 320 * y
                      forM_ [0..319] $ \x -> do
                        a <- U.unsafeRead fb $ y_ + x
                        v <- Vec.unsafeIndexM p $ fromIntegral a .&. 0xff
                        U.unsafeWrite vec2 (y' + x) v
                    return (vec2, return ())
                U.unsafeWith vec $ glTexSubImage2D gl_TEXTURE_2D 0 0 0 320 200 gl_RGBA gl_UNSIGNED_INT_8_8_8_8
                glBlitFramebuffer 0 0 320 200 0 0 (fromIntegral winW) (fromIntegral winH) gl_COLOR_BUFFER_BIT gl_NEAREST
                GLFW.swapBuffers window
                post
                GLFW.pollEvents
                mainLoop
    mainLoop
--    wait <- newEmptyMVar
--    interrupt $ PrintFreqTable wait
--    _ <- takeMVar wait

    -- free back buffer
    Foreign.with fbo $ glDeleteFramebuffers 1
    Foreign.with tex $ glDeleteTextures 1

    GLFW.destroyWindow window
    GLFW.terminate

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

