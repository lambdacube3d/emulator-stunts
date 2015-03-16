import qualified Data.ByteString as BS
import Control.Monad.State
import Control.Lens as Lens
import Control.Concurrent
import System.IO
import Sound.ALUT

import Dos
import Emulate
import DosBox
import MachineState

--------------------------------------------------------------------------------

gameFile = "../restunts/stunts/game.exe"
loadSegment = 0x20e

main = withProgNameAndArgs runALUT $ \_ _ -> do

    bData <- createBufferData (Square 440 0 0.1)
    buff <- createBuff bData 1
    [source] <- genObjectNames 1
    loopingMode source $= Looping
    stop [source]
    buffer source $= Just buff

    hSetBuffering stdout NoBuffering
    changeState <- newMVar $ return ()
    let addChange m = modifyMVar_ changeState $ \n -> return $ n >> m
--    l <- getLabels
    game <- BS.readFile gameFile
    st <- emptyState
    pmvar <- newMVar st
    _ <- forkIO $ void $ flip evalStateT st $ do
        config . verboseLevel .= 1 
        config . soundSource .= source
        getInst <- loadExe loadSegment game
        loadCache getInst
        forever $ do
            sp <- use $ config . speed
            if sp > 0 then do
                mkStep >>= checkInt
              else liftIO $ threadDelay 20000
            st <- use id
            liftIO $ modifyMVar_ pmvar $ const $ return st
            join $ liftIO $ modifyMVar changeState $ \m -> return (return (), m)
    drawWithFrameBuffer addChange (\r -> modifyMVar_ (st ^. config . interruptRequest) $ return . (++[r])) pmvar $ return ()

createBuff :: BufferData a -> Frequency -> IO Buffer
createBuff (BufferData m fmt f) x = do
    [b] <- genObjectNames 1
    bufferData b $= BufferData m fmt (x*f)
    return b

