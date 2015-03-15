import Sound.ALUT
import Control.Concurrent

main :: IO ()
main = withProgNameAndArgs runALUT $ \_ _ -> do
    bData <- createBufferData (Sine 440 0 0.1)
    buff <- createBuff bData 1
    [source] <- genObjectNames 1
    loopingMode source $= Looping

    stop [source]
    buffer source $= Just buff
    sourceGain source $= 1
    play [source]
    threadDelay 100000
    pitch source $= 0.5
    threadDelay 1000000

createBuff :: BufferData a -> Frequency -> IO Buffer
createBuff (BufferData m fmt f) x = do
    [b] <- genObjectNames 1
    bufferData b $= BufferData m fmt (x*f)
    return b





