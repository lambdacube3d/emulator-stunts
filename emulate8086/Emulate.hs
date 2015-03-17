module Emulate where

import Data.Word
import Data.Bits hiding (bit)
import Data.List
import Data.Monoid
import qualified Data.ByteString as BS
import qualified Data.IntMap.Strict as IM
import qualified Data.Vector.Storable as US
import qualified Data.Vector.Storable.Mutable as U
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens as Lens
import Control.Concurrent
import Control.Exception
import Control.DeepSeq
import System.Directory

import Hdis86

import Helper
import Edsl
import MachineState
import DeBruijn
import Dos

--------------------------------------


getFetcher :: Machine (Int -> Metadata)
getFetcher = do
    v <- liftIO $ US.unsafeFreeze heap''
    (start, bs) <- use $ config . gameexe
    ip_ <- use' ip
    cs_ <- use' cs
    inv <- use $ config . invalid
    let f ips
            | 0 <= i && i < BS.length bs = if x == x' then x else error $ "getFetcher: " ++ show ((cs_,ip_), ips)
            | otherwise = x
          where
            x = head . disassembleMetadata disasmConfig . BS.pack . take 7 . map fromIntegral . US.toList $ US.drop ips v
            x' = head . disassembleMetadata disasmConfig . BS.drop i $ bs
            i = ips - start
    return f

-- TODO: tye the knot
evalBlocks cs' ip' e = case IM.lookup (fromIntegral ip') e of
    Just x -> do
        evalExpM mempty x
{- TODO
        cs_ <- use cs
        ip_ <- use ip
        when (cs_ == cs') $ do
            checkInt 1
            evalBlocks cs' ip_ e
-}
    Nothing -> return ()

fetchBlock_' ca f cs ss es ds ip = do
    let (n, r, e) = fetchBlock_ (f) cs ss es ds ip
    _ <- liftIO $ evaluate n
    return $ Compiled cs ss es ds n r $ do
        _ <- evalBlocks cs ip e
        b <- use' showReads
        when b $ do
            off <- use' showOffset
            liftIO $ forM_ r $ \(beg, end) -> forM_ [max 0 $ beg - off .. min (320 * 200 - 1) $ end - 1 - off] $ \i -> do
                x <- U.unsafeRead showBuffer i
                U.unsafeWrite showBuffer i $ x .|. 0xff000000

fetchBlock :: Cache -> Machine CacheEntry
fetchBlock ca = do
    es_ <- use' es
    ds_ <- use' ds
    fetchBlock'' (Just es_) (Just ds_) ca

fetchBlock'' es ds ca = do
    cs_ <- use' cs
    ss_ <- use' ss
    ip_ <- use' ip
    f <- getFetcher
    fetchBlock_' ca f cs_ ss_ es ds ip_

mkStep :: Machine Int
mkStep = do
    ip_ <- use' ip
    cs_ <- use' cs

    let ips = segAddr cs_ ip_
        compile fe = do
            entry@(Compiled _ _ _ _ n reg ch) <- mdo
                e <- fe ca
                ca <- use cache
                return e
            when (cacheOK ips) $ cache %= IM.insert ips entry
            ch
            return n

    cv <- use $ cache . at ips
    case cv of
     Just v -> case v of
      Compiled cs' ss' es' ds' n len m -> do
        cs'' <- use' cs
        when (cs' /= cs'') $ error "cs differs"
        ss'' <- use' ss
        when (ss' /= ss'') $ error "ss differs"
        es'' <- use' es
        ds'' <- use' ds
        let f a b = if a == Just b then a else Nothing
        if (maybe False (/= es'') es' || maybe False (/=ds'') ds') then do
            trace_ "recompile"
            compile $ fetchBlock'' (f es' es'') (f ds' ds'')
          else do
            m
            return n
      BuiltIn m -> do
        m
        return 1
      DontCache _ -> do
        Compiled _ _ _ _ n _ ch <- fetchBlock mempty
        ch
        return n
     Nothing -> compile fetchBlock

-- ad-hoc hacking for stunts!
cacheOK ips = ips < 0x39000 -- || ips >= 0x3a700

disasmConfig = Config Intel Mode16 SyntaxIntel 0

type MachinePart' a = (Machine a, a -> Machine ())

evalPart_ :: Part_ e a -> MachinePart'' a
evalPart_ = \case
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
    Low AX -> al
    Low BX -> bl
    Low CX -> cl
    Low DX -> dl
    High AX -> ah
    High BX -> bh
    High CX -> ch
    High DX -> dh
    CF -> carryF
    PF -> parityF
    ZF -> zeroF
    SF -> signF
    IF -> interruptF
    DF -> directionF
    OF -> overflowF
    Edsl.Flags -> flags
    DXAX -> dxax



data Env :: List * -> * where
  Empty :: Env Nil
  Push  :: { getPushEnv :: Env env, getPushVal :: t } -> Env (Con t env)

prj :: Var env t -> Env env -> t
prj VarZ = getPushVal
prj (VarS ix) = prj ix . getPushEnv

type Machine' e = ReaderT (Env e) Machine

---------------------------------

iterateM 0 _ a = return a
iterateM n f a = f a >>= iterateM (n-1) f

iff x y True = x
iff x y _ = y

evalExp' :: Exp a -> Machine a
evalExp' e = flip runReaderT Empty $ evalExp (convExp e)

evalExp :: EExp e a -> Machine' e a
evalExp x = ReaderT $ \e -> liftIO $ runReaderT (evalExp_ x) e

type Machine'' e = ReaderT (Env e) IO

pushVal' :: Machine'' (Con b e) a -> b -> Machine'' e a
pushVal' m v = ReaderT $ runReaderT m . (`Push` v)

evalExp_ :: EExp e a -> Machine'' e a
evalExp_ = evalExp where
  evalExp :: EExp e a -> Machine'' e a
  evalExp = \case
    Var' ix -> reader $ prj ix
    Let' e f -> evalExp e >>= pushVal' (evalExp f)
    Iterate' n f a -> evalExp n >>= \i -> evalExp a >>= iterateM i (pushVal' (evalExp f))

    C' a -> return a
    Get' p -> case p of
        Heap16 e -> evalExp e >>= liftIO . getWordAt (Program e)
        Heap8 e -> evalExp e >>= liftIO . getByteAt (Program e)
        p -> liftIO $ fst $ evalPart_ p

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
    QuotRem' a b -> liftM2 quotRem (evalExp a) (evalExp b)
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
    SegAddr' (C' i) f -> (fromIntegral i `shiftL` 4 +) . fromIntegral <$> evalExp f
    SegAddr' e f -> liftM2 segAddr (evalExp e) (evalExp f)
    Convert' e -> fromIntegral <$> evalExp e    

    Tuple' a b -> liftM2 (,) (evalExp a) (evalExp b)
    Fst' p -> fst <$> evalExp p
    Snd' p -> snd <$> evalExp p

evalExpM :: Cache -> ExpM Jump' -> Machine ()
evalExpM ca e = flip runReaderT Empty $ evalEExpM ca (convExpM e) >>= \(JumpAddr c i) -> cs ..= c >> ip ..= i

evalEExpM :: Cache -> EExpM e a -> Machine' e a
evalEExpM ca = evalExpM
  where
  evalExpM :: EExpM e a -> Machine' e a
  evalExpM = \case
    LetM' e f -> evalExp e >>= pushVal (evalExpM f)
    Set' p e' c -> case p of 
        Heap16 e -> join (lift <$> liftM2 (setWordAt $ Program e) (evalExp e) (evalExp e')) >> evalExpM c
        Heap8 e -> join (lift <$> liftM2 (setByteAt $ Program e) (evalExp e) (evalExp e')) >> evalExpM c
        p -> evalExp e' >>= (evalPart_ p ..=) >> evalExpM c
{- temporarily comment out
    Jump'' (C' c) (C' i) | Just (Compiled cs' ss' _ _ _ _ m) <- IM.lookup (segAddr c i) ca
                       , cs' == c -> lift $ do
                            checkInt 1
                            ip .= i
                            m
-}
    Jump'' c i -> liftM2 JumpAddr (evalExp c) (evalExp i)
    Stop' a -> return a

    IfM' b x y -> evalExp b >>= iff (evalExpM x) (evalExpM y)

    Input' a f -> evalExp a >>= lift . input >>= pushVal (evalExpM f)

    Replicate' n b e f -> evalExp n >>= replicateM' (evalExp b) (evalExpM e) >>= pushVal (evalExpM f)

    Output' a b c -> join (lift <$> liftM2 output' (evalExp a) (evalExp b)) >> evalExpM c

replicateM' _ _ 0 = return 0
replicateM' b m n = do
    () <- m
    y <- b
    let !n' = n - 1
    if y then replicateM' b m n' else return n'

pushVal :: Machine' (Con b e) a -> b -> Machine' e a
pushVal m v = ReaderT $ runReaderT m . (`Push` v)

checkInt n = do
  ns <- use $ config . stepsCounter
  let !ns' = ns + n
  config . stepsCounter .= ns'
  let ma = complement 0xff
  when (ns' .&. ma /= ns .&. ma) $ do
    i <- use' interruptF
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
              when (id == cc) $ interrupt 0x08
           AskKeyInterrupt scancode -> do
              config . keyDown .= scancode
              interrupt 0x09

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


loadCache getInst = do
    trace_ "Loading cache"
    cf <- liftIO readCache
--    when (not $ unique [segAddr cs $ fromIntegral ip | (fromIntegral -> cs, ips) <- IM.toList cf, ip <- IS.toList ips]) $ error "corrupt cache"
    let fromIntegral' :: Int -> Maybe Word16
        fromIntegral' x | x == -1 = Nothing
        fromIntegral' x = Just $ fromIntegral x
        fromIntegral_ :: Int -> Word16
        fromIntegral_ = fromIntegral
    cf' <- cf `deepseq` mdo
        cf' <- forM (IM.toList cf) $ \(ip, (fromIntegral_ -> cs, fromIntegral_ -> ss, fromIntegral' -> es, fromIntegral' -> ds)) ->
                 (,) ip <$> fetchBlock_' ca (head . disassembleMetadata disasmConfig . getInst) cs ss es ds (fromIntegral $ ip - cs ^. paragraph)
        ca <- use cache
        return cf'
    cache %= IM.union (IM.fromList cf')
    trace_ "cache loaded"

readCache :: IO (IM.IntMap (Int,Int,Int,Int))
readCache = do
    let newCache = do
        writeFile cacheFile "fromList []"
        return mempty
    b <- doesFileExist cacheFile
    if not b then newCache else do
        x <- readFile cacheFile
        case x `deepseq` reads x of
            [(v,"")] -> return v
            _ -> do
                putStrLn "outdated cache file deleted!"
                newCache


