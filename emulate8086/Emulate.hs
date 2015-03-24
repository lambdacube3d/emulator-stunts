module Emulate where

import Data.Word
import Data.Bits hiding (bit)
import Data.List
import Data.Monoid
import Data.Maybe
import qualified Data.ByteString as BS
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Vector.Storable as US
import qualified Data.Vector.Storable.Mutable as U
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Concurrent
import Control.Exception
import Control.DeepSeq
import System.Directory
--import Debug.Trace
import Prelude

import Helper
import Edsl
import DeBruijn
import MachineState
import Dos (input, output')
import CPU

--------------------------------------

interrupt :: Word8 -> Machine ()
interrupt v = do
    use' flags >>= push
    use' cs >>= push
    use' ip >>= push
    interruptF ..= False
    getWordAt System (ad + 2) >>= (cs ..=)
    getWordAt System ad >>= (ip ..=)
  where
    ad = 4 * fromIntegral v

getFetcher :: Machine Fetcher
getFetcher = do
    v <- US.unsafeFreeze heap''
    (start, bs) <- use'' gameexe
    ip_ <- use' ip
    cs_ <- use' cs
    let f ips
            | 0 <= i && i < BS.length bs = {-if x /= x' then error $ "getFetcher: " ++ show ((cs_,ip_), ips) else-} x'
            | otherwise = x
          where
            x = disassemble . BS.pack . map fromIntegral . US.toList $ US.slice ips 7 v
            x' = disassemble . BS.drop i $ bs
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
    jumps <- use' cache2
    let (n, r, e) = fetchBlock_ (\i -> fromMaybe mempty $ IM.lookup i jumps) f cs ss es ds ip
    _ <- evaluate n
    let !cc = spTrans $ convExpM $ snd $ head $ IM.toList e
        !dd = evalExpM mempty cc
    return $ Compiled (not $ highAddr $ segAddr cs ip) cs ss es ds n r $ do
        _ <- dd
        b <- use' showReads
        when b $ do
            off <- use' showOffset
            forM_ r $ \(beg, end) -> forM_ [max 0 $ beg - off .. min (320 * 200 - 1) $ end - 1 - off] $ \i -> do
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
    ips <- liftM2 segAddr (use' cs) (use' ip)
    cv <- IM.lookup ips <$> use' cache
    case cv of
     Just v -> case v of
      Compiled _ cs' ss' es' ds' n len m -> do
        when debug $ do
            cs'' <- use' cs
            when (cs' /= cs'') $ error "cs differs"
            ss'' <- use' ss
            when (ss' /= ss'') $ error "ss differs"
        es'' <- use' es
        ds'' <- use' ds
        if (maybe False (/= es'') es' || maybe False (/=ds'') ds') then do
            trace_ "recompile"
            let f a b = if a == Just b then a else Nothing
            compile $ fetchBlock'' (f es' es'') (f ds' ds'')
          else do
            m
            return n
      BuiltIn m -> do
        m
        return 1
      DontCache _ -> do
        Compiled _ _ _ _ _ n _ ch <- fetchBlock mempty
        ch
        return n
     Nothing -> do
        compile fetchBlock

compile :: (Cache -> IO CacheEntry) -> Machine Int
compile fe = do
    ip_ <- use' ip
    cs_ <- use' cs
    let ips = segAddr cs_ ip_
    entry@(Compiled b _ _ _ _ n reg ch) <- do
        let ca = mempty
        e <- fe ca
--                ca <- use'' cache
        return e
    when (cacheOK ips || not b) $ cache .%= IM.insert ips entry
    ch
    return n

-- ad-hoc hacking for stunts!
cacheOK ips = ips < 0x39000 || ips >= 0x3a700
highAddr ips = ips >= 0x3a700

type MachinePart' a = (Machine a, a -> Machine ())



evalPart_, evalPart__ :: Part_ e a -> MachinePart'' a
evalPart_ = {-trace "." . -} evalPart__
evalPart__ = \case
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
    AL -> al
    BL -> bl
    CL -> cl
    DL -> dl
    AH -> ah
    BH -> bh
    CH -> ch
    DH -> dh
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

type Machine' e = ReaderT (Env e) IO

---------------------------------

iterateM 0 _ a = return a
iterateM n f a = f a >>= iterateM (n-1) f

iff x y True = x
iff x y _ = y

pushVal :: Machine' (Con b e) a -> b -> Machine' e a
pushVal (ReaderT m) v = ReaderT $ \x -> m (x `Push` v)

evalExp :: EExp e a -> Machine' e a
evalExp = \case
    Var ix -> let f = prj ix in reader f
--    Let (C e) f -> pushVal (evalExp f) e
    Let e (DB f) -> evalExp e >>= pushVal (evalExp f)
    Iterate n (DB f) a -> evalExp n >>= \i -> evalExp a >>= iterateM i (pushVal (evalExp f))

    C a -> return a
    Get p -> case p of
--        Heap16 (C e) -> lift $ getWordAt (Program $ C e) e
        Heap16 e -> evalExp e >>= lift . getWordAt (Program e)
--        Heap8 (C e) -> lift $ getByteAt (Program $ C e) e
        Heap8 e -> evalExp e >>= lift . getByteAt (Program e)
        p -> let x = fst $ evalPart_ p in lift x

--    If (C b) x y -> if b then evalExp x else evalExp y
    If b (C x) (C y) -> iff x y <$> evalExp b
    If b x y -> evalExp b >>= iff (evalExp x) (evalExp y)
    Eq (C x) y -> (==x) <$> evalExp y
    Eq y (C x) -> (==x) <$> evalExp y
    Eq x y -> liftM2 (==) (evalExp x) (evalExp y)

    Not a -> complement <$> evalExp a
    ShiftL a -> (`shiftL` 1) <$> evalExp a
    ShiftR a -> (`shiftR` 1) <$> evalExp a
    RotateL a -> (`rotateL` 1) <$> evalExp a
    RotateR a -> (`rotateR` 1) <$> evalExp a
    Sub (C a) b -> (a-) <$> evalExp b
    Sub b (C a) -> (+(-a)) <$> evalExp b
    Sub a b -> liftM2 (-) (evalExp a) (evalExp b)
    Add (C a) b -> (+a) <$> evalExp b
    Add b (C a) -> (+a) <$> evalExp b
    Add a b -> liftM2 (+) (evalExp a) (evalExp b)
    Mul a b -> liftM2 (*) (evalExp a) (evalExp b)
    QuotRem a b -> liftM2 quotRem (evalExp a) (evalExp b)
    And (C a) b -> (.&. a) <$> evalExp b
    And b (C a) -> (.&. a) <$> evalExp b
    And a b -> liftM2 (.&.) (evalExp a) (evalExp b)
    Or (C a) b -> (.|. a) <$> evalExp b
    Or b (C a) -> (.|. a) <$> evalExp b
    Or  a b -> liftM2 (.|.) (evalExp a) (evalExp b)
    Xor (C a) b -> (xor a) <$> evalExp b
    Xor b (C a) -> (xor a) <$> evalExp b
--    Xor a b | a == b -> return zeroBits
    Xor a b -> liftM2 xor (evalExp a) (evalExp b)

    EvenParity e -> even . popCount <$> evalExp e

--    SegAddr (C i) (C f) -> return $ segAddr i f
    SegAddr (C i) f -> (fromIntegral i `shiftL` 4 +) . fromIntegral <$> evalExp f
    SegAddr e f -> liftM2 segAddr (evalExp e) (evalExp f)
    Convert e -> fromIntegral <$> evalExp e    

    Tuple a b -> liftM2 (,) (evalExp a) (evalExp b)
    Fst p -> fst <$> evalExp p
    Snd p -> snd <$> evalExp p


--evalExpM :: Cache -> ExpM Jump' -> Machine ()
evalExpM ca e = let !m = evalEExpM ca e in runReaderT m Empty >>= \(JumpAddr c i) -> cs ..= c >> ip ..= i

evalEExpM :: Cache -> EExpM e a -> Machine' e a
evalEExpM ca = evalExpM
  where
  evalExpM :: EExpM e a -> Machine' e a
  evalExpM = \case
--    LetM(C e) f -> pushVal (evalExpM f) e
    LetM e (DBM f) -> evalExp e >>= pushVal (evalExpM f)
--    LetMC e f g -> evalExp e >>= pushVal (evalExpM f) >> evalExpM g
    Set p (C e') c -> case p of
        Heap16 (C e_) -> lift (setWordAt (Program $ C e_) e_ e') >> evalExpM c
        Heap16 e -> evalExp e >>= \e_ -> lift (setWordAt (Program e) e_ e') >> evalExpM c
--        Heap8 (C e_) -> lift (setByteAt (Program $ C e_) e_ e') >> evalExpM c
        Heap8 e -> evalExp e >>= \e_ -> lift (setByteAt (Program e) e_ e') >> evalExpM c
        p -> let x = snd $ evalPart_ p in lift (x e') >> evalExpM c
    Set p e' c -> case p of 
        Heap16 (C e_) -> evalExp e' >>= \e_' -> lift (setWordAt (Program $ C e_) e_ e_') >> evalExpM c
        Heap16 e -> evalExp e >>= \e_ -> evalExp e' >>= \e_' -> lift (setWordAt (Program e) e_ e_') >> evalExpM c
--        Heap8 (C e_) -> evalExp e' >>= \e_' -> lift (setByteAt (Program $ C e_) e_ e_') >> evalExpM c
        Heap8 e -> evalExp e >>= \e_ -> evalExp e' >>= \e_' -> lift (setByteAt (Program e) e_ e_') >> evalExpM c
        p -> let x = snd $ evalPart_ p in evalExp e' >>= lift . x >> evalExpM c
{- temporarily comment out
    Jump'' (C c) (C i) | Just (Compiled cs' ss' _ _ _ _ m) <- IM.lookup (segAddr c i) ca
                       , cs' == c -> lift $ do
                            checkInt 1
                            ip .= i
                            m
-}
    Ret (C a) -> return a
    Ret a -> evalExp a

    IfM (C b) x y -> if b then evalExpM x else evalExpM y
    IfM b x y -> evalExp b >>= iff (evalExpM x) (evalExpM y)

    IfM' b x y (DBM f) -> evalExp b >>= iff (evalExpM x) (evalExpM y) >>= pushVal (evalExpM f)

    Replicate n (C True) e (DBM f) -> evalExp n >>= \n -> replicateM_ (fromIntegral n) (evalExpM e) >> pushVal (evalExpM f) (0 `asTypeOf` n)
    Replicate n b e (DBM f) -> evalExp n >>= replicateM' (evalExp b) (evalExpM e) >>= pushVal (evalExpM f)

    Input a (DBM f) -> evalExp a >>= lift . input >>= pushVal (evalExpM f)

    Output a b c -> join (lift <$> liftM2 output' (evalExp a) (evalExp b)) >> evalExpM c

    Trace s c -> lift (trace_ s) >> evalExpM c

    Call c i _ _ -> liftM2 JumpAddr (evalExp c) (evalExp i)
    Jump' Nothing (C c) (C i) -> return $ JumpAddr c i
    Jump' Nothing c i -> liftM2 JumpAddr (evalExp c) (evalExp i)
    Jump' (Just ((cs, ip), table, fallback)) cs' ip' -> let
        table' = IM.map evalExpM table
        end = evalExpM fallback
        in do
            cs'' <- evalExp cs'
            ip'' <- evalExp ip'
            let ip''' = fromIntegral ip''
            if cs /= cs'' then end else
              case IM.lookup ip''' table' of
                Just m -> m
                Nothing -> do
                    lift $ cache2 .%= alter' (segAddr cs ip) (IS.insert ip''')
                    end

alter' i f = IM.alter (Just . maybe (f mempty) f) i

replicateM' _ _ n@0 = return n
replicateM' b m n = do
    _ <- m
    y <- b
    let !n' = n - 1
    if y then replicateM' b m n' else return n'

checkInt changeState cycles cont n = do
  ns <- use' stepsCounter
  let !ns' = ns + n
  stepsCounter ..= ns'
  let ma = complement 0xff
  if (ns' .&. ma == ns .&. ma) then cont else do
    join $ modifyMVar changeState $ \m -> return (return (), m)
    i <- use' interruptF
    when i $ do
        mask <- use'' intMask
        ivar <- use'' interruptRequest
        ints <- takeMVar ivar
        cc <- use'' counter
        let ibit = \case
                AskTimerInterrupt{} -> 0
                AskKeyInterrupt{}   -> 1
            getFirst [] = (return (), [])
            getFirst (x:xs) = case x of
               AskTimerInterrupt c | c /= cc -> getFirst xs
               _ | testBit mask $ ibit x -> (m, x:xs') where (m, xs') = getFirst xs
               AskTimerInterrupt _ -> (timerOn ...= False >> interrupt 0x08, xs)
               AskKeyInterrupt scancode -> (keyDown ...= scancode >> interrupt 0x09, xs)
            (now, later) = getFirst ints
        putMVar ivar later
        now
    when (ns' < cycles) cont

--------------------------------------------------------------------------------

cacheFile = "cache.txt"

adjustCache = do
    trace_ "adjust cache"
    ch <- use' cache
    jumps <- use' cache2
    let p (Compiled True cs ss es ds _ _ _) = Just (cs, ss, es, ds)
        p _ = Nothing

    (cf, jumps') <- read <$> readFile cacheFile
    let cf' = ( foldr (uncurry IM.insert) cf
                [(i, (cs, ss, alter' es, alter' ds)) | (i, p -> Just t@(cs, ss, es, ds)) <- IM.toList ch ]
              , IM.union jumps jumps'
              )
    cf' `deepseq` writeFile cacheFile (show cf')
  where
    alter' :: Maybe Word16 -> Int
    alter' (Just i) = fromIntegral i
    alter' Nothing = -1


loadCache getInst = do
    trace_ "Loading cache..."
    (cf, jumps) <- readCache
--    when (not $ unique [segAddr cs $ fromIntegral ip | (fromIntegral -> cs, ips) <- IM.toList cf, ip <- IS.toList ips]) $ error "corrupt cache"
    let fromIntegral' :: Int -> Maybe Word16
        fromIntegral' x | x == -1 = Nothing
        fromIntegral' x = Just $ fromIntegral x
        fromIntegral_ :: Int -> Word16
        fromIntegral_ = fromIntegral
    cf' <- cf `deepseq` do
        let ca = mempty :: Cache
        cf' <- forM (IM.toList cf) $ \(ip, (fromIntegral_ -> cs, fromIntegral_ -> ss, fromIntegral' -> es, fromIntegral' -> ds)) ->
                 (,) ip <$> fetchBlock_' ca (disassemble . getInst) cs ss es ds (fromIntegral $ ip - segAddr cs 0)
--        ca <- use'' cache
        return cf'
    cache .%= IM.union (IM.fromList cf')
    cache2 .%= IM.unionWith IS.union jumps
    trace_' "ok"

type CacheFile = (IM.IntMap (Int,Int,Int,Int), Cache2)

readCache :: IO CacheFile
readCache = do
    let newCache = do
            writeFile cacheFile $ show (mempty :: CacheFile)
            return mempty
    b <- doesFileExist cacheFile
    if not b then newCache else do
        x <- readFile cacheFile
        case x `deepseq` reads x of
            [(v,"")] -> return v
            _ -> do
                putStrLn "outdated cache file deleted!"
                newCache


