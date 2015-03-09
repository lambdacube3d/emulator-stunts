{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RebindableSyntax #-}
module Edsl
    ( compileInst, execInstruction'
    , nextAddr
    , reorderExp
    , iret
    , interrupt
    , Part (..), Exp (..), ExpM (..), Halt (..)
    , memIndex
    , addressOf, addressOf'
    ) where

import Data.List
import Data.Maybe
import Data.Int
import Data.Word
import Data.Bits
import Data.Monoid
import Control.Applicative
import Control.Monad ((>=>))
import Control.Lens
import Prelude hiding ((>>), return)

import Hdis86 hiding (wordSize)
import Hdis86.Incremental

import Helper

----------------------------------------

data Halt
    = CleanHalt
    | Interr
    | Err String
  deriving Show

infixr 1 >>, `Seq`
(>>) :: ExpM () -> ExpM () -> ExpM ()
(>>) = (<>)

return :: () -> ExpM ()
return () = mempty

ifThenElse :: Bool -> a -> a -> a
ifThenElse True a _ = a
ifThenElse _ _ b = b

instance Monoid (ExpM ()) where
    Nop `mappend` e   = e
    e   `mappend` Nop = e
    Seq a b `mappend` e  = Seq a (b `mappend` e)
    e1      `mappend` e2 = Seq e1 e2
    mempty = Nop

data Part a where
    Heap8  :: Exp Int -> Part Word8
    Heap16 :: Exp Int -> Part Word16

    IP :: Part Word16
    AX, BX, CX, DX, SI, DI, BP, SP :: Part Word16
    Es, Ds, Ss, Cs :: Part Word16
    CF, PF, AF, ZF, SF, IF, DF, OF :: Part Bool

    Flags :: Part Word16
    DXAX :: Part Word32

    Low, High :: Part Word16 -> Part Word8

data ExpM a where
    Seq :: ExpM () -> ExpM () -> ExpM ()

    IfM :: Exp Bool -> ExpM () -> ExpM () -> ExpM ()
    QuotRem :: Integral a => Exp a -> Exp a -> ExpM () -> ((Exp a, Exp a) -> ExpM ()) -> ExpM ()

    LetM :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
    Replicate :: Exp Int -> ExpM () -> ExpM ()

    Nop :: ExpM ()
    Error :: Halt -> ExpM ()
    Trace :: String -> ExpM ()
    Set :: Part a -> Exp a -> ExpM ()
    Mod :: Part a -> (Exp a -> Exp a) -> ExpM ()
    Input :: Exp Word16 -> (Exp Word16 -> ExpM ()) -> ExpM ()
    Output :: Exp Word16 -> Exp Word16 -> ExpM ()
    CheckInterrupt :: Int -> ExpM ()
    Interrupt :: Exp Word8 -> ExpM ()

data Exp a where
    C :: a -> Exp a
    Let :: Exp a -> (Exp a -> Exp b) -> Exp b
    Tuple :: Exp a -> Exp b -> Exp (a, b)
    Fst :: Exp (a, b) -> Exp a
    Snd :: Exp (a, b) -> Exp b
    Iterate :: Exp Int -> (Exp a -> Exp a) -> Exp a -> Exp a
    If :: Exp Bool -> Exp a -> Exp a -> Exp a

    Get :: Part a -> Exp a

    Eq :: Eq a => Exp a -> Exp a -> Exp Bool
    Sub, Add, Mul :: Num a => Exp a -> Exp a -> Exp a
    And, Or, Xor :: Bits a => Exp a -> Exp a -> Exp a
    Not, ShiftL, ShiftR, RotateL, RotateR :: Bits a => Exp a -> Exp a
    Bit :: Bits a => Int -> Exp a -> Exp Bool
    SetBit :: Bits a => Int -> Exp Bool -> Exp a -> Exp a
    HighBit :: FiniteBits a => Exp a -> Exp Bool
    SetHighBit :: FiniteBits a => Exp Bool -> Exp a -> Exp a
    EvenParity :: Exp Word8 -> Exp Bool

    Signed :: AsSigned a => Exp a -> Exp (Signed a)
    Extend :: Extend a => Exp a -> Exp (X2 a)
    Convert :: (Integral a, Num b) => Exp a -> Exp b
    SegAddr :: Exp Word16 -> Exp Word16 -> Exp Int

trace_ = Trace
undefBool = C False
unTup x = (Fst x, Snd x)

instance Num Bool where
    (+) = xor
    (-) = xor
    (*) = (&&)
    abs = id
    signum = id
    fromInteger = toEnum . fromInteger . (`mod` 2)
    
instance Real Bool where
    toRational = toRational . fromEnum

instance Integral Bool where
    toInteger = toInteger . fromEnum
    a `quotRem` 1 = (a, 0)
    a `quotRem` 0 = error $ "quotRem " ++ show a ++ " 0 :: Bool"


ifM (C c) a b = if c then a else b
ifM x a b = IfM x a b

letM (C c) f = f (C c)
letM x f = LetM x f

add (C c) (C c') = C $ c + c'
add a b = Add a b

and' (C c) (C c') = C $ c .&. c'
and' a b = And a b

not' (C c) = C $ complement c
not' b = Not b

eq' (C c) (C c') = C $ c == c'
eq' a b = Eq a b

when :: Bool -> ExpM () -> ExpM ()
when b x = if b then x else mempty

when' :: Exp Bool -> ExpM () -> ExpM ()
when' b x = ifM b x mempty


--------------------------------------------------------------------------------

-- get / set / mod / neutral / Interrupt

--data

reorderExp :: ExpM () -> ExpM ()
reorderExp = -- snd . foldrExp f (AGet, Nop) . 
    groupInterrupts 0
{-
  where

        
    IfM :: Exp Bool -> ExpM () -> ExpM () -> ExpM ()
    QuotRem :: Integral a => Exp a -> Exp a -> ExpM () -> ((Exp a, Exp a) -> ExpM ()) -> ExpM ()

    LetM :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
    Replicate :: Exp Int -> ExpM () -> ExpM ()

    Set :: Part a -> Exp a -> ExpM ()
    Mod :: Part a -> (Exp a -> Exp a) -> ExpM ()

    CheckInterrupt :: Int -> ExpM ()
    Interrupt :: Exp Word8 -> ExpM ()
        

    f (Mod IP f) (AGet, b) = (AMod f, b)
    f (Set IP v) (AGet, b) = (ASet v, b)
    f a (AGet, b) | isInterr a =
    f a (AGet, b) | hasGet a = (AGet, a `Seq` b)  --
    f (Mod IP _) (ASet v, b) = (ASet v, b)
    f (Set IP _) (ASet v, b) = (ASet v, b)
    f a (ASet v, b) | isInterr a =
    f a (ASet v, b) | hasGet a =
    f (Mod IP g) (AMod f, b) = (AMod $ f . g, b)
    f (Set IP v) (AMod f, b) = (ASet $ f v, b)
    f a (AMod f, b) | isInterr a =
    f a (AMod f, b) | hasGet a =

    f a (st, b) = (st, a `Seq` b)
-}
foldrExp :: (ExpM () -> a -> a) -> a -> ExpM () -> a
foldrExp f x (Seq a b) = f a (foldrExp f x b)
foldrExp f x y = f y x

groupInterrupts n = \case
    Seq (CheckInterrupt n') b -> groupInterrupts (n + n') b
    Seq i@(Interrupt _) e -> checkInterrupt n `Seq` i `Seq` groupInterrupts 0 e
    Seq a b -> a `Seq` groupInterrupts n b
    CheckInterrupt n' -> CheckInterrupt $ n + n'
    e -> e `Seq` checkInterrupt n

checkInterrupt 0 = Nop
checkInterrupt n = CheckInterrupt n

nextAddr :: ExpM () -> Word16 -> Maybe Word16
nextAddr e = case e of
    LetM e f -> nextAddr (f e)
    Seq a b -> nextAddr a >=> nextAddr b
    Nop -> Just
    Trace _ -> Just
    CheckInterrupt _ -> Just  -- !
    Output _ _ -> Just

    Set IP _ -> const Nothing
    Set Cs _ -> const Nothing
    Set _ _ -> Just

    Mod IP f -> \x -> case f (C x) of
        Add (C i) (C x) | i >= 0 && i < 8 -> Just $ i + x
        _ -> Nothing
    Mod Cs _ -> const Nothing
    Mod _ _ -> Just

    _ -> const Nothing

--------------------------------------------------------------------------------

sizeByte_ i@Inst{..}
    | inOpcode `elem` [Icbw, Icmpsb, Imovsb, Istosb, Ilodsb, Iscasb, Ilahf] = 1
    | inOpcode `elem` [Icwd, Icmpsw, Imovsw, Istosw, Ilodsw, Iscasw] = 2
    | inOpcode == Iout  = fromJust $ operandSize $ inOperands !! 1
    | otherwise = fromMaybe (error $ "size: " ++ show i) $ listToMaybe $ catMaybes $ map operandSize inOperands

operandSize = \case
    Reg (Reg16 _)   -> Just 2
    Reg (Reg8 _ _)  -> Just 1
    Mem (Memory Bits8 _ _ _ _)  -> Just 1
    Mem (Memory Bits16 _ _ _ _) -> Just 2
    Imm (Immediate Bits8 v)  -> Just 1
    Imm (Immediate Bits16 v) -> Just 2
    _ -> Nothing

segOf = \case
    RegIP     -> Cs
    Reg16 RSP -> Ss
    Reg16 RBP -> Ss
    _         -> Ds

getReg :: Register -> Exp Word16
getReg = \case
    RegNone -> C 0
    r -> Get $ reg r

reg :: Register -> Part Word16
reg = \case
    Reg16 r -> case r of
        RAX -> AX
        RBX -> BX
        RCX -> CX
        RDX -> DX
        RSI -> SI
        RDI -> DI
        RBP -> BP
        RSP -> SP
    RegSeg r -> case r of
        ES -> Es
        DS -> Ds
        SS -> Ss
        CS -> Cs
    RegIP -> IP
--    RegNone -> Immed $ C 0

segAddr_ :: Part Word16 -> Exp Word16 -> Exp Int
segAddr_ seg off = SegAddr (Get seg) off

ips, sps :: Exp Int
ips = segAddr_ Cs $ Get IP
sps = segAddr_ Ss $ Get SP

addressOf :: Maybe Segment -> Memory -> Exp Int
addressOf segmentPrefix m
    = segAddr_ (maybe (segOf $ mBase m) (reg . RegSeg) segmentPrefix) (addressOf' m)

addressOf' :: Memory -> Exp Word16
addressOf' (Memory _ r r' 0 i) = Add (C $ imm i) $ Add (getReg r) (getReg r')

getByteOperand segmentPrefix = \case
    Imm (Immediate Bits8 v) -> C $ fromIntegral v
    Hdis86.Const (Immediate Bits0 0) -> C 1 -- !!!
    x -> Get $ byteOperand segmentPrefix x

byteOperand :: Maybe Segment -> Operand -> Part Word8
byteOperand segmentPrefix x = case x of
    Reg r -> case r of
        Reg8 r L -> case r of
            RAX -> Low AX
            RBX -> Low BX
            RCX -> Low CX
            RDX -> Low DX
        Reg8 r H -> case r of
            RAX -> High AX
            RBX -> High BX
            RCX -> High CX
            RDX -> High DX
    Mem m -> Heap8 $ addressOf segmentPrefix m
--    Imm (Immediate Bits8 v) -> Immed $ C $ fromIntegral v
--    Hdis86.Const (Immediate Bits0 0) -> Immed $ C 1 -- !!!

getWordOperand segmentPrefix = \case
    Imm i  -> C $ imm' i
    Jump i -> Add (C $ imm i) (Get IP)
    x -> Get $ wordOperand segmentPrefix x

wordOperand :: Maybe Segment -> Operand -> Part Word16
wordOperand segmentPrefix x = case x of
    Reg r  -> reg r
    Mem m  -> Heap16 $ addressOf segmentPrefix m
--    Imm i  -> Immed $ C $ imm' i
--    Jump i -> Immed $ Add (C $ imm i) (Get IP)


imm = fromIntegral . iValue
-- patched version
imm' (Immediate Bits8 i) = fromIntegral (fromIntegral i :: Int8)
imm' i = imm i

memIndex r = Memory undefined (Reg16 r) RegNone 0 $ Immediate Bits0 0

stackTop :: Part Word16
stackTop = Heap16 sps

push :: Exp Word16 -> ExpM ()
push x = do
    Mod SP $ Add $ C $ -2
    Set stackTop x

pop :: (Exp Word16 -> ExpM ()) -> ExpM ()
pop cont = LetM (Get stackTop) $ \x -> do
    Mod SP $ Add $ C 2
    cont x

move a b = Set a $ Get b

execInstruction' :: Metadata -> ExpM ()
execInstruction' mdat@Metadata{mdInst = i@Inst{..}}
  = case filter nonSeg inPrefixes of
    [Rep, RepE]
        | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw] -> cycle $ Get ZF      -- repe
        | inOpcode `elem` [Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw] -> cycle'      -- rep
    [RepNE]
        | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw, Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw]
            -> cycle $ Not $ Get ZF
    [] -> body
  where
    body = compileInst $ mdat { mdInst = i { inPrefixes = filter (not . rep) inPrefixes }}

    cycle' = do
        Replicate (Convert $ Get CX) body
        Set CX $ C 0

    cycle :: Exp Bool -> ExpM ()
    cycle cond = do
        when' (Not $ Eq (C 0) $ Get CX) $ do
            body
            Mod CX $ Add $ C $ -1
            when' cond $ cycle cond

    rep p = p `elem` [Rep, RepE, RepNE]

nonSeg = \case
    Seg _ -> False
    x -> True


compileInst :: Metadata -> ExpM ()
compileInst mdat@Metadata{mdInst = i@Inst{..}} = case inOpcode of

    _ | length inOperands > 2 -> error "more than 2 operands are not supported"

    _ | inOpcode `elem` [Ijmp, Icall] -> do
      case op1 of
        Ptr (Pointer seg (Immediate Bits16 v)) -> do
            when (inOpcode == Icall) $ do
                push $ Get Cs
                push $ Get IP
            Set Cs $ C $ fromIntegral seg
            Set IP $ C $ fromIntegral v
        Mem _ -> do
            when (inOpcode == Icall) $ do
                when far $ push $ Get Cs
                push $ Get IP
            letM (addr op1) $ \ad -> do
                Set IP $ Get $ Heap16 ad
                when far $ Set Cs $ Get $ Heap16 $ add (C 2) ad
        _ -> do
            when (inOpcode == Icall) $ do
                push $ Get IP
            Set IP $ getOp1w

    _ | inOpcode `elem` [Iret, Iretf, Iiretw] -> do
        when (inOpcode == Iiretw) $ trace_ "iret"
        pop $ Set IP
        when (inOpcode `elem` [Iretf, Iiretw]) $ pop $ Set Cs
        when (inOpcode == Iiretw) $ pop $ Set Flags
        when (length inOperands == 1) $ Mod SP $ Add (getOp1w)

    Iint  -> Interrupt $ getByteOperand segmentPrefix op1
    Iinto -> when' (Get OF) $ Interrupt $ C 4

    Ihlt  -> Error CleanHalt

    Ijp   -> condJump $ Get PF
    Ijnp  -> condJump $ Not $ Get PF
    Ijz   -> condJump $ Get ZF
    Ijnz  -> condJump $ Not $ Get ZF
    Ijo   -> condJump $ Get OF
    Ijno  -> condJump $ Not $ Get OF
    Ijs   -> condJump $ Get SF
    Ijns  -> condJump $ Not $ Get SF
    Ijb   -> condJump $ Get CF
    Ijae  -> condJump $ Not $ Get CF
    Ijbe  -> condJump $ Or (Get CF) (Get ZF)
    Ija   -> condJump $ Not $ Or (Get CF) (Get ZF)
    Ijl   -> condJump $ Xor (Get SF) (Get OF)
    Ijge  -> condJump $ Not $ Xor (Get SF) (Get OF)
    Ijle  -> condJump $ Or (Xor (Get SF) (Get OF)) (Get ZF)
    Ijg   -> condJump $ Not $ Or (Xor (Get SF) (Get OF)) (Get ZF)

    Ijcxz -> condJump $ Eq (C 0) (Get CX)

    Iloop   -> loop $ C True
    Iloope  -> loop $ Get ZF
    Iloopnz -> loop $ Not $ Get ZF

    Ipush   -> push $ getOp1w
    Ipop    -> pop $ setOp1w
    Ipusha  -> mconcat $ map (push . Get) [AX,CX,DX,BX,SP,BP,SI,DI]
    Ipopa   -> mconcat $ map pop [Set DI,Set SI,Set BP,const Nop,Set BX,Set DX,Set CX,Set AX]
    Ipushfw -> push $ Get Flags
    Ipopfw  -> pop $ Set Flags
    Isahf -> Set (Low  AX) $ Get $ Low Flags
    Ilahf -> Set (High AX) $ Get $ Low Flags

    Iclc  -> Set CF $ C False
    Icmc  -> Mod CF Not
    Istc  -> Set CF $ C True
    Icld  -> Set DF $ C False
    Istd  -> Set DF $ C True
    Icli  -> Set IF $ C False
    Isti  -> Set IF $ C True

    Inop  -> Nop

    Ixlatb -> Set (Low AX) $ Get $ Heap8 $ segAddr_ (maybe Ds (reg . RegSeg) segmentPrefix) $ Add (Convert $ Get $ Low AX) (Get BX)

    Ilea -> setOp1w op2addr'
    _ | inOpcode `elem` [Iles, Ilds] -> letM (addr op2) $ \ad -> do
        setOp1w $ Get $ Heap16 ad
        Set (case inOpcode of Iles -> Es; Ilds -> Ds) $ Get $ Heap16 $ add (C 2) ad

    _ -> case sizeByte of
        1 -> withSize getByteOperand byteOperand (Low AX) (High AX) AX
        2 -> withSize getWordOperand wordOperand AX DX DXAX
  where
    withSize :: forall a . (AsSigned a, Extend a, Extend (Signed a), AsSigned (X2 a), X2 (Signed a) ~ Signed (X2 a))
        => (Maybe Segment -> Operand -> Exp a)
        -> (Maybe Segment -> Operand -> Part a)
        -> Part a
        -> Part a
        -> Part (X2 a)
        -> ExpM ()
    withSize getTr tr_ alx ahd axd = case inOpcode of
        Imov  -> Set op1' op2v
        Ixchg -> LetM op1v $ \o1 -> do
            Set op1' op2v
            Set op2' o1
        Inot  -> Mod op1' Not

        Isal  -> shiftOp $ \_ x -> (HighBit x, ShiftL x)
        Ishl  -> shiftOp $ \_ x -> (HighBit x, ShiftL x)
        Ircl  -> shiftOp $ \c x -> (HighBit x, SetBit 0 c $ ShiftL x)
        Irol  -> shiftOp $ \_ x -> (HighBit x, RotateL x)
        Isar  -> shiftOp $ \_ x -> (Bit 0 x, Convert $ ShiftR $ Signed x)
        Ishr  -> shiftOp $ \_ x -> (Bit 0 x, ShiftR x)
        Ircr  -> shiftOp $ \c x -> (Bit 0 x, SetHighBit c $ ShiftR x)
        Iror  -> shiftOp $ \_ x -> (Bit 0 x, RotateR x)

        Iadd  -> twoOp True  Add
        Isub  -> twoOp True  Sub
        Icmp  -> twoOp False Sub
        Ixor  -> twoOp True  Xor
        Ior   -> twoOp True  Or
        Iand  -> twoOp True  And
        Itest -> twoOp False And
        Iadc  -> twoOp True $ \a b -> Add (Add a b) $ Convert (Get CF)
        Isbb  -> twoOp True $ \a b -> Sub (Sub a b) $ Convert (Get CF)
        Ineg  -> twoOp_ True (flip Sub) op1' $ C 0
        Idec  -> twoOp_ True Add op1' $ C $ -1
        Iinc  -> twoOp_ True Add op1' $ C 1

        Idiv  -> divide id id
        Iidiv -> divide Signed Signed
        Imul  -> multiply id
        Iimul -> multiply Signed

        _ | inOpcode `elem` [Icwd, Icbw] -> Set axd $ Convert $ Signed $ Get alx
          | inOpcode `elem` [Istosb, Istosw] -> move di'' alx >> adjustIndex DI
          | inOpcode `elem` [Ilodsb, Ilodsw] -> move alx si'' >> adjustIndex SI
          | inOpcode `elem` [Imovsb, Imovsw] -> move di'' si'' >> adjustIndex SI >> adjustIndex DI
          | inOpcode `elem` [Iscasb, Iscasw] -> do
            twoOp_ False Sub di'' $ Get alx
            adjustIndex DI
          | inOpcode `elem` [Icmpsb, Icmpsw] -> do
            twoOp_ False Sub si'' $ Get di''
            adjustIndex SI
            adjustIndex DI

        Iin  -> Input (getWordOperand segmentPrefix op2) $ Set op1' . Convert
        Iout -> Output (getWordOperand segmentPrefix op1) $ Convert op2v

      where
        si'', di'' :: Part a
        si'' = tr_ segmentPrefix $ Mem $ memIndex RSI
        di'' = tr_ (Just $ fromMaybe ES segmentPrefix) $ Mem $ memIndex RDI

        adjustIndex i = Mod i $ \x -> If (Get DF) (Add x $ C $ -sizeByte) (Add x $ C sizeByte)

        op1' = tr_ segmentPrefix op1
        op2' = tr_ segmentPrefix op2
        op1v = getTr segmentPrefix op1
        op2v = getTr segmentPrefix op2

        divide :: (Integral a, Integral c, Integral (X2 c)) => (Exp a -> Exp c) -> (Exp (X2 a) -> Exp (X2 c)) -> ExpM ()
        divide asSigned asSigned' =
            QuotRem (asSigned' $ Get axd) (Convert $ asSigned op1v)
                (Error $ Err $ "divide by zero interrupt is not called (not implemented)") $ \(d, m) -> do
                    Set alx $ Convert d
                    Set ahd $ Convert m

        multiply :: forall c . (Extend c, FiniteBits (X2 c)) => (Exp a -> Exp c) -> ExpM ()
        multiply asSigned =
            LetM (Mul (Extend $ asSigned $ Get alx) (Extend $ asSigned op1v)) $ \r ->
            LetM (Not $ Eq r $ Extend (Convert r :: Exp c)) $ \c -> do
                Set axd $ Convert r
                Set CF c
                Set OF c
                Set SF undefBool
                Set PF undefBool
                Set ZF undefBool

        shiftOp :: (forall b . (AsSigned b) => Exp Bool -> Exp b -> (Exp Bool, Exp b)) -> ExpM ()
        shiftOp op = do
            letM (and' (C 0x1f) $ getByteOperand segmentPrefix op2) $ \n -> do
            when' (not' $ eq' (C 0) n) $ LetM (Iterate (Convert n) (uncurry Tuple . uncurry op . unTup) $ Tuple (Get CF) op1v) $ \t -> do
                let r = Snd t
                Set CF $ Fst t
                Set op1' r
                when (inOpcode `elem` [Isal, Isar, Ishl, Ishr]) $ do
                    Set ZF $ Eq (C 0) r
                    Set SF $ HighBit r
                    Set OF undefBool
                    Set PF $ EvenParity $ Convert r
                    Set AF undefBool
                when (inOpcode `elem` [Ircl, Ircr, Irol, Iror]) $ do
                    Set ZF undefBool
                    Set SF undefBool
                    Set OF undefBool
                    Set PF undefBool
                    Set AF undefBool

        twoOp :: Bool -> (forall b . (Integral b, FiniteBits b) => Exp b -> Exp b -> Exp b) -> ExpM ()
        twoOp store op = twoOp_ store op op1' op2v

        twoOp_ :: AsSigned a => Bool -> (forall a . (Integral a, FiniteBits a) => Exp a -> Exp a -> Exp a) -> Part a -> Exp a -> ExpM ()
        twoOp_ store op op1 op2 = LetM (Get op1) $ \a -> letM op2 $ \b -> letM (op a b) $ \r -> do

            when (inOpcode `notElem` [Idec, Iinc]) $
                Set CF $ Not $ Eq (Convert r) $ op (Convert a :: Exp Int) (Convert b)
            Set OF $ Not $ Eq (Convert $ Signed r) $ op (Convert $ Signed a :: Exp Int) (Convert $ Signed b)

            Set ZF $ Eq (C 0) r
            Set SF $ HighBit r
            Set PF $ EvenParity $ Convert r
            Set AF undefBool

            when store $ Set op1 r

    far = " far " `isInfixOf` mdAssembly mdat

    addr op = case op of Mem m -> addressOf segmentPrefix m

    loop cond = do
        Mod CX $ Add $ C $ -1
        condJump $ And (Not $ Eq (C 0) (Get CX)) cond

    condJump :: Exp Bool -> ExpM ()
    condJump b = when' b (Set IP $ getOp1w)

    sizeByte :: Word16
    sizeByte = fromIntegral $ sizeByte_ i

    ~(op1: ~(op2:_)) = inOperands
    getOp1w = getWordOperand segmentPrefix op1
    setOp1w = Set $ wordOperand segmentPrefix op1
    op2addr' = case op2 of Mem m -> addressOf' m

    segmentPrefix :: Maybe Segment
    segmentPrefix = case inPrefixes of
        [Seg s] -> Just s
        [] -> Nothing


interrupt v = do
--    trace_ $ "interrupt " ++ showHex' 2 v
    push $ Get Flags
    push $ Get Cs
    push $ Get IP
    Set IF $ C False
    Set Cs $ Get $ Heap16 $ C (4*fromIntegral v + 2)
    Set IP $ Get $ Heap16 $ C (4*fromIntegral v)

iret :: ExpM ()
iret = do
--    trace_ "iret"
    pop $ Set IP
    pop $ Set Cs
    pop $ Set IF . Bit 9


