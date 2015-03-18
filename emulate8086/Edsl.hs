module Edsl where

import Data.List
import Data.Maybe
import Data.Int
import Data.Word
import Data.Bits
import qualified Data.IntMap.Strict as IM
import Control.Monad
import Hdis86
--import Debug.Trace

import Helper

----------------------------------------

type Part = Part_ Exp

data Part_ e a where
    Heap8  :: e Int -> Part_ e Word8
    Heap16 :: e Int -> Part_ e Word16

    AL, AH, BL, BH, CL, CH, DL, DH :: Part_ e Word8
    AX, BX, CX, DX, SI, DI, BP, SP :: Part_ e Word16
    Es, Ds, Ss, Cs :: Part_ e Word16
    CF, PF, ZF, SF, IF, DF, OF :: Part_ e Bool

    Flags :: Part_ e Word16
    DXAX :: Part_ e Word32

instance Eq (Part_ e a) where
    AX == AX = True
    _ == _ = False

mapPart :: (forall a . e a -> f a) -> Part_ e a -> Part_ f a
mapPart f = \case
    Heap8 a -> Heap8 (f a)
    Heap16 a -> Heap16 (f a)
    AL -> AL
    BL -> BL
    CL -> CL
    DL -> DL
    AH -> AH
    BH -> BH
    CH -> CH
    DH -> DH
    AX -> AX
    BX -> BX
    CX -> CX
    DX -> DX
    SI -> SI
    DI -> DI
    BP -> BP
    SP -> SP
    Es -> Es
    Ds -> Ds
    Ss -> Ss
    Cs -> Cs
    CF -> CF
    PF -> PF
    ZF -> ZF
    SF -> SF
    IF -> IF
    DF -> DF
    OF -> OF
    Flags -> Flags
    DXAX -> DXAX

data Jump' = JumpAddr Word16 Word16

data ExpM e where
    Stop :: e -> ExpM e
    Set :: Part a -> Exp a -> ExpM e -> ExpM e

    Jump' :: Exp Word16 -> Exp Word16 -> ExpM Jump'
    -- constrained let type (with more efficient interpretation) 
    LetMC :: Exp a -> (Exp a -> ExpM ()) -> ExpM e -> ExpM e
    LetM :: Exp a -> (Exp a -> ExpM e) -> ExpM e
    IfM :: Exp Bool -> ExpM e -> ExpM e -> ExpM e
    Replicate :: Integral a => Exp a -> Exp Bool -> ExpM () -> (Exp a -> ExpM e) -> ExpM e

    Input :: Exp Word16 -> (Exp Word16 -> ExpM e) -> ExpM e
    Output :: Exp Word16 -> Exp Word16 -> ExpM e -> ExpM e

set :: Part a -> Exp a -> ExpM ()
set x y = Set x y (return ())

ifM (C c) a b = if c then a else b
ifM x a b = IfM x a b

letM :: Exp a -> ExpM (Exp a)
letM (C c) = return (C c)
letM x = LetM x return

letMC :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
letMC (C c) f = f (C c)
letMC x f = LetMC x f (return ())

output a b = Output a b (return ())


instance Monad ExpM where
    return = Stop
    a >>= f = case a of
        Stop x -> f x
        Set a b e -> Set a b $ e >>= f
        LetMC e x g -> LetMC e x $ g >>= f
        LetM e g -> LetM e $ g >=> f
        IfM b x y -> IfM b (x >>= f) (y >>= f)
        Replicate n b m g -> Replicate n b m $ g >=> f
        Input e g -> Input e $ g >=> f
        Output a b e -> Output a b $ e >>= f
        Jump' _ _ -> error "Jump' >>="

data Exp a where
    Var :: Int -> Exp a

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
    QuotRem :: Integral a => Exp a -> Exp a -> Exp (a, a)
    And, Or, Xor :: Bits a => Exp a -> Exp a -> Exp a
    Not, ShiftL, ShiftR, RotateL, RotateR :: Bits a => Exp a -> Exp a
    EvenParity :: Exp Word8 -> Exp Bool

    Signed :: AsSigned a => Exp a -> Exp (Signed a)
    Extend :: Extend a => Exp a -> Exp (X2 a)
    Convert :: (Integral a, Num b) => Exp a -> Exp b
    SegAddr :: Exp Word16 -> Exp Word16 -> Exp Int

unTup x = (fst' x, snd' x)

instance Num Bool where
    (+) = xor
    (-) = xor
    (*) = (&&)
    abs = id
    signum = id
    fromInteger = odd

instance Real Bool where
    toRational = toRational . fromEnum

instance Integral Bool where
    toInteger = toInteger . fromEnum
    a `quotRem` 1 = (a, 0)
    a `quotRem` 0 = error $ "quotRem " ++ show a ++ " 0 :: Bool"


add (C 0) x = x
add x (C 0) = x
add (C c) (C c') = C $ c + c'
add (C c) (Add (C c') v) = add (C $ c + c') v
add a b = Add a b

mul (C 1) x = x
mul (C 0) x = C 0
mul x (C 1) = x
mul x (C 0) = C 0
mul (C c) (C c') = C $ c * c'
mul a b = Mul a b

and' (C 0) _ = C 0
and' (C c) (C c') = C $ c .&. c'
and' a b = And a b

and'' (C False) _ = C False
and'' (C True) b = b
and'' a b = And a b

not' (C c) = C $ complement c
not' b = Not b

eq' (C c) (C c') = C $ c == c'
eq' a b = Eq a b

fst' (Tuple a _) = a
fst' e = Fst e
snd' (Tuple _ b) = b
snd' e = Snd e

convert :: (Num b, Integral a) => Exp a -> Exp b
convert (C a) = C $ fromIntegral a
convert e = Convert e

iterate' (C 0) f e = e
iterate' (C 1) f e = f e
iterate' n f e = Iterate n f e

extend' :: Extend a => Exp a -> Exp (X2 a)
extend' (C x) = C $ extend x
extend' e = Extend e

signed (C x) = C $ asSigned x
signed e = Signed e

--------------------------------------------------------------------------------

-- instruction blocks
type Blocks = IM.IntMap (ExpM Jump')

--fetchBlock_ :: (Int -> Metadata) -> Word16 -> Word16 -> Maybe Word16 -> Maybe Word16 -> Word16 -> ExpM ()
fetchBlock_ fetch cs ss es ds ip
    = (1, [(ips, ips +1)], IM.singleton (fromIntegral ip) $ fetchBlock' fetch cs ip ss (maybe (Get Es) C es) (maybe (Get Ds) C ds) (Get OF) (Get SF) (Get ZF) (Get PF) (Get CF))
  where
    ips = segAddr cs ip

--------------------------------------------------------------------------------

type FlagTr = forall x . (Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> ExpM x)
                      -> (Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> ExpM x)

highBit :: (Integral a, Bits a) => Exp a -> Exp Bool
highBit = Convert . RotateL

setHighBit :: (Num a, Bits a) => Exp Bool -> Exp a -> Exp a
setHighBit c = Or (RotateR $ Convert c)

fetchBlock'
    :: (Int -> Metadata)
    -> Word16 -> Word16 -> Word16 -> Exp Word16 -> Exp Word16
    -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool -> Exp Bool
    -> ExpM Jump'
fetchBlock' fetch cs ip ss es ds oF sF zF pF cF = case inOpcode of

    _ | length inOperands > 2 -> error "more than 2 operands are not supported"

    _ | inOpcode `elem` [Ijmp, Icall] -> do
      let jmp far cs' ip' = do
            when (inOpcode == Icall) $ do
                when far $ push $ C cs
                push $ C nextip
            jump cs' ip'
      case op1 of
        Ptr (Pointer seg (Immediate Bits16 v)) -> jmp True (C $ fromIntegral seg) (C $ fromIntegral v)
        Mem _ -> addr2 op1 $ \ad ad2 -> jmp far (if far then ad2 else C cs) ad
        _     -> jmp False (C cs) (getWordOperand op1)

    _ | inOpcode `elem` [Iret, Iretf, Iiretw] -> do
        ip <- pop
        cs <- if inOpcode == Iret then return $ C cs else pop
        if inOpcode == Iiretw then pop' $ set Flags else setFlags
        when (length inOperands == 1) $ modif SP $ Add (getWordOperand op1)
        Jump' cs ip

    Iint  -> case getByteOperand op1 of C n -> interrupt n
    Iinto -> ifM oF (interrupt 4) cc

    Ihlt  -> interrupt 0x20

    Ijp   -> condJump pF
    Ijnp  -> condJump $ Not pF
    Ijz   -> condJump zF
    Ijnz  -> condJump $ Not zF
    Ijo   -> condJump oF
    Ijno  -> condJump $ Not oF
    Ijs   -> condJump sF
    Ijns  -> condJump $ Not sF
    Ijb   -> condJump cF
    Ijae  -> condJump $ Not cF
    Ijbe  -> condJump $ Or cF zF
    Ija   -> condJump $ Not $ Or cF zF
    Ijl   -> condJump $ Xor sF oF
    Ijge  -> condJump $ Not $ Xor sF oF
    Ijle  -> condJump $ Or (Xor sF oF) zF
    Ijg   -> condJump $ Not $ Or (Xor sF oF) zF

    Ijcxz -> condJump $ Eq (C 0) (Get CX)

    Iloop   -> loop $ C True
    Iloope  -> loop zF
    Iloopnz -> loop $ Not zF

    -- hack for stunts!  TODO: do it in a postprocessing phase?
    Ipop | op1 == Reg (RegSeg DS) -> cont' es (Get Ds) $ pop' $ set Ds
         | op1 == Reg (RegSeg ES) -> cont' (Get Es) ds $ pop' $ set Es
    Imov | op1 == Reg (RegSeg DS) -> cont' es (Get Ds) $ set Ds $ getWordOperand op2
         | op1 == Reg (RegSeg ES) -> cont' (Get Es) ds $ set Es $ getWordOperand op2

    Inop  -> cc

    Ipush   -> c $ push (getWordOperand op1)
    Ipop    -> c $ pop' $ set $ wordOperand op1
    Ipusha  -> c $ mapM_ (push . Get) [AX,CX,DX,BX,SP,BP,SI,DI]
    Ipopa   -> c $ mapM_ pop' [set DI,set SI,set BP,const $ return (),set BX,set DX,set CX,set AX]
    Ipushfw -> setFlags >> push (Get Flags) >> ccClean
    Ipopfw  ->             pop' (set Flags) >> ccClean
    Isahf   -> setFlags >> set AL (Convert $ Get Flags) >> ccClean
    Ilahf   -> setFlags >> set AH (Convert $ Get Flags) >> ccClean

    Iclc  -> ccF oF sF zF pF (C False)
    Icmc  -> ccF oF sF zF pF (Not cF)
    Istc  -> ccF oF sF zF pF (C True)
    Icld  -> c $ set DF $ C False
    Istd  -> c $ set DF $ C True
    Icli  -> c $ set IF $ C False
    Isti  -> c $ set IF $ C True

    Ixlatb -> c $ set AL $ Get $ Heap8 $ segAddr_ (segmentPrefix DS) $ Add (Extend $ Get AL) (Get BX)

    Ilea -> c $ set (wordOperand op1) $ addressOf' (unMem op2)
    _ | inOpcode `elem` [Iles, Ilds] -> addr2 op2 $ \ad ad2 -> do
        set (wordOperand op1) ad
        case inOpcode of
            Iles -> cont' (Get Es) ds $ set Es ad2
            Ilds -> cont' es (Get Ds) $ set Ds ad2

    _ -> case sizeByte of
        1 -> withSize getByteOperand byteOperand AL AH AX
        2 -> withSize getWordOperand wordOperand AX DX DXAX
  where
    Metadata{..} = fetch $ segAddr cs ip
    Inst{..} = mdInst
    ~(op1: ~(op2:_)) = inOperands
    nextip = ip + fromIntegral mdLength

    c m = m >> cc
    cc = ccF oF sF zF pF cF
    ccF = fetchBlock' fetch cs nextip ss es ds
    uSet' f _ = Get f -- const $ C False
    ccClean = ccF (Get OF) (Get SF) (Get ZF) (Get PF) (Get CF)
    cont' es ds m = m >> fetchBlock' fetch cs nextip ss es ds oF sF zF pF cF
    jump a b = setFlags >> Jump' a b
    setFlags = setF oF sF zF pF cF
    setF oF sF zF pF cF = setOF oF >> setSF sF >> setZF zF >> setPF pF >> setCF cF
      where
        setOF (Get OF) = return ()
        setOF x = set OF x
        setSF (Get SF) = return ()
        setSF x = set SF x
        setZF (Get ZF) = return ()
        setZF x = set ZF x
        setPF (Get PF) = return ()
        setPF x = set PF x
        setCF (Get CF) = return ()
        setCF x = set CF x

    withSize :: forall a . (AsSigned a, Extend a, Extend (Signed a), AsSigned (X2 a), X2 (Signed a) ~ Signed (X2 a))
        => (Operand -> Exp a)
        -> (Operand -> Part a)
        -> Part a
        -> Part a
        -> Part (X2 a)
        -> ExpM Jump'
    withSize getTr tr_ alx ahd axd = case inOpcode of
        Imov  -> c $ set op1' op2v
        Ixchg -> c $ letMC op1v $ \o1 -> do
            set op1' op2v
            set op2' o1
        Inot  -> c $ modif op1' Not

        Isal  -> shiftOp $ \_ x -> (highBit x, ShiftL x)
        Ishl  -> shiftOp $ \_ x -> (highBit x, ShiftL x)
        Ircl  -> shiftOp $ \c x -> (highBit x, Xor (Convert c) $ ShiftL x)
        Irol  -> shiftOp $ \_ x -> (highBit x, RotateL x)
        Isar  -> shiftOp $ \_ x -> (Convert x, Convert $ ShiftR $ Signed x)
        Ishr  -> shiftOp $ \_ x -> (Convert x, ShiftR x)
        Ircr  -> shiftOp $ \c x -> (Convert x, setHighBit c $ ShiftR x)
        Iror  -> shiftOp $ \_ x -> (Convert x, RotateR x)

        Iadd  -> twoOp True  Add
        Isub  -> twoOp True  Sub
        Icmp  -> twoOp False Sub
        Ixor  -> twoOp True  Xor
        Ior   -> twoOp True  Or
        Iand  -> twoOp True  And
        Itest -> twoOp False And
        Iadc  -> twoOp True $ \a b -> Add (Add a b) $ Convert cF
        Isbb  -> twoOp True $ \a b -> Sub (Sub a b) $ Convert cF
        Ineg  -> twoOp_ True (flip Sub) op1' $ C 0
        Idec  -> twoOp_ True Add op1' $ C $ -1
        Iinc  -> twoOp_ True Add op1' $ C 1

        Idiv  -> divide id id
        Iidiv -> divide signed Signed
        Imul  -> multiply id
        Iimul -> multiply signed

        _ | inOpcode `elem` [Icwd,   Icbw]   -> c $ set axd $ Convert $ Signed $ Get alx
          | inOpcode `elem` [Istosb, Istosw] -> cycle $ normal $ move di'' alx >> adjustIndex DI
          | inOpcode `elem` [Ilodsb, Ilodsw] -> cycle $ normal $ move alx si'' >> adjustIndex SI
          | inOpcode `elem` [Imovsb, Imovsw] -> cycle $ normal $ move di'' si'' >> adjustIndex SI >> adjustIndex DI
          | inOpcode `elem` [Iscasb, Iscasw] -> cycle $ \cont ->
                twoOp__ False Sub di'' (Get alx) $ \oF sF zF pF cF -> do
                    adjustIndex DI
                    cont oF sF zF pF cF
          | inOpcode `elem` [Icmpsb, Icmpsw] -> cycle $ \cont ->
                twoOp__ False Sub si'' (Get di'') $ \oF sF zF pF cF -> do
                    adjustIndex SI
                    adjustIndex DI
                    cont oF sF zF pF cF

        Iin  -> c $ Input (getWordOperand op2) $ set op1' . Convert
        Iout -> c $ output (getWordOperand op1) $ convert op2v

      where

        si'', di'' :: Part a
        si'' = tr_ $ memIndex RSI
        di'' = tr_ $ memIndex RDI

        memIndex r = Mem $ Memory undefined (Reg16 r) RegNone 0 $ Immediate Bits0 0

        adjustIndex i = modif i $ Add $ If (Get DF) (C $ -sizeByte) (C sizeByte)

        op1' = tr_ op1
        op2' = tr_ op2
        op1v = getTr op1
        op2v = getTr op2

        divide :: (Integral a, Integral c, Integral (X2 c)) => (Exp a -> Exp c) -> (Exp (X2 a) -> Exp (X2 c)) -> ExpM Jump'
        divide asSigned asSigned' = c $ letMC (QuotRem (asSigned' $ Get axd) (convert $ asSigned op1v)) $ \t -> do
            set alx $ Convert $ Fst t
            set ahd $ Convert $ Snd t

        multiply :: forall c . (Extend c, FiniteBits (X2 c)) => (Exp a -> Exp c) -> ExpM Jump'
        multiply asSigned =
            letM (Mul (Extend $ asSigned $ Get alx) (extend' $ asSigned op1v)) >>= \r ->
            letM (Not $ Eq r $ Extend (Convert r :: Exp c)) >>= \c -> do
            set axd $ Convert r
            ccF c (uSet' SF sF) (C False){-needed for Stunts-} (uSet' PF pF) c

        shiftOp :: (forall b . (AsSigned b) => Exp Bool -> Exp b -> (Exp Bool, Exp b)) -> ExpM Jump'
        shiftOp op = letM (and' (C 0x1f) $ getByteOperand op2) >>= \n -> do
             ifM (eq' (C 0) n) cc $ do        -- TODO!
                letM (iterate' (convert n) (uncurry Tuple . uncurry op . unTup) $ Tuple cF op1v) >>= \t -> do
                let r = snd' t
                set op1' r
                if inOpcode `elem` [Isal, Isar, Ishl, Ishr] then
                    ccF (uSet' OF oF) (highBit r) (Eq (C 0) r) (EvenParity $ Convert r) (fst' t)
                  else   -- [Ircl, Ircr, Irol, Iror]
                    ccF (uSet' OF oF) (uSet' SF sF) (uSet' ZF zF) (uSet' PF pF) (fst' t)

        twoOp :: Bool -> (forall b . (Integral b, FiniteBits b) => Exp b -> Exp b -> Exp b) -> ExpM Jump'
        twoOp store op = twoOp_ store op op1' op2v

        twoOp_ :: AsSigned a => Bool -> (forall a . (Integral a, FiniteBits a) => Exp a -> Exp a -> Exp a) -> Part a -> Exp a -> ExpM Jump'
        twoOp_ store op op1 op2 = twoOp__ store op op1 op2 ccF oF sF zF pF cF

        twoOp__ :: AsSigned a
                => Bool -> (forall a . (Integral a, FiniteBits a) => Exp a -> Exp a -> Exp a) -> Part a -> Exp a
                -> FlagTr
        twoOp__ store op op1 op2 cont oF sF zF pF cF =
            letM (Get op1) >>= \a -> do
            let b = op2 --letMC op2 $ \b ->
            letM (op a b) >>= \r -> do

            when store $ set op1 r

            cont (Not $ Eq (Convert $ Signed r) $ op (Convert $ Signed a :: Exp Int) (convert $ signed b))
                 (highBit r)
                 (Eq (C 0) r)
                 (EvenParity $ Convert r)
                 (if inOpcode `elem` [Idec, Iinc] then cF else Not $ Eq (Convert r) $ op (Convert a :: Exp Int) (convert b))

    cycle :: FlagTr -> ExpM Jump'
    cycle body = case filter rep inPrefixes of
        [Rep, RepE]
            | inOpcode `elem` [Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw] -> cyc $ C True      -- rep
            | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw] -> cyc $ Get ZF      -- repe
        [RepNE]
            | inOpcode `elem` [Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw] -> cyc $ Not $ Get ZF -- cyc $ C True    -- ???
            | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw] -> cyc $ Not $ Get ZF
                
        [] -> body ccF oF sF zF pF cF
      where
        cyc cond = setFlags >> Replicate (Get CX) cond (body setF (Get OF) (Get SF) (Get ZF) (Get PF) (Get CF)) (\x -> set CX x >> ccClean)

    normal m setF oF sF zF pF cF = m >> setF oF sF zF pF cF

    rep = (`elem` [Rep, RepE, RepNE])

    far = " far " `isInfixOf` mdAssembly

    addr2 m f = do
        ad <- letM $ addressOf $ unMem m
        f (Get $ Heap16 ad) (Get $ Heap16 $ Add (C 2) ad)

    loop cond = do
        modif CX $ Add $ C $ -1
        condJump $ and'' cond $ Not $ Eq (C 0) (Get CX)

    condJump :: Exp Bool -> ExpM Jump'
    condJump b = ifM b (jump (C cs) (getWordOperand op1)) cc

    sizeByte :: Word16
    sizeByte = case inOpcode of
        Iin  -> fromJust $ operandSize op1
        Iout -> fromJust $ operandSize op2
        _   | inOpcode `elem` [Icbw, Icmpsb, Imovsb, Istosb, Ilodsb, Iscasb, Ilahf] -> 1
            | inOpcode `elem` [Icwd, Icmpsw, Imovsw, Istosw, Ilodsw, Iscasw] -> 2
            | otherwise -> fromMaybe (error $ "size: " ++ show mdInst) $ listToMaybe $ catMaybes $ map operandSize inOperands

    operandSize = \case
        Reg (Reg16 _)   -> Just 2
        Reg (Reg8 _ _)  -> Just 1
        Mem (Memory Bits8 _ _ _ _)  -> Just 1
        Mem (Memory Bits16 _ _ _ _) -> Just 2
        Imm (Immediate Bits8 v)  -> Just 1
        Imm (Immediate Bits16 v) -> Just 2
        _ -> Nothing

    unMem (Mem m) = m

    getReg :: Register -> Exp Word16
    getReg = \case
        RegNone -> C 0
        RegIP -> C nextip
        RegSeg s -> case s of
            SS -> C ss
            CS -> C cs
            ES -> es
            DS -> ds
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
        x -> error $ "reg: " ++ show x

    segmentPrefix s' = getReg $ RegSeg $ case filter (not . rep) inPrefixes of
        [Seg s] -> s
        [] -> s'

    addressOf :: Memory -> Exp Int
    addressOf m
        = segAddr_ (segmentPrefix s) (addressOf' m)
      where
        s = case mBase m of
            RegIP     -> CS
            Reg16 RSP -> SS
            Reg16 RBP -> SS
            Reg16 RDI | stringinstruction -> ES
            _         -> DS

    stringinstruction = inOpcode `elem` [Icwd, Icbw, Istosb, Istosw, Ilodsb, Ilodsw, Imovsb, Imovsw, Iscasb, Iscasw, Icmpsb, Icmpsw]

    addressOf' :: Memory -> Exp Word16
    addressOf' (Memory _ r r' 0 i) = add (C $ imm i) $ add (getReg r) (getReg r')

    getByteOperand = \case
        Imm (Immediate Bits8 v) -> C $ fromIntegral v
        Hdis86.Const (Immediate Bits0 0) -> C 1 -- !!!
        x -> Get $ byteOperand x

    byteOperand :: Operand -> Part Word8
    byteOperand = \case
        Mem m -> Heap8 $ addressOf m
        Reg r -> case r of
            Reg8 r L -> case r of
                RAX -> AL
                RBX -> BL
                RCX -> CL
                RDX -> DL
            Reg8 r H -> case r of
                RAX -> AH
                RBX -> BH
                RCX -> CH
                RDX -> DH

    getWordOperand = \case
        Imm i  -> C $ imm' i
        Jump i -> C $ imm i + nextip
        Reg r  -> getReg r
        Mem m  -> Get $ Heap16 $ addressOf m

    wordOperand :: Operand -> Part Word16
    wordOperand = \case
        Reg r  -> reg r
        Mem m  -> Heap16 $ addressOf m


    imm = fromIntegral . iValue
    -- patched version
    imm' (Immediate Bits8 i) = fromIntegral (fromIntegral i :: Int8)
    imm' i = imm i

    push :: Exp Word16 -> ExpM ()
    push x = letMC (Add (C $ -2) (Get SP)) $ \sp -> do
        set SP sp
        set (Heap16 $ segAddr_ (C ss) sp) x

    pop :: ExpM (Exp Word16)
    pop = do
        sp <- letM $ Get SP
        set SP $ Add (C 2) sp
        return $ Get $ Heap16 $ segAddr_ (C ss) sp

    pop' :: (Exp Word16 -> ExpM ()) -> ExpM ()
    pop' f = letMC (Get SP) $ \sp -> do
        set SP $ Add (C 2) sp
        f $ Get $ Heap16 $ segAddr_ (C ss) sp

    interrupt :: Word8 -> ExpM Jump'
    interrupt v = do
        setFlags
        push $ Get Flags
        push $ C cs
        push $ C nextip
        set IF $ C False
        let i = fromIntegral $ 4*v
        Jump' (Get $ Heap16 $ C $ i + 2) (Get $ Heap16 $ C i)

    segAddr_ :: Exp Word16 -> Exp Word16 -> Exp Int
    segAddr_ (C s) (C o) = C $ segAddr s o
    segAddr_ seg off = SegAddr seg off

    move a b = set a $ Get b

    modif p f = set p $ f $ Get p


