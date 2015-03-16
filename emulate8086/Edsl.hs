module Edsl where

import Data.List
import Data.Maybe
import Data.Int
import Data.Word
import Data.Bits
import qualified Data.Set as S
import Data.Monoid
import Control.Monad
import Hdis86

import Helper

----------------------------------------

type Part = Part_ Exp

data Part_ e a where
    Heap8  :: e Int -> Part_ e Word8
    Heap16 :: e Int -> Part_ e Word16

    AX, BX, CX, DX, SI, DI, BP, SP :: Part_ e Word16
    Es, Ds, Ss, Cs :: Part_ e Word16
    CF, PF, ZF, SF, IF, DF, OF :: Part_ e Bool

    Flags :: Part_ e Word16
    DXAX :: Part_ e Word32

    Low, High :: Part_ e Word16 -> Part_ e Word8

mapPart :: (forall a . e a -> f a) -> Part_ e a -> Part_ f a
mapPart f = \case
    Heap8 a -> Heap8 (f a)
    Heap16 a -> Heap16 (f a)
    Low a -> Low $ mapPart f a
    High a -> High $ mapPart f a
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



data Part'
    = Heap'
    | IP' | AL' | BL' | CL' | DL' | AH' | BH' | CH' | DH' 
    | SI' | DI' | BP' | SP' | Es' | Ds' | Ss' | Cs' | CF' | PF' | ZF' | SF' | IF' | DF' | OF'
    deriving (Eq, Ord)

data Eqq a b where
    Eqq :: (a ~ b) => Eqq a b
    NotEq :: Eqq a b
{-
same :: Part a -> Part b -> Eqq a b
same a b | keyOf a == keyOf b = unsafeCoerce Eqq
         | otherwise = NotEq

keyOf :: Part a -> S.Set Part'
keyOf = \case
    AX -> S.fromList [AL', AH']
    BX -> S.fromList [BL', BH']
    CX -> S.fromList [CL', CH']
    DX -> S.fromList [DL', DH']
    IP -> S.singleton IP'
    SI -> S.singleton SI'
    DI -> S.singleton DI'
    BP -> S.singleton BP'
    SP -> S.singleton SP'
    Es -> S.singleton Es'
    Ds -> S.singleton Ds'
    Cs -> S.singleton Cs'
    Ss -> S.singleton Ss'
    CF -> S.singleton CF'
    PF -> S.singleton PF'
    AF -> S.singleton AF'
    ZF -> S.singleton ZF'
    SF -> S.singleton SF'
    IF -> S.singleton IF'
    DF -> S.singleton DF'
    OF -> S.singleton OF'
    Flags -> S.fromList [CF', PF', AF', ZF', SF', IF', DF', OF']
    DXAX  -> S.fromList [AL', AH', DL', DH']
    Low AX -> S.singleton AL'
    Low BX -> S.singleton BL'
    Low CX -> S.singleton CL'
    Low DX -> S.singleton DL'
    Low  a -> keyOf a
    High AX -> S.singleton AH'
    High BX -> S.singleton BH'
    High CX -> S.singleton CH'
    High DX -> S.singleton DH'
    High a  -> keyOf a
    Heap8 _  -> S.singleton Heap'
    Heap16 _ -> S.singleton Heap'
--    _ -> full --Heap8' i
--    Heap16
-}
full :: Inf
full = S.fromList [ Heap',
      IP', AL', BL', CL', DL', AH', BH', CH', DH', SI', DI', BP', SP', Es', Ds', Ss', Cs', CF', PF', ZF', SF', IF', DF', OF'
        ]

data Jump' = JumpAddr Word16 Word16

data ExpM e where
    Stop :: e -> ExpM e
    Set :: Part a -> Exp a -> ExpM e -> ExpM e

    Jump' :: Exp Word16 -> Exp Word16 -> ExpM Jump'
    LetM :: Exp a -> (Exp a -> ExpM e) -> ExpM e  -- -> ExpM e
    IfM :: Exp Bool -> ExpM e -> ExpM e -> ExpM e
    Replicate :: Integral a => Exp a -> Exp Bool -> ExpM () -> (Exp a -> ExpM e) -> ExpM e

    Input :: Exp Word16 -> (Exp Word16 -> ExpM e) -> ExpM e
    Output :: Exp Word16 -> Exp Word16 -> ExpM e -> ExpM e

set :: Part a -> Exp a -> ExpM ()
set x y = Set x y (return ())

ifM (C c) a b = if c then a else b
ifM x a b = IfM x a b

when' :: Exp Bool -> ExpM () -> ExpM ()
when' b x = ifM b x (return ())

letM :: Exp a -> (Exp a -> ExpM e) -> ExpM e
letM (C c) f = f (C c)
letM x f = LetM x f

output a b = Output a b (return ())


instance Monad ExpM where
    return = Stop
    a >>= f = case a of
        Stop x -> f x
        Set a b e -> Set a b $ e >>= f
--        LetM e x g -> LetM e x $ g >>= f
        LetM e g -> LetM e $ g >=> f
        IfM b x y -> IfM b (x >>= f) (y >>= f)
        Replicate n b m g -> Replicate n b m $ g >=> f
        Input e g -> Input e $ g >=> f
        Output a b e -> Output a b $ e >>= f

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
    Bit :: Bits a => Int -> Exp a -> Exp Bool
    SetBit :: Bits a => Int -> Exp Bool -> Exp a -> Exp a
    HighBit :: FiniteBits a => Exp a -> Exp Bool
    SetHighBit :: FiniteBits a => Exp Bool -> Exp a -> Exp a
    EvenParity :: Exp Word8 -> Exp Bool

    Signed :: AsSigned a => Exp a -> Exp (Signed a)
    Extend :: Extend a => Exp a -> Exp (X2 a)
    Convert :: (Integral a, Num b) => Exp a -> Exp b
    SegAddr :: Exp Word16 -> Exp Word16 -> Exp Int

uSet f = return () --Set f $ C False
unTup x = (fst' x, snd' x)

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


add (C 0) x = x
add x (C 0) = x
add (C c) (C c') = C $ c + c'
add (C c) (Add (C c') v) = add (C $ c + c') v
add a b = Add a b

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

-- get / set / mod / neutral / Interrupt

type Inf = S.Set Part'
type Info = (Inf, Inf)

{-
mparts :: ExpM b -> Info
mparts = \case
    Seq a b -> mparts a |+| mparts b
    IfM e a b -> eparts' e |+| mparts a |+| mparts b
    LetM e f -> mparts $ f e
    Replicate e x -> eparts' e |+| mparts x
    Cyc2 a b x -> eparts' a |+| eparts' b |+| mparts x
    Set x y -> (keyOf x, eparts y)
    Jump' x y -> eparts' x |+| eparts' y |+| (keyOf Cs |.| keyOf IP, mempty)
    Nop -> mempty
    Trace{} -> mempty
    QuotRem{} -> (full, full)
    Input{} -> (full, full)
    Output{} -> (full, full)
--    _ -> (full, full)

eparts' = (,) mempty . eparts

(a,b) |+| (c,d) = (S.union a c, S.union b d)
(|.|) = S.union

eparts :: Exp b -> S.Set Part'
eparts = \case
    C{} -> mempty

    Let e f -> eparts $ f e
    Tuple a b -> eparts a |.| eparts b
    Fst e -> eparts e
    Snd e -> eparts e
    If e a b -> eparts e |.| eparts a |.| eparts b

    Get x -> keyOf x

    Eq a b -> eparts a |.| eparts b
    Sub a b -> eparts a |.| eparts b
    Add a b -> eparts a |.| eparts b
    Mul a b -> eparts a |.| eparts b
    And a b -> eparts a |.| eparts b
    Or a b -> eparts a |.| eparts b
    Xor a b -> eparts a |.| eparts b
    Not e -> eparts e
    ShiftL e -> eparts e
    ShiftR e -> eparts e
    RotateL e -> eparts e
    RotateR e -> eparts e
    Bit _ e -> eparts e
    SetBit _ e b -> eparts e |.| eparts b
    HighBit e -> eparts e
    SetHighBit a e -> eparts a |.| eparts e
    EvenParity e -> eparts e

    Signed e -> eparts e
    Extend e -> eparts e
    Convert e -> eparts e
    SegAddr a b -> eparts a |.| eparts b

    Iterate{}   -> full
-}
{-
reple :: forall a . Part a -> Exp a -> (forall b . Exp b -> Exp b)
reple k e' = eparts where

  eparts :: forall b . Exp b -> Exp b
  eparts = \case

{-
    Let e f -> Let (eparts e) $ 
--    Let :: Exp a -> (Exp a -> Exp b) -> Exp b
--    Iterate :: Exp Int -> (Exp a -> Exp a) -> Exp a -> Exp a
    --Iterate e f x -> Iterate --
-}
    Tuple a b -> eparts a `Tuple` eparts b
    Fst e -> Fst $ eparts e
    Snd e -> Snd $ eparts e
    If e a b -> If (eparts e) (eparts a) (eparts b)

    x@(Get k') -> case same k' k of
        Eqq -> e'
        _ -> x

    Eq a b -> eparts a `Eq` eparts b
    Sub a b -> eparts a `Sub` eparts b
    Add a b -> eparts a `Add` eparts b
    Mul a b -> eparts a `Mul` eparts b
    And a b -> eparts a `And` eparts b
    Or a b -> eparts a `Or` eparts b
    Xor a b -> eparts a `Xor` eparts b
    Not e -> Not $ eparts e
    ShiftL e -> ShiftL $ eparts e
    ShiftR e -> ShiftR $ eparts e
    RotateL e -> RotateL $ eparts e
    RotateR e -> RotateR $ eparts e
    Bit i e -> Bit i $ eparts e
    SetBit i e b -> SetBit i (eparts e) (eparts b)
    HighBit e -> HighBit $ eparts e
    SetHighBit a e -> eparts a `SetHighBit` eparts e
    EvenParity e -> EvenParity $ eparts e

    Signed e -> Signed $ eparts e
    Extend e -> Extend $ eparts e
    Convert e -> Convert $ eparts e
    SegAddr a b ->  `SegAddr` eparts b
    e -> e
-}
{-
repl' IP e m@(Set IP (Add v (Get IP))) = Set IP (add v e)
repl' IP e m@(Set IP (Add v (Get IP)) `Seq` m') = Set IP (add v e) `Seq` m'
repl' k e m = Set k e `Seq` m


repl' :: Part a -> Exp a -> ExpM () -> ExpM ()
-}
{-
repl k e = \case
    p@(Set k' e') -> case same k k' of
        Eqq -> Set k $ reple k e e'
        _ -> p
-}
{-
    IfM :: Exp Bool -> ExpM () -> ExpM () -> ExpM ()
    QuotRem :: Integral a => Exp a -> Exp a -> ExpM () -> ((Exp a, Exp a) -> ExpM ()) -> ExpM ()

    LetM :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
--    LetM' :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
    Replicate :: Exp Int -> ExpM () -> ExpM ()

    _ -> e


    Input :: Exp Word16 -> (Exp Word16 -> ExpM ()) -> ExpM ()
    Output :: Exp Word16 -> Exp Word16 -> ExpM ()
-}
{-
type AState = [(Inf, ExpM ())]

fin = uncurry final
final st b = mconcat (map snd st) <> b

findKey :: S.Set Part' -> AState -> Maybe (Inf, ExpM ())
findKey k [] = Nothing
findKey k (v@(_, Set k' _): _) | k == keyOf k' = Just v
findKey k (_: xs) = findKey k xs

-- TODO: optimize IP setting out of IfM 
reorderExp :: ExpM () -> ExpM ()
reorderExp =  uncurry final . foldrExp f (\b x y -> ([], IfM b (fin x) (fin y))) ([], Nop)
  where
    f :: ExpM b -> (AState, ExpM ()) -> (AState, ExpM ())
    f a (st, b) = case a of

        Set k@IP v -> case findKey (keyOf k) st of
            Nothing -> ([(na, a)], b)
            Just (i, vs)
                | i `disj` ni -> ( if keyOf k `disj` i then [(i, vs)] else [(na |.| i, repl' k v vs)], b)
                | otherwise -> fin

        _ -> case st of
            [(i, vs)] | IP' `S.notMember` na && i `disj` ni -> ([(i, vs)], a `Seq` b)
            _ -> fin

      where
        (ni, na) = mparts a

        fin :: (AState, ExpM ())
        fin = ([], a `Seq` final st b)
-}

disj a b = S.null $ S.intersection a b

{-
foldrExp :: (forall b . ExpM b -> a -> a) -> (forall b . Exp Bool -> a -> a -> a) -> a -> ExpM b -> a
foldrExp f g x (Seq a b) = f a (foldrExp f g x b)
foldrExp f g x (IfM a b c) = g a (foldrExp f g x b) (foldrExp f g x c)
foldrExp f g x y = f y x
-}
--fetchBlock_ :: (Int -> Metadata) -> Word16 -> Word16 -> Maybe Word16 -> Maybe Word16 -> Word16 -> ExpM ()
fetchBlock_ fetch cs_ ss es ds ip_ = (1, [(ips_, ips_ +1)], fetchBlock_' fetch cs_ ss es ds ip_)
  where
    ips_ = segAddr cs_ ip_

    fetchBlock_' :: (Int -> Metadata) -> Word16 -> Word16 -> Maybe Word16 -> Maybe Word16 -> Word16 -> ExpM Jump'
    fetchBlock_' fetch cs_ ss es ds ip_ =
        execInstruction' md (fetchBlock_' fetch cs_ ss es ds) cs_ ss es ds ip_
      where
        md = fetch $ segAddr cs_ ip_

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

execInstruction' :: Metadata -> (Word16 -> ExpM Jump') -> Word16 -> Word16 -> Maybe Word16 -> Maybe Word16 -> Word16 -> ExpM Jump'
execInstruction' mdat@Metadata{mdInst = i@Inst{..}} cont cs ss es ds ip
  = case filter rep inPrefixes of
    [Rep, RepE]
        | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw] -> cycle $ Get ZF      -- repe
        | inOpcode `elem` [Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw] -> cycle $ C True      -- rep
    [RepNE]
        | inOpcode `elem` [Icmpsb, Icmpsw, Iscasb, Iscasw, Imovsb, Imovsw, Ilodsb, Ilodsw, Istosb, Istosw]
            -> cycle $ Not $ Get ZF
    [] -> body cont cs ss es ds ip
  where
    body = compileInst (mdat { mdInst = i { inPrefixes = filter (not . rep) inPrefixes }})
    body' = body (const $ return undefined) cs ss es ds ip

    cycle :: Exp Bool -> ExpM Jump'
    cycle cond = Replicate (Get CX) cond (body' >> return ()) (set CX) >> cc

    rep = (`elem` [Rep, RepE, RepNE])
    cc = cont $ ip + fromIntegral (mdLength mdat)

jump a b = Jump' a b

compileInst :: Metadata -> (Word16 -> ExpM Jump') -> Word16 -> Word16 -> Maybe Word16 -> Maybe Word16 -> Word16 -> ExpM Jump'
compileInst mdat@Metadata{mdInst = i@Inst{..}} cont cs ss es ds ip = case inOpcode of

    _ | length inOperands > 2 -> error "more than 2 operands are not supported"

    _ | inOpcode `elem` [Ijmp, Icall] -> do
      let jmp far cs' ip' = do
            when (inOpcode == Icall) $ do
                when far $ push $ C cs
                push $ C nextip
            jump cs' ip'
      case op1 of
        Ptr (Pointer seg (Immediate Bits16 v)) -> jmp True (C $ fromIntegral seg) (C $ fromIntegral v)
        Mem _ -> addr2 op1 $ \(ad, ad2) -> jmp far (if far then ad2 else C cs) ad
        _     -> jmp False (C cs) getOp1w

    _ | inOpcode `elem` [Iret, Iretf, Iiretw] -> pop $ \ip -> do
        let m = do
                when (inOpcode == Iiretw) $ pop $ set Flags
                when (length inOperands == 1) $ modif SP $ Add (getOp1w)
        if (inOpcode `elem` [Iretf, Iiretw])
            then pop $ \cs' -> m >> jump cs' ip
            else m >> jump (C cs) ip

    Iint  -> interrupt (C cs) $ getByteOperand segmentPrefix op1
    Iinto -> ifM (Get OF) (interrupt (C cs) $ C 4) end

    Ihlt  -> interrupt (C cs) $ C 0x20

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

    -- hack for stunts!
    Ipop | op1 == Reg (RegSeg DS) -> stop $ pop $ set Ds
         | op1 == Reg (RegSeg ES) -> stop $ pop $ set Es
    Imov | op1 == Reg (RegSeg DS) -> stop $ set Ds $ getWordOperand segmentPrefix op2
         | op1 == Reg (RegSeg ES) -> stop $ set Es $ getWordOperand segmentPrefix op2
         | op1 == Reg (RegSeg SS) -> stop $ set Ss $ getWordOperand segmentPrefix op2


    Ipush   -> c $ push getOp1w
    Ipop    -> c $ pop setOp1w
    Ipusha  -> c $ mapM_ (push . Get) [AX,CX,DX,BX,SP,BP,SI,DI]
    Ipopa   -> c $ mapM_ pop [set DI,set SI,set BP,const $ return (),set BX,set DX,set CX,set AX]
    Ipushfw -> c $ push $ Get Flags
    Ipopfw  -> c $ pop $ set Flags
    Isahf -> c $ set (Low  AX) $ Get $ Low Flags
    Ilahf -> c $ set (High AX) $ Get $ Low Flags

    Iclc  -> c $ set CF $ C False
    Icmc  -> c $ modif CF Not
    Istc  -> c $ set CF $ C True
    Icld  -> c $ set DF $ C False
    Istd  -> c $ set DF $ C True
    Icli  -> c $ set IF $ C False
    Isti  -> c $ set IF $ C True

    Inop  -> cc

    Ixlatb -> c $ set (Low AX) $ Get $ Heap8 $ segAddr_ (maybe gds (getReg . RegSeg) segmentPrefix) $ Add (Extend $ Get $ Low AX) (Get BX)

    Ilea -> c $ setOp1w op2addr'
    _ | inOpcode `elem` [Iles, Ilds] -> stop $ addr2 op2 $ \(ad, ad2) -> do
        setOp1w ad
        set (case inOpcode of Iles -> Es; Ilds -> Ds) ad2

    _ -> case sizeByte of
        1 -> c $ withSize getByteOperand byteOperand (Low AX) (High AX) AX
        2 -> c $ withSize getWordOperand wordOperand AX DX DXAX
  where
    withSize :: forall a . (AsSigned a, Extend a, Extend (Signed a), AsSigned (X2 a), X2 (Signed a) ~ Signed (X2 a))
        => (Maybe Segment -> Operand -> Exp a)
        -> (Maybe Segment -> Operand -> Part a)
        -> Part a
        -> Part a
        -> Part (X2 a)
        -> ExpM ()
    withSize getTr tr_ alx ahd axd = case inOpcode of
        Imov  -> set op1' op2v
        Ixchg -> LetM op1v $ \o1 -> do
            set op1' op2v
            set op2' o1
        Inot  -> modif op1' Not

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
        Iidiv -> divide signed Signed
        Imul  -> multiply id
        Iimul -> multiply signed

        _ | inOpcode `elem` [Icwd, Icbw] -> set axd $ Convert $ Signed $ Get alx
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

        Iin  -> Input (getWordOperand segmentPrefix op2) $ set op1' . Convert
        Iout -> output (getWordOperand segmentPrefix op1) $ convert op2v

      where
        si'', di'' :: Part a
        si'' = tr_ segmentPrefix $ Mem $ memIndex RSI
        di'' = tr_ (Just $ fromMaybe ES segmentPrefix) $ Mem $ memIndex RDI

        adjustIndex i = modif i $ Add $ If (Get DF) (C $ -sizeByte) (C sizeByte)

        op1' = tr_ segmentPrefix op1
        op2' = tr_ segmentPrefix op2
        op1v = getTr segmentPrefix op1
        op2v = getTr segmentPrefix op2

        divide :: (Integral a, Integral c, Integral (X2 c)) => (Exp a -> Exp c) -> (Exp (X2 a) -> Exp (X2 c)) -> ExpM ()
        divide asSigned asSigned' =
            LetM (QuotRem (asSigned' $ Get axd) (convert $ asSigned op1v)) $ \t -> do
                    set alx $ Convert $ Fst t
                    set ahd $ Convert $ Snd t

        multiply :: forall c . (Extend c, FiniteBits (X2 c)) => (Exp a -> Exp c) -> ExpM ()
        multiply asSigned =
            LetM (Mul (Extend $ asSigned $ Get alx) (extend' $ asSigned op1v)) $ \r ->
            LetM (Not $ Eq r $ Extend (Convert r :: Exp c)) $ \c -> do
                set axd $ Convert r
                set CF c
                set OF c
                uSet SF
                uSet PF
                set ZF $ C False    -- needed for Stunts

        shiftOp :: (forall b . (AsSigned b) => Exp Bool -> Exp b -> (Exp Bool, Exp b)) -> ExpM ()
        shiftOp op = do
            letM (and' (C 0x1f) $ getByteOperand segmentPrefix op2) $ \n -> do
            when' (not' $ eq' (C 0) n) $ letM (iterate' (convert n) (uncurry Tuple . uncurry op . unTup) $ Tuple (Get CF) op1v) $ \t -> do
                let r = snd' t
                set CF $ fst' t
                set op1' r
                when (inOpcode `elem` [Isal, Isar, Ishl, Ishr]) $ do
                    set ZF $ Eq (C 0) r
                    set SF $ HighBit r
                    uSet OF
                    set PF $ EvenParity $ Convert r
                when (inOpcode `elem` [Ircl, Ircr, Irol, Iror]) $ do
                    uSet ZF
                    uSet SF
                    uSet OF
                    uSet PF

        twoOp :: Bool -> (forall b . (Integral b, FiniteBits b) => Exp b -> Exp b -> Exp b) -> ExpM ()
        twoOp store op = twoOp_ store op op1' op2v

        twoOp_ :: AsSigned a => Bool -> (forall a . (Integral a, FiniteBits a) => Exp a -> Exp a -> Exp a) -> Part a -> Exp a -> ExpM ()
        twoOp_ store op op1 op2 = LetM (Get op1) $ \a -> letM op2 $ \b -> letM (op a b) $ \r -> do

            when (inOpcode `notElem` [Idec, Iinc]) $
                set CF $ Not $ Eq (Convert r) $ op (Convert a :: Exp Int) (convert b)
            set OF $ Not $ Eq (Convert $ Signed r) $ op (Convert $ Signed a :: Exp Int) (convert $ signed b)

            set ZF $ Eq (C 0) r
            set SF $ HighBit r
            set PF $ EvenParity $ Convert r

            when store $ set op1 r

    c m = m >> cc
    cc = cont nextip
    stop m = m >> end
    end = jump (C cs) (C nextip)
    nextip = ip + fromIntegral (mdLength mdat)

    far = " far " `isInfixOf` mdAssembly mdat

    addr2 (Mem m) f = letM (addressOf segmentPrefix m) $ \ad -> f (Get $ Heap16 ad, Get $ Heap16 $ Add (C 2) ad)

    loop cond = do
        modif CX $ Add $ C $ -1
        condJump $ and'' cond (Not $ Eq (C 0) (Get CX))

    condJump :: Exp Bool -> ExpM Jump'
    condJump b = ifM b (jump (C cs) getOp1w) cc

    sizeByte :: Word16
    sizeByte = fromIntegral $ sizeByte_ i

    ~(op1: ~(op2:_)) = inOperands
    getOp1w = getWordOperand segmentPrefix op1
    setOp1w = set $ wordOperand segmentPrefix op1
    op2addr' = case op2 of Mem m -> addressOf' m

    segmentPrefix :: Maybe Segment
    segmentPrefix = case inPrefixes of
        [Seg s] -> Just s
        [] -> Nothing


    getSegOf = \case
        RegIP     -> error "segOf RegIP"
        Reg16 RSP -> C ss
        Reg16 RBP -> C ss
        _         -> gds

    gds = maybe (Get Ds) C ds

    getReg :: Register -> Exp Word16
    getReg = \case
        RegNone -> C 0
        RegIP -> C nextip
        RegSeg s -> case s of
            SS -> C ss
            CS -> C cs
            ES -> maybe (Get Es) C es
            DS -> gds
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

    addressOf :: Maybe Segment -> Memory -> Exp Int
    addressOf segmentPrefix m
        = segAddr_ (maybe (getSegOf $ mBase m) (getReg . RegSeg) segmentPrefix) (addressOf' m)

    addressOf' :: Memory -> Exp Word16
    addressOf' (Memory _ r r' 0 i) = add (C $ imm i) $ add (getReg r) (getReg r')

    getByteOperand segmentPrefix = \case
        Imm (Immediate Bits8 v) -> C $ fromIntegral v
        Hdis86.Const (Immediate Bits0 0) -> C 1 -- !!!
        x -> Get $ byteOperand segmentPrefix x

    byteOperand :: Maybe Segment -> Operand -> Part Word8
    byteOperand segmentPrefix = \case
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

    getWordOperand segmentPrefix = \case
        Imm i  -> C $ imm' i
        Jump i -> C $ imm i + nextip
        Reg r  -> getReg r
        Mem m  -> Get $ Heap16 $ addressOf segmentPrefix m

    wordOperand :: Maybe Segment -> Operand -> Part Word16
    wordOperand segmentPrefix = \case
        Reg r  -> reg r
        Mem m  -> Heap16 $ addressOf segmentPrefix m


    imm = fromIntegral . iValue
    -- patched version
    imm' (Immediate Bits8 i) = fromIntegral (fromIntegral i :: Int8)
    imm' i = imm i

    memIndex r = Memory undefined (Reg16 r) RegNone 0 $ Immediate Bits0 0

    stackTop :: Part Word16
    stackTop = Heap16 $ segAddr_ (C ss) $ Get SP

    push :: Exp Word16 -> ExpM ()
    push x = do
        modif SP $ Add $ C $ -2
        set stackTop x

    pop :: (Exp Word16 -> ExpM e) -> ExpM e
    pop cont = LetM (Get stackTop) $ \x -> do
        modif SP $ Add $ C 2
        cont x

    interrupt :: Exp Word16 -> Exp Word8 -> ExpM Jump'
    interrupt cs v = letM (mul (C 4) $ convert v) $ \v -> do
    --    trace_ $ "interrupt " ++ showHex' 2 v
        push $ Get Flags
        push $ cs
        push $ C nextip
        set IF $ C False
        jump (Get $ Heap16 $ add (C 2) v) (Get $ Heap16 v)

    segAddr_ :: Exp Word16 -> Exp Word16 -> Exp Int
    segAddr_ (C s) (C o) = C $ segAddr s o
    segAddr_ seg off = SegAddr seg off

    move a b = set a $ Get b

    modif p f = set p $ f $ Get p

maxInstLength = 7


