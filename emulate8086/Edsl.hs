module Edsl where

import Data.Word
import Data.Bits
import Control.Applicative
import Control.Monad
import Prelude

import Helper

----------------------------------------

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
    _ == _ = False  -- TODO

mapPart :: (forall a . e a -> f a) -> Part_ e a -> Part_ f a
mapPart f = \case
    Heap8 a  -> Heap8 (f a)
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

--------------------------------------------------------------------------------

data Exp_ (v :: * -> *) (c :: * -> * -> *) a where
    Var :: v a -> Exp_ v c a

    C :: a -> Exp_ v c a
    Let :: Exp_ v c a -> c a b -> Exp_ v c b
    Tuple :: Exp_ v c a -> Exp_ v c b -> Exp_ v c (a, b)
    Fst :: Exp_ v c (a, b) -> Exp_ v c a
    Snd :: Exp_ v c (a, b) -> Exp_ v c b
    Iterate :: Exp_ v c Int -> c a a -> Exp_ v c a -> Exp_ v c a
    If :: Exp_ v c Bool -> Exp_ v c a -> Exp_ v c a -> Exp_ v c a

    Get :: Part_ (Exp_ v c) a -> Exp_ v c a

    Eq :: Eq a => Exp_ v c a -> Exp_ v c a -> Exp_ v c Bool
    Add, Mul :: (Num a, Eq a) => Exp_ v c a -> Exp_ v c a -> Exp_ v c a
    QuotRem :: Integral a => Exp_ v c a -> Exp_ v c a -> Exp_ v c (a, a)
    And, Or, Xor :: Bits a => Exp_ v c a -> Exp_ v c a -> Exp_ v c a
    Not, ShiftL, ShiftR, RotateL, RotateR :: Bits a => Exp_ v c a -> Exp_ v c a
    EvenParity :: Exp_ v c Word8 -> Exp_ v c Bool

    Convert :: (Integral a, Num b) => Exp_ v c a -> Exp_ v c b
    SegAddr :: Exp_ v c Word16 -> Exp_ v c Word16 -> Exp_ v c Int

unTup x = (fst' x, snd' x)

pattern Neg a = Mul (C (-1)) a
pattern Sub a b = Add a (Neg b)

add (C c) (C c') = C $ c + c'
add (C c) (Add (C c') v) = add (C $ c + c') v
add (C 0) x = x
add a (C c) = add (C c) a
add (Neg a) (Neg b) = Neg (add a b)
add a b = Add a b

sub a b = add a (mul (C $ -1) b)

mul (C c) (C c') = C $ c * c'
mul (C c) (Mul (C c') x) = mul (C $ c * c') x   -- signed modulo multiplication is also associative
mul (C 0) x = C 0
mul (C 1) x = x
mul x (C c) = mul (C c) x
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

convert :: (Num b, Integral a) => Exp_ v c a -> Exp_ v c b
convert (C a) = C $ fromIntegral a
convert e = Convert e

iterate' (C 0) f e = e
iterate' (C 1) f e = f e
iterate' n f e = Iterate n (Fun f) e

extend' :: Extend a => Exp_ v c a -> Exp_ v c (X2 a)
extend' = convert

signed :: AsSigned a => Exp_ v c a -> Exp_ v c (Signed a)
signed = convert

highBit :: (Integral a, Bits a) => Exp_ v c a -> Exp_ v c Bool
highBit = Convert . RotateL

setHighBit :: (Num a, Bits a) => Exp_ v c Bool -> Exp_ v c a -> Exp_ v c a
setHighBit c = Or (RotateR $ Convert c)

-- TODO: abstract add, mul
{-# INLINE foldExp #-}
foldExp :: forall v v' c c' a
     . (forall x y . c x y -> c' x y)
    -> (forall x . v x -> Exp_ v' c' x)
    -> (forall x . Part_ (Exp_ v c) x -> Exp_ v' c' x)
    -> Exp_ v c a -> Exp_ v' c' a
foldExp tr var get = f where
  f :: Exp_ v c x -> Exp_ v' c' x
  f = \case
    Var c -> var c
    Get x -> get x
    C c -> C c
    Fst p -> Fst $ f p
    Snd p -> Snd $ f p
    Tuple a b -> Tuple (f a) (f b)
    If a b c -> If (f a) (f b) (f c)
    Let e x -> Let (f e) (tr x)
    Iterate n g c -> Iterate (f n) (tr g) (f c)
    Eq a b -> Eq (f a) (f b)
    Add a b -> add (f a) (f b)
    Mul a b -> mul (f a) (f b)
    And a b -> And (f a) (f b)
    Or a b -> Or (f a) (f b)
    Xor a b -> Xor (f a) (f b)
    SegAddr a b -> SegAddr (f a) (f b)
    QuotRem a b -> QuotRem (f a) (f b)
    Not a -> Not (f a)
    ShiftL a -> ShiftL (f a)
    ShiftR a -> ShiftR (f a)
    RotateL a -> RotateL (f a)
    RotateR a -> RotateR (f a)
    EvenParity a -> EvenParity (f a)
    Convert a -> Convert (f a)

instance Eq a => Eq (Exp_ v c a) where
    C a == C b = a == b 
    Get a == Get b = a == b
    _ == _ = False      -- TODO

------------------------------------ HOAS

newtype Co a = Co Int

newtype Fun a b = Fun {getFun :: Exp a -> Exp b}

type Exp = Exp_ Co Fun

type Part = Part_ Exp

---------------------- DeBruijn

data List a = Con a (List a) | Nil

data Var :: List * -> * -> * where
    VarZ :: Var (Con a e) a
    VarS :: Var e a -> Var (Con b e) a

newtype DB e a b = DB {getDB :: EExp (Con a e) b}

type EExp e = Exp_ (Var e) (DB e)

--------------------------------------------------------------------------------

data Jump' = JumpAddr Word16 Word16

data ExpM_ (e :: * -> *) (c :: * -> * -> *) a where
    Stop :: a -> ExpM_ e c a
    Set :: Part_ e b -> e b -> ExpM_ e c a -> ExpM_ e c a

    Jump' :: e Word16 -> e Word16 -> ExpM_ e c Jump'
    -- constrained let type (with more efficient interpretation) 
    LetMC :: e b -> c b () -> ExpM_ e c a -> ExpM_ e c a
    LetM :: e b -> c b a -> ExpM_ e c a
    IfM :: e Bool -> ExpM_ e c a -> ExpM_ e c a -> ExpM_ e c a
    Replicate :: Integral b => e b -> e Bool -> ExpM_ e c () -> c b a -> ExpM_ e c a

    Input :: e Word16 -> c Word16 a -> ExpM_ e c a
    Output :: e Word16 -> e Word16 -> ExpM_ e c a -> ExpM_ e c a

class CC c where
    type Ex c :: * -> *
    ret :: c a (Ex c a)
    (.>=>) :: c a b -> (b -> ExM c x) -> c a x

type ExM c = ExpM_ (Ex c) c

instance (CC c, e ~ Ex c) => Functor (ExpM_ e c) where
    fmap  = liftM

instance (CC c, e ~ Ex c) => Applicative (ExpM_ e c) where
    pure  = return
    (<*>) = ap  -- defined in Control.Monad

instance (CC c, e ~ Ex c) => Monad (ExpM_ e c) where
    return = Stop
    a >>= f = case a of
        Stop x -> f x
        Set a b e -> Set a b $ e >>= f
        LetMC e x g -> LetMC e x $ g >>= f
        LetM e g -> LetM e $ g .>=> f
        IfM b x y -> IfM b (x >>= f) (y >>= f)
        Replicate n b m g -> Replicate n b m $ g .>=> f
        Input e g -> Input e $ g .>=> f
        Output a b e -> Output a b $ e >>= f
        Jump' _ _ -> error "Jump' >>="


set :: CC c => Part_ (Ex c) a -> Ex c a -> ExM c ()
set x y = Set x y (return ())

ifM (C c) a b = if c then a else b
ifM x a b = IfM x a b

-- letM :: CC c => Ex c a -> ExM c (Ex c a)  -- ambiguous
letM :: Exp a -> ExpM (Exp a)
letM x@(C c) = return x
letM x = LetM x ret

-- letMC, letMC' :: CC c => Ex c a -> (Ex c a -> ExM c ()) -> ExM c () -- ambiguous
letMC, letMC' :: Exp a -> (Exp a -> ExpM ()) -> ExpM ()
letMC (C c) f = f (C c)
letMC x f = LetMC x (ret .>=> f) (return ())

letMC' x f = letM x >>= f

output a b = Output a b (return ())

---------------------- HOAS

newtype FunM a b = FunM {getFunM :: Exp a -> ExpM b}

instance CC FunM where
    type Ex FunM = Exp
    FunM f .>=> g = FunM $ f >=> g
    ret = FunM return

type ExpM = ExM FunM

-------------------------- DeBruijn

newtype DBM e a b = DBM {getDBM :: EExpM (Con a e) b}
{-
instance CC (DBM e) where
    type Ex (DBM e) = EExp
-}
type EExpM e = ExpM_ (EExp e) (DBM e)

