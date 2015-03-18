module DeBruijn
    ( EExp (..)
    , EExpM (..)
    , List (..)
    , Var (..)
    , convExpM
    , spTrans
    ) where

import Data.Word
import Data.Bits hiding (bit)
import Unsafe.Coerce

import Edsl

--------------------------

data List a = Con a (List a) | Nil

data Var :: List * -> * -> * where
    VarZ :: Var (Con a e) a
    VarS :: Var e a -> Var (Con b e) a

data EExp :: List * -> * -> * where
    Var' :: Var e a -> EExp e a

    C' :: a -> EExp e a
    Let' :: EExp e a -> EExp (Con a e) b -> EExp e b
    Iterate' :: EExp e Int -> EExp (Con a e) a -> EExp e a -> EExp e a

    Tuple' :: EExp e a -> EExp e b -> EExp e (a, b)
    Fst' :: EExp e (a, b) -> EExp e a
    Snd' :: EExp e (a, b) -> EExp e b
    If' :: EExp e Bool -> EExp e a -> EExp e a -> EExp e a

    Get' :: Part_ (EExp e) a -> EExp e a

    Eq' :: Eq a => EExp e a -> EExp e a -> EExp e Bool
    Sub', Add', Mul' :: Num a => EExp e a -> EExp e a -> EExp e a
    QuotRem' :: Integral a => EExp e a -> EExp e a -> EExp e (a, a)
    And', Or', Xor' :: Bits a => EExp e a -> EExp e a -> EExp e a
    Not', ShiftL', ShiftR', RotateL', RotateR' :: Bits a => EExp e a -> EExp e a
    EvenParity' :: EExp e Word8 -> EExp e Bool

    Convert' :: (Integral a, Num b) => EExp e a -> EExp e b
    SegAddr' :: EExp e Word16 -> EExp e Word16 -> EExp e Int

--    Lift' :: EExp e a -> EExp (Con x e) a

instance Eq a => Eq (EExp e a) where
    C' a == C' b = a == b 
    Get' a == Get' b = a == b
    _ == _ = False

data EExpM :: List * -> * -> * where
    Stop' :: a -> EExpM e a
    Set' :: Part_ (EExp e) a -> EExp e a -> EExpM e x -> EExpM e x

    Jump'' :: EExp e Word16 -> EExp e Word16 -> EExpM e Jump'
    LetM' :: EExp e a -> EExpM (Con a e) b -> EExpM e b
    LetMC' :: EExp e a -> EExpM (Con a e) () -> EExpM e b -> EExpM e b
    IfM' :: EExp e Bool -> EExpM e a -> EExpM e a -> EExpM e a
    Replicate' :: Integral a => EExp e a -> EExp e Bool -> EExpM e () -> EExpM (Con a e) x -> EExpM e x

    Input' :: EExp e Word16 -> EExpM (Con Word16 e) x -> EExpM e x
    Output' :: EExp e Word16 -> EExp e Word16 -> EExpM e x -> EExpM e x

data Layout :: List * -> List * -> * where
  EmptyLayout :: Layout env Nil
  PushLayout  :: {-Typeable t 
              => -}Layout env env' -> Var env t -> Layout env (Con t env')

size :: Layout env env' -> Int
size EmptyLayout        = 0
size (PushLayout lyt _) = size lyt + 1

inc :: Layout env env' -> Layout (Con t env) env'
inc EmptyLayout         = EmptyLayout
inc (PushLayout lyt ix) = PushLayout (inc lyt) (VarS ix)

prjIx :: Int -> Layout env env' -> Var env t
prjIx _ EmptyLayout       = error "Convert.prjIx: internal error"
prjIx 0 (PushLayout _ ix) = unsafeCoerce ix
prjIx n (PushLayout l _)  = prjIx (n - 1) l

convExp_ :: forall a e . Layout e e -> Exp a -> EExp e a
convExp_ lyt = g where
      h :: forall a e . Layout e e -> Exp a -> EExp e a
      h = convExp_

      g :: forall a . Exp a -> EExp e a
      g = \case
        Var sz -> Var' (prjIx (size lyt - sz - 1) lyt)

        C a -> C' a
        Let e f -> Let' (g e) $ h (inc lyt `PushLayout` VarZ) $ f $ Var (size lyt)
        Iterate n f e -> Iterate' (g n) (h (inc lyt `PushLayout` VarZ) $ f $ Var (size lyt)) (g e)

        Tuple a b -> Tuple' (g a) (g b)
        Fst a -> Fst' $ g a
        Snd a -> Snd' $ g a
        If a b c -> If' (g a) (g b) (g c)

        Get p -> Get' (convPart lyt p)

        Eq a b -> Eq' (g a) (g b)
        Sub a b -> Sub' (g a) (g b)
        Add a b -> Add' (g a) (g b)
        Mul a b -> Mul' (g a) (g b)
        QuotRem a b -> QuotRem' (g a) (g b)
        And a b -> And' (g a) (g b)
        Or a b -> Or' (g a) (g b)
        Xor a b -> Xor' (g a) (g b)
        SegAddr a b -> SegAddr' (g a) (g b)
        Not a -> Not' (g a)
        ShiftL a -> ShiftL' (g a)
        ShiftR a -> ShiftR' (g a)
        RotateL a -> RotateL' (g a)
        RotateR a -> RotateR' (g a)
        EvenParity a -> EvenParity' (g a)
        Convert a -> Convert' (g a)

convExpM :: ExpM a -> EExpM Nil a
convExpM = f EmptyLayout where
    h :: forall a e . Layout e e -> Exp a -> EExp e a
    h = convExp_

    f :: forall e a . Layout e e -> ExpM a -> EExpM e a
    f lyt = k where
      q :: forall a . Exp a -> EExp e a
      q = h lyt

      k :: forall a . ExpM a -> EExpM e a
      k = \case
        LetM e g -> LetM' (q e) $ f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)
        LetMC e g x -> LetMC' (q e) (f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)) (k x)
        Input e g -> Input' (q e) $ f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)

--        Seq a b -> Seq' (k a) (k b)
        IfM a b c -> IfM' (q a) (k b) (k c)
        Replicate n b a g -> Replicate' (q n) (q b) (k a) $ f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)
--        Nop -> Nop'
        Jump' cs ip -> Jump'' (q cs) (q ip) --Seq' (Set' (convPart lyt Cs) (q cs)) (Set' (convPart lyt IP) (q ip))
        Set Cs _ _ -> error "convExpM: set cs"
--        Set IP _ -> error "convExpM: set ip"
        Set p e cont -> Set' (convPart lyt p) (q e) $ k cont
        Output a b cont -> Output' (q a) (q b) $ k cont
        Stop a -> Stop' a

convPart :: Layout e e -> Part_ Exp a -> Part_ (EExp e) a
convPart lyt = mapPart (convExp_ lyt)

----------------------------

lift' :: EExp e a -> EExp (Con x e) a
lift' = lift'' VarS

incV :: (Var e a -> Var f a) -> Var (Con x e) a -> Var (Con x f) a
incV f VarZ = VarZ
incV f (VarS x) = VarS $ f x

lift'' :: forall e e' . (forall x . Var e x -> Var e' x) -> forall a . EExp e a -> EExp e' a
lift'' gv = f where
  f :: forall x . EExp e x -> EExp e' x
  f = \case
    Get' p -> Get' $ mapPart f p
    C' c -> C' c
    Var' c -> Var' $ gv c
    Fst' p -> Fst' $ f p
    Snd' p -> Snd' $ f p
    Tuple' a b -> Tuple' (f a) (f b)
    If' a b c -> If' (f a) (f b) (f c)
    Let' e x -> Let' (f e) (lift'' (incV gv) x)
    Iterate' n g c -> Iterate' (f n) (lift'' (incV gv) g) (f c)
    Eq' a b -> Eq' (f a) (f b)
    Sub' a b -> Sub' (f a) (f b)
    Add' a b -> Add' (f a) (f b)
    Mul' a b -> Mul' (f a) (f b)
    And' a b -> And' (f a) (f b)
    Or' a b -> Or' (f a) (f b)
    Xor' a b -> Xor' (f a) (f b)
    SegAddr' a b -> SegAddr' (f a) (f b)
    QuotRem' a b -> QuotRem' (f a) (f b)
    Not' a -> Not' (f a)
    ShiftL' a -> ShiftL' (f a)
    ShiftR' a -> ShiftR' (f a)
    RotateL' a -> RotateL' (f a)
    RotateR' a -> RotateR' (f a)
    EvenParity' a -> EvenParity' (f a)
    Convert' a -> Convert' (f a)

spTrE :: forall e a . EExp e Word16 -> EExp e a -> EExp e a
spTrE sp = f where
  f :: forall x . EExp e x -> EExp e x
  f = \case
    Get' SP -> sp
    Get' x -> Get' x

    C' c -> C' c
    Var' c -> Var' c
    Fst' p -> Fst' $ f p
    Snd' p -> Snd' $ f p
    Tuple' a b -> Tuple' (f a) (f b)
    If' a b c -> If' (f a) (f b) (f c)
    Let' e x -> Let' (f e) (spTrE (lift' sp) x)
    Iterate' n g c -> Iterate' (f n) (spTrE (lift' sp) g) (f c)
    Eq' a b -> Eq' (f a) (f b)
    Sub' a b -> Sub' (f a) (f b)
    Add' a b -> Add' (f a) (f b)
    Mul' a b -> Mul' (f a) (f b)
    And' a b -> And' (f a) (f b)
    Or' a b -> Or' (f a) (f b)
    Xor' a b -> Xor' (f a) (f b)
    SegAddr' a b -> SegAddr' (f a) (f b)
    QuotRem' a b -> QuotRem' (f a) (f b)
    Not' a -> Not' (f a)
    ShiftL' a -> ShiftL' (f a)
    ShiftR' a -> ShiftR' (f a)
    RotateL' a -> RotateL' (f a)
    RotateR' a -> RotateR' (f a)
    EvenParity' a -> EvenParity' (f a)
    Convert' a -> Convert' (f a)

------------------------------------

add' (C' i) (Add' (C' j) x) = add' (C' (i+j)) x
add' a b = Add' a b

add_ (Add' (C' j) x) = (j, x)
add_ v = (0, v)

spTrans :: EExpM e a -> EExpM e a
spTrans = spTr (Get' SP)

spTr :: EExp e Word16 -> EExpM e a -> EExpM e a
spTr sp (Set' SP (add_ -> (i, Get' SP)) c) = spTr (add' (C' i) sp) c
spTr sp (Set' SP v c) = Set' SP (spTrE sp v) (spTr (Get' SP) c)
spTr sp (Set' p v c) = Set' p (spTrE sp v) (spTr sp c)
spTr (Get' SP) x@Jump''{} = x
spTr sp x@Jump''{} = Set' SP sp x
spTr sp (IfM' a b c) = IfM' (spTrE sp a) (spTr sp b) (spTr sp c)
spTr sp (Output' a b c) = Output' (spTrE sp a) (spTrE sp b) (spTr sp c) 
spTr sp (Input' a c) = Input' (spTrE sp a) (spTr (lift' sp) c)
spTr sp (LetM' a c) = LetM' (spTrE sp a) (spTr (lift' sp) c)
spTr sp (Replicate' n b x c) = Replicate' n b x (spTr (lift' sp) c)
spTr _ Stop'{} = error "spTr Stop"
spTr _ LetMC'{} = error "spTr LetMC"

