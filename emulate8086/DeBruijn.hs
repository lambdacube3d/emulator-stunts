module DeBruijn
    {-( EExp (..), Sub'
    , EExpM (..)
    , List (..)
    , Var (..)
    , convExpM
    , spTrans
    )-} where

import Data.Word
import Unsafe.Coerce

import Edsl

--------------------------

data List a = Con a (List a) | Nil

data Var :: List * -> * -> * where
    VarZ :: Var (Con a e) a
    VarS :: Var e a -> Var (Con b e) a

type EExp e = Exp_ (Var e) (DB e)

newtype DB e a b = DB {getDB :: EExp (Con a e) b}
newtype DBM e a b = DBM {getDBM :: EExpM (Con a e) b}

instance Eq a => Eq (EExp e a) where
    C a == C b = a == b 
    Get a == Get b = a == b
    _ == _ = False      -- TODO

type EExpM e = ExpM_ (Var e) (DBM e) (DB e)

data Layout :: List * -> List * -> * where
  EmptyLayout :: Layout env Nil
  PushLayout  :: {-Typeable t =>-} Layout env env' -> Var env t -> Layout env (Con t env')

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
convExp_ lyt = foldExp
    (\(Fun f) -> DB $ convExp_ (inc lyt `PushLayout` VarZ) $ f $ Var $ Co $ size lyt)
    (\(Co sz) -> Var (prjIx (size lyt - sz - 1) lyt))
    (Get . convPart lyt)

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
        LetM e (FunM g) -> LetM (q e) $ DBM $ f (inc lyt `PushLayout` VarZ) $ g $ Var $ Co $ size lyt
--        LetMC e g x -> LetMC (q e) (f (inc lyt `PushLayout` VarZ) $ g $ Var (size lyt)) (k x)
        Input e (FunM g) -> Input (q e) $ DBM $ f (inc lyt `PushLayout` VarZ) $ g $ Var $ Co $ size lyt

--        Seq a b -> Seq' (k a) (k b)
        IfM a b c -> IfM (q a) (k b) (k c)
        Replicate n b a (FunM g) -> Replicate (q n) (q b) (k a) $ DBM $ f (inc lyt `PushLayout` VarZ) $ g $ Var $ Co $ size lyt
--        Nop -> Nop'
        Jump' cs ip -> Jump' (q cs) (q ip) --Seq' (Set (convPart lyt Cs) (q cs)) (Set (convPart lyt IP) (q ip))
        Set Cs _ _ -> error "convExpM: set cs"
--        Set IP _ -> error "convExpM: set ip"
        Set p e cont -> Set (convPart lyt p) (q e) $ k cont
        Output a b cont -> Output (q a) (q b) $ k cont
        Stop a -> Stop a

convPart :: Layout e e -> Part_ Exp a -> Part_ (EExp e) a
convPart lyt = mapPart (convExp_ lyt)

----------------------------

lift' :: EExp e a -> EExp (Con x e) a
lift' = lift'' VarS

incV :: (Var e a -> Var f a) -> Var (Con x e) a -> Var (Con x f) a
incV f VarZ = VarZ
incV f (VarS x) = VarS $ f x

lift'' :: forall e e' . (forall x . Var e x -> Var e' x) -> forall a . EExp e a -> EExp e' a
lift'' gv = foldExp (\(DB x) -> DB $ lift'' (incV gv) x) (Var . gv) (Get . mapPart (lift'' gv))

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

spTrE :: forall e a . EExp e Word16 -> EExp e a -> EExp e a
spTrE sp = foldExp (\(DB c) -> DB $ spTrE (lift' sp) c) Var get
  where
    get :: Part_ (EExp e) x -> EExp e x
    get SP = sp
    get x = Get x

------------------------------------

add_ (Add (C j) x) = (j, x)
add_ v = (0, v)

pattern Neg' a = Mul (C (-1)) a
pattern Sub' a b = Add a (Neg' b)

spTrans :: EExpM e a -> EExpM e a
spTrans = spTr (Get SP)

spTr :: EExp e Word16 -> EExpM e a -> EExpM e a
spTr sp (Set SP (add_ -> (i, Get SP)) c) = spTr (add (C i) sp) c
spTr sp (Set SP v c) = Set SP (spTrE sp v) (spTr (Get SP) c)
spTr sp (Set p v c) = Set p (spTrE sp v) (spTr sp c)
spTr (Get SP) x@Jump'{} = x
spTr sp x@Jump'{} = Set SP sp x
spTr sp (IfM a b c) = IfM (spTrE sp a) (spTr sp b) (spTr sp c)
spTr sp (Output a b c) = Output (spTrE sp a) (spTrE sp b) (spTr sp c) 
spTr sp (Input a (DBM c)) = Input (spTrE sp a) (DBM $ spTr (lift' sp) c)
spTr sp (LetM a (DBM c)) = LetM (spTrE sp a) (DBM $ spTr (lift' sp) c)
spTr sp (Replicate n b x (DBM c)) = Replicate n b x (DBM $ spTr (lift' sp) c)
spTr _ Stop{} = error "spTr Stop"
--spTr _ LetMC{} = error "spTr LetMC"

