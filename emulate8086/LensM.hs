{-# LANGUAGE NoMonomorphismRestriction #-}
--{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

import Data.Char  -- for examples
import Data.Monoid
import Data.Functor.Compose

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

import Control.Lens
import Control.Lens.Internal.Iso (Exchange (..))
import Control.Lens.Internal.Indexed (Indexing (..))
import Control.Lens.Action.Internal (Effect (..))

-------------------

newtype IdentityT m a = IdentityT { runIdentityT :: m a }
    deriving (Functor, Contravariant, Applicative, Monad)

--------------

class Functor f => FunctorM m f | f -> m where
    joinL :: m (f a) -> f a
    joinR :: f (m a) -> f a
instance Monad m => FunctorM m (Effect m a) where
    joinL = Effect . (>>= getEffect)
    joinR = Effect . getEffect
instance (Functor m, Monad m) => FunctorM m (IdentityT m) where
    joinL = IdentityT . (>>= runIdentityT)
    joinR = IdentityT . join . runIdentityT

class Profunctor p => ProfunctorM m p where
    dimapM :: forall f a b c d . FunctorM m f => (a -> m b) -> (c -> m d) -> p b (f c) -> p a (f d)
instance Functor f => ProfunctorM f (->) where
    dimapM f g h = joinR . fmap g . joinL . fmap h . f
instance Monad m => ProfunctorM m (Exchange (IdentityT m a) b) where
    dimapM f g (Exchange k l) = Exchange (IdentityT . f >=> k) (joinR . fmap g . l)

type IsoM m s t a b = forall p f . (ProfunctorM m p, FunctorM m f) => Optic p f s t a b
type AnIsoM m s t a b = ExchangeM m a b a b -> ExchangeM m a b s t
type ExchangeM m a b s t = Exchange (IdentityT m a) b s (IdentityT m t)
type LensM m s t a b = forall f . FunctorM m f => LensLike f s t a b
type GettingM m r s a = (a -> Effect m r a) -> s -> Effect m r s
type SettingM m p s t a b = p a (IdentityT m b) -> s -> IdentityT m t
type ASetterM m s t a b = SettingM m (->) s t a b

----------------------

isoM :: (s -> f a) -> (b -> f t) -> IsoM f s t a b
isoM = dimapM

fromM :: Applicative f => AnIsoM f s t a b -> IsoM f b a t s
fromM l = withIsoM l $ \ sa bt -> isoM bt sa

withIsoM :: Applicative f => AnIsoM f s t a b -> ((s -> f a) -> (b -> f t) -> r) -> r
withIsoM ai k = case ai (Exchange pure pure) of
  Exchange sa bt -> k (runIdentityT . sa) (runIdentityT . bt)

lensM :: Functor f => (s -> f a) -> (s -> b -> f t) -> LensM f s t a b
lensM f g tr s = joinR . fmap (g s) . joinL . fmap tr $ f s

(%~!) :: ProfunctorM f p => SettingM f p s t a b -> p a (f b) -> s -> f t
k %~! b = runIdentityT . k (rmap IdentityT b)

(.~!) :: Functor f => ASetterM f s t a b -> f b -> s -> f t
k .~! b = k %~! const b

(^.!) :: Applicative f => s -> GettingM f a s a -> f a
x ^.! k = getEffect . k (Effect . pure) $ x

(%=!) :: (ProfunctorM m p, MonadState s m) => SettingM m p s s a b -> p a (m b) -> m ()
k %=! b = get >>= k %~! b >>= put

(.=!) :: (Functor m, MonadState s m) => ASetterM m s s a b -> m b -> m ()
k .=! b = k %=! const b

useM :: (Applicative m, MonadState s m) => GettingM m a s a -> m a
useM k = get >>= (^.! k)

infix 4 %=!, .=!
infixr 4 %~!, .~!
infixl 8 ^.!

-------------------

{-
---------------
st ->          (True,["hel","lo"],Left (Sum {getSum = 3}))
_2 ->          ["hel","lo"]
to length ->   2
---------------
st ->          (True,["hel","lo"],Left (Sum {getSum = 3}))
_1 ->          True
notting ->     False
not            True
notting <-     True
_1 <-          False
st <-          (False,["hel","lo"],Left (Sum {getSum = 3}))
---------------
st ->          (False,["hel","lo"],Left (Sum {getSum = 3}))
_3 ->          Left (Sum {getSum = 3})
_Left ->       Sum {getSum = 3}
+1             Sum {getSum = 4}
_Left <-       Sum {getSum = 4}
_3 <-          Left (Sum {getSum = 4})
st <-          (False,["hel","lo"],Left (Sum {getSum = 4}))
---------------
st ->          (False,["hel","lo"],Left (Sum {getSum = 4}))
_3 ->          Left (Sum {getSum = 4})
_3 <-          Left (Sum {getSum = 4})
st <-          (False,["hel","lo"],Left (Sum {getSum = 4}))
---------------
-}
testL = putStrLn $ snd $ runWriter $ flip runStateT (True, ["hel","lo"] :: [String], Left 3 :: Either (Sum Int) Any) $ do
    next
    _ <- useM $ tracing "st" . _2 . tracing "_2" . to length . tracing "to length"
    next
    tracing "st" . _1 . tracing "_1" . iso not not . tracing "notting" %=! trace "not" . not
    next
    tracing "st" . _3 . tracing "_3" . _Left . tracing "_Left" %=! trace "+1" . (+1)
    next
    tracing "st" . _3 . tracing "_3" . _Right . tracing "_Right" %=! trace "True||" . (Any True `mappend`)
    next
  where
    next = tell $ replicate 15 '-' ++ "\n"

    trace f x = tell (f ++ replicate (15 - length f) ' ' ++ show x ++ "\n") >> return x

    tracing e = isoM (trace $ e ++ " ->") (trace $ e ++ " <-")


------------------- Indexed variants

type IndexedLensM m i s t a b = forall f . FunctorM m f => IndexedLensLike i f s t a b

--------

newtype IndexingM i m f a = IndexingM { runIndexingM_ :: Compose (StateT i m) f a }
    deriving (Functor, Applicative, Contravariant)

runIndexingM = getCompose . runIndexingM_

instance (FunctorM m f, Functor m, Monad m) => FunctorM m (IndexingM i m f) where
    joinL m = IndexingM $ Compose $ StateT $ \i -> m >>= flip runStateT i . runIndexingM
    joinR m = IndexingM $ Compose $ StateT $ \i -> fmap (joinR *** id) $ flip runStateT i $ runIndexingM m

indexingM :: (Applicative m, FunctorM m f, Num i) => LensLike (IndexingM i m f) s t a b -> IndexedLensLike i f s t a b
indexingM tr f s = joinL . fmap fst . flip runStateT 0 . runIndexingM .
              tr (\a -> IndexingM $ Compose $ StateT $ \i -> i `seq` pure (indexed f i a, i + 1)) $ s

--indexedLensM :: (Applicative m, Monad m) => (i -> s -> m a) -> (i -> s -> b -> m t) -> IndexedLensM m i s t a b
indexedLensM :: (Applicative m, Monad m, FunctorM m f) => (i -> s -> m a) -> (i -> s -> b -> m t) -> IndexedLensLike i (IndexingM i m f) s t a b
indexedLensM f g tr s
    = IndexingM $ Compose $ get >>= \i -> fmap joinR . runIndexingM . fmap (g i s) . joinL . fmap (indexed tr i) $ f i s

-----------

testI = putStrLn $ snd $ runWriter $ flip runStateT (True, ["hel","lo"] :: [String], Left 3 :: Either (Sum Int) Any) $ do
    next
    _ <- useM $ indexingM $ tracing "st" . _2 . tracing "_2" . folded . tracingI "folded#1" . folded . tracingI "folded#2" . iso ord chr . tracingI "ord" . iso Sum getSum
    next
    indexingM (tracing "st" . _2 . tracing "_2" . each . tracingI "each#1" . each . tracingI "each#2") %=! pure . toUpper
    next
  where
    next = tell $ replicate 15 '-' ++ "\n"

    trace f x = tell (f ++ replicate (15 - length f) ' ' ++ show x ++ "\n") >> return x

    tracing e = isoM (trace $ e ++ " ->") (trace $ e ++ " <-")

    tracingI e = indexedLensM (\i -> trace $ e ++ "[" ++ show i ++ "] ->")
                              (\i s -> trace $ e ++ "[" ++ show i ++ "] <-")



{-
-------------------------- Lenses

newtype IdentityT m a = IdentityT { runIdentityT :: m a }
    deriving (Functor, Applicative, Monad)

newtype IndexingM i m f a = IndexingM { runIndexingM :: StateT i m (f a) }
-- type IndexingM m f a = Compose (StateT Int m) f
instance (Functor m, Functor f) => Functor (IndexingM i m f) where
    fmap f = IndexingM . fmap (fmap f) . runIndexingM
instance (Monad m, Functor m, Applicative f) => Applicative (IndexingM i m f) where
    pure = IndexingM . pure . pure
    f <*> x = IndexingM $ (<*>) <$> runIndexingM f <*> runIndexingM x
instance (Monad m, Functor m, Contravariant f) => Contravariant (IndexingM i m f) where
    contramap f = IndexingM . fmap (contramap f) . runIndexingM

--------------

class Functor f => FunctorM m f | f -> m where
    joinL :: m (f a) -> f a
    joinR :: f (m a) -> f a
instance Monad m => FunctorM m (Effect m a) where
    joinL = Effect . (>>= getEffect)
    joinR = Effect . getEffect
instance (Functor m, Monad m) => FunctorM m (IdentityT m) where
    joinL = IdentityT . (>>= runIdentityT)
    joinR = IdentityT . join . runIdentityT
instance (FunctorM m f, Functor m, Monad m) => FunctorM m (IndexingM i m f) where
    joinL m = IndexingM $ StateT $ \i -> m >>= flip runStateT i . runIndexingM
    joinR m = IndexingM $ StateT $ \i -> fmap (joinR *** id) $ flip runStateT i $ runIndexingM m

class Profunctor p => ProfunctorM m p where
    dimapM :: forall f a b c d . FunctorM m f => (a -> m b) -> (c -> m d) -> p b (f c) -> p a (f d)
instance Monad m => ProfunctorM m (Exchange (IdentityT m a) b) where
    dimapM f g (Exchange k l) = Exchange (IdentityT . f >=> k) (joinR . fmap g . l)
instance Functor f => ProfunctorM f (->) where
    dimapM f g h = joinR . fmap g . joinL . fmap h . f

type LensM m s t a b = forall f . FunctorM m f => LensLike f s t a b
type IndexedLensM m i s t a b = forall f . FunctorM m f => IndexedLensLike i f s t a b
type IsoM m s t a b = forall p f . (ProfunctorM m p, FunctorM m f) => Optic p f s t a b
type AnIsoM m s t a b = ExchangeM m a b a b -> ExchangeM m a b s t
type ExchangeM m a b s t = Exchange (IdentityT m a) b s (IdentityT m t)
type GettingM m r s a = (a -> Effect m r a) -> s -> Effect m r s
type SettingM m p s t a b = p a (IdentityT m b) -> s -> IdentityT m t
type ASetterM m s t a b = SettingM m (->) s t a b

indexingM :: (Applicative m, FunctorM m f, Num i) => LensLike (IndexingM i m f) s t a b -> IndexedLensLike i f s t a b
indexingM tr f s = joinL . fmap fst . flip runStateT 0 . runIndexingM .
              tr (\a -> IndexingM $ StateT $ \i -> i `seq` pure (indexed f i a, i + 1)) $ s

withIsoM :: Applicative f => AnIsoM f s t a b -> ((s -> f a) -> (b -> f t) -> r) -> r
withIsoM ai k = case ai (Exchange pure pure) of
  Exchange sa bt -> k (runIdentityT . sa) (runIdentityT . bt)

fromM :: Applicative f => AnIsoM f s t a b -> IsoM f b a t s
fromM l = withIsoM l $ \ sa bt -> isoM bt sa

lensM :: Functor f => (s -> f a) -> (s -> b -> f t) -> LensM f s t a b
lensM f g tr s = joinR . fmap (g s) . joinL . fmap tr $ f s

indexedLensM :: (Applicative m, Monad m, FunctorM m f) => (i -> s -> m a) -> (i -> s -> b -> m t) -> LensLike (IndexingM i m f) s t a b
indexedLensM f g tr s
    = IndexingM $ get >>= \i -> fmap joinR . runIndexingM . fmap (g i s) . joinL . fmap tr $ f i s
{-
  = IndexingM $ get >>= \i -> fmap (\fs -> joinL $ f i s >> return (joinR $ fmap (g i s) fs)) (runIndexingM (tr s))
-}


isoM :: (s -> f a) -> (b -> f t) -> IsoM f s t a b
isoM = dimapM

(%~!) :: ProfunctorM f p => SettingM f p s t a b -> p a (f b) -> s -> f t
k %~! b = runIdentityT . k (rmap IdentityT b)

(.~!) :: Functor f => ASetterM f s t a b -> f b -> s -> f t
k .~! b = k %~! const b

(^.!) :: Applicative f => s -> GettingM f a s a -> f a
x ^.! k = getEffect . k (Effect . pure) $ x

(%=!) :: (ProfunctorM m p, MonadState s m) => SettingM m p s s a b -> p a (m b) -> m ()
k %=! b = get >>= k %~! b >>= put

(.=!) :: (Functor m, MonadState s m) => ASetterM m s s a b -> m b -> m ()
k .=! b = k %=! const b

useM :: (Applicative m, MonadState s m) => GettingM m a s a -> m a
useM k = get >>= (^.! k)

infix 4 %=!, .=!
infixr 4 %~!, .~!
infixl 8 ^.!

-----------

swp m n = do
    a <- n
    m
    return a

-- tracing write
tracing :: (Monoid e, MonadWriter e m) => (s -> e) -> IsoM m t s t s
tracing show = isoM return $ \x -> tell (show x) >> return x

tracingI :: (Monoid e, Applicative m, FunctorM m f, MonadWriter e m) => (Int -> s -> e) -> (Int -> t -> e) -> LensLike (IndexingM Int m f) t s t s
tracingI g f = indexedLensM (\i s -> tell (f i s) >> return s) (\i s b -> tell (g i b) >> return b)

--testM :: 
test = putStrLn $ snd $ runWriter $ flip runStateT (True, ["hel","lo"] :: [String], Left 3 :: Either (Sum Int) Any) $ do
    next
    b <- useM $ k "st" . _2 . k "_2" . to show . k "to show"
    next
    k "st" . _3 . k "_3" . _Left . k "_Left" %=! pure . (1 `mappend`)
    next
    k "st" . _3 . k "_3" . _Right . k "_Right" %=! pure . (Any True `mappend`)
    next
    k "st" . _1 . k "_1" . iso not not . k "not" %=! pure . not
    next
    indexingM (k "st" . _2 . k "_2" . each . k' "each#1" . each . k' "each#2") %=! pure . toUpper
    next
    _1 . k "x" .=! pure False
    next
    b <- useM $ indexingM $ k' "st" . _2 . k "_2" . folded . k' "folded#1" . folded . k' "folded#2" . iso ord chr . k' "ord" . iso Sum getSum
    tell $ show b
    return ()
  where
    next = tell "\n\n"

    k e =        (tracing $ ("\n " ++) . (++ (" -") ++ e ++ "->") . show)
         . fromM (tracing $ (++ "\n") . (("-" ++ e ++ "-> ") ++) . show)

    k' e =        tracingI (\i -> ("\n " ++) . (++ (" -" ++ e ++ "[" ++ show i ++ "]->")) . show)
                           (\i -> (++ "\n") . (("-" ++ e ++ "[" ++ show i ++ "]-> ") ++) . show)
-}
