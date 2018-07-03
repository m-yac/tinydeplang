{-# LANGUAGE MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances,
             LambdaCase #-}

module Utils (
    -- * Error Handling
    ExceptM(..), StrExcept, addWarning,
    -- * Custom Unbound
    Boxed(..), Subst(..),
    Bnd.Var(..), Scope(..),
    abstractf, abstract, instantiatef, instantiate,
    subst, substVar, closed, isClosed, fv,
    -- * Other Useful Functions
    notNull
) where

import Data.Maybe
import Control.Monad.Except
import Data.Functor.Classes
import Data.Foldable

import qualified Bound as Bnd



-- FIX LATER
type StrExcept = Except String

data ExceptM w e a = Error e
                   | NoError [w] a

instance Eq w => Eq2 (ExceptM w) where
    liftEq2 e1 _  (Error e)      (Error e')       = e1 e e'
    liftEq2 _  e2 (NoError ws a) (NoError ws' a') = ws == ws' && e2 a a'
    liftEq2 _ _ _ _                               = False

instance (Eq w, Eq e      ) => Eq1 (ExceptM w e)   where liftEq = liftEq2 (==)
instance (Eq w, Eq e, Eq a) => Eq  (ExceptM w e a) where (==) = eq1

instance Show w => Show2 (ExceptM w) where
    liftShowsPrec2 sp1 _ _ _ d (Error e) = showsUnaryWith sp1 "Error" d e
    liftShowsPrec2 _ _ sp2 _ d (NoError ws a) = showsBinaryWith showsPrec sp2 "NoError" d ws a

instance (Show w, Show e        ) => Show1 (ExceptM w e)   where liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Show w, Show e, Show a) => Show  (ExceptM w e a) where showsPrec = showsPrec2

instance Functor (ExceptM w e) where
    fmap f (Error e)      = Error e
    fmap f (NoError ws a) = NoError ws (f a)

instance Applicative (ExceptM w e) where
    pure a = NoError [] a
    Error e      <*> _             = Error e
    NoError ws f <*> Error e       = Error e
    NoError ws f <*> NoError ws' x = NoError (ws ++ ws') (f x)

instance Monad (ExceptM w e) where
    Error e      >>= _ = Error e
    NoError ws a >>= f = NoError ws id <*> f a

instance MonadError e (ExceptM w e) where
    throwError = Error
    Error e      `catchError` f = f e
    NoError ws a `catchError` _ = NoError ws a

addWarning :: w -> ExceptM w e ()
addWarning w = NoError [w] ()



class Functor f => Boxed f where
    box :: a -> f a

class Boxed f => Subst m f where
    (*>>=) :: m a -> (a -> f a) -> m a



newtype Scope b f a = Scope { unscope :: f (Bnd.Var b a) }

instance (Functor f) => Functor (Scope b f) where
    fmap f = Scope . fmap (fmap f) . unscope

instance (Subst f g) => Subst (Scope b f) g where
    (Scope m) *>>= f = Scope $ m *>>= (\case Bnd.F a -> Bnd.F <$> (f a)
                                             Bnd.B b -> box (Bnd.B b)   )

instance (Eq b, Eq1 f) => Eq1 (Scope b f) where
  liftEq f m n = liftEq (liftEq f) (unscope m) (unscope n)

-- | @'toList'@ is provides a list (with duplicates) of the free variables
instance Foldable f => Foldable (Scope b f) where
  foldMap f (Scope a) = foldMap (foldMap f) a
  {-# INLINE foldMap #-}

instance Traversable f => Traversable (Scope b f) where
  traverse f (Scope a) = Scope <$> traverse (traverse f) a
  {-# INLINE traverse #-}

instance (Show b, Show1 f) => Show1 (Scope b f) where
  liftShowsPrec f g d m = showsUnaryWith (liftShowsPrec (liftShowsPrec f g) (liftShowList f g)) "Scope" d (unscope m)

-- Make standard Eq and Show instances from Eq1 and Show1:
instance (  Eq b,   Eq1 f,   Eq a) =>   Eq (Scope b f a) where      (==) = eq1
instance (Show b, Show1 f, Show a) => Show (Scope b f a) where showsPrec = showsPrec1

-- | Capture some free variables in an expression to yield
-- a 'Scope' with bound variables in @b@
abstractf :: (Functor f) => (a -> Maybe b) -> f a -> Scope b f a
abstractf f e = Scope (k <$> e) where
  k y = case f y of
    Just z  -> Bnd.B z
    Nothing -> Bnd.F y
{-# INLINE abstractf #-}

-- | Abstract over a list of variables
abstract :: (Functor f, Eq a) => [(a,b)] -> f a -> Scope b f a
abstract xs = abstractf (\b -> listToMaybe $ mapMaybe (\(a,x) -> if a == b then Just x else Nothing) xs)
{-# INLINE abstract #-}

-- | Enter a scope, instantiating all bound variables
instantiatef :: (Functor f) => (b -> a) -> Scope b f a -> f a
instantiatef f e = k <$> (unscope e) where
  k y = case y of
    Bnd.B b -> f b
    Bnd.F a -> a
{-# INLINE instantiatef #-}

-- | Enter a 'Scope' that binds some number of variables, instantiating it
instantiate :: (Functor f, Eq b) => [(b,a)] -> Scope b f a -> f a
instantiate xs = instantiatef (\b -> fromJust $ lookup b xs)
{-# INLINE instantiate #-}

-- | @'subst' a p w@ replaces the free variable @a@ with @p@ in @w@.
subst :: (Subst f g, Eq a) => a -> g a -> f a -> f a
subst a p w = w *>>= \b -> if a == b then p else box b
{-# INLINE subst #-}

-- | @'substVar' a b w@ replaces a free variable @a@ with another free variable @b@ in @w@.
substVar :: (Functor f, Eq a) => a -> a -> f a -> f a
substVar a p = fmap (\b -> if a == b then p else b)
{-# INLINE substVar #-}

-- | If a term has no free variables, you can freely change the type of
-- free variables it is parameterized on.
closed :: Traversable f => f a -> Maybe (f b)
closed = traverse (const Nothing)
{-# INLINE closed #-}

-- | A closed term has no free variables.
isClosed :: Foldable f => f a -> Bool
isClosed = all (const False)
{-# INLINE isClosed #-}

-- | Gives a list of all free variables.
fv :: Foldable f => f a -> [a]
fv = toList
{-# INLINE fv #-}





notNull :: [a] -> Bool
notNull = not . null
