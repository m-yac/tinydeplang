{-# LANGUAGE MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances,
             LambdaCase #-}

module Utils (
    Boxed(..), Subst(..),
    Bnd.Var, Scope(..),
    abstractf, abstract, instantiatef, instantiate,
    subst, substVar, closed, isClosed, fv,
    lines_dbl, notNull, StrExcept
) where

import Data.Maybe
import Control.Monad.Except
import Data.Functor.Classes
import Data.Foldable
import qualified Bound as Bnd



notNull :: [a] -> Bool
notNull = not . null

type StrExcept = Except String



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




lines_dbl :: String -> [String]
lines_dbl = go []
    where go accum [] = [accum]
          go accum (x:xs) = let (ns,rest) = span (== '\n') (x:xs)
                             in case ns of
                                    '\n':'\n':_ -> accum : (go [] rest)
                                    ['\n'] -> go (accum ++ " ") rest
                                    [] -> go (accum ++ [x]) xs



