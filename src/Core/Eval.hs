
module Core.Eval (
    evalU, Strength(..), eval
) where

import Utils
import Core.Syntax
import Core.Context



-- | Eagerly evaluates a 'ULvl', using the context given
evalU :: ULvl Name -> WithCtx Name (ULvl Name)

-- UO                                        -- ^ 0                 [UO]

evalU (ULvl n) = return $ ULvl n

-- USuc (ULvl v)                             -- ^ S i               [USuc i]

evalU (USuc n i) = do
    i' <- evalU i
    return $ case i' of
      (ULvl m)   -> ULvl (n + m)
      (USuc m i) -> USuc (n + m) i'
      _          -> if n == 0 then i' else USuc n i'

-- UMax (ULvl v) (ULvl v)                    -- ^ max i j           [UMax i j]

evalU (UMax i j) = do
    i' <- evalU i
    j' <- evalU j
    return $ case (i',j') of
      ((ULvl n)  , (ULvl m)  ) -> ULvl (max n m)
      ((ULvl n)  , (USuc m i)) -> if n <= m then USuc m i
                                            else USuc m (UMax (ULvl (n-m)) i)
      ((USuc n i), (ULvl m)  ) -> if n >= m then USuc n i
                                            else USuc n (UMax i (ULvl (m-n)))
      ((USuc n i), (USuc m j)) -> if n <= m then USuc n (UMax i (ULvl (m-n)))
                                            else USuc m (UMax (ULvl (n-m)) i)
      ((ULvl 0)  , j         ) -> j
      (i         , (ULvl 0)  ) -> i
      (i         , j         ) -> UMax i j

-- UVar v                                    -- ^ i                 [UVar i]

evalU (UVar v) = do
    def <- lookupULvlVar v
    case def of
        Just body -> evalU body
        Nothing   -> return $ UVar v




data Strength = NF | WHNF deriving (Eq, Read, Show)

-- | Evaluates a 'Term', to either weak head normal form ('WHNF') or normal
--   form ('NF'), using the context given
eval :: Strength -> Term Name -> WithCtx Name (Term Name)

-- Var v                                   -- ^ x                [Var x]

eval k (Var v) = do
    -- Get the type, and definition if it exists, of the variable "v"
    (ty,def) <- lookupTermVar v
    case def of
        -- If "v" has a definiton in scope, substitute it
        Just body -> eval k body
        -- Otherwise, we can't do anything
        Nothing   -> return $ Var v

-- App (Term v) (Term v)                   -- ^ X Y              [App X Y]

eval k (App x y) = do
    -- Evaluate x
    x' <- eval k x
    -- Only evaluate y if we're going for normal form
    y' <- case k of WHNF -> return y
                    NF   -> eval NF y
    case x' of
        -- If x ≡ (z : A) >-> X, the result is X[y/z]
        Lam z tyA scope -> eval k $ subst z y' (instantiate [(V,z)] scope)
        -- Otherwise, we cant't do anything
        _ -> return $ App x' y'

-- Lam Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) >-> X    [Lam "x" A (x. X)]

eval k (Lam x tyA scope) = do
    case instantiate [(V,x)] scope of
        -- If body ≡ (Y x) and x is not free in Y, do η-reduction:
        App y (Var z) | z == x && x `notElem` (fv y) -> eval k y
        -- Otherwise, we can't do anything
        _ -> return $ Lam x tyA scope

-- Universe (Ulvl v)                       -- ^ 𝕋{i}             [Universe i]

eval k (Universe i) = do
    -- ULvls always eagerly evaluate
    Universe <$> evalU i

-- ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]

eval k (ULvlApp x i) = do
    -- Evaluate x
    x' <- eval k x
    -- Only evaluate i if we're going for normal form
    i' <- case k of WHNF -> return i
                    NF   -> evalU i
    case x' of
        -- If x ≡ j >-> X, the result is X[i/j]
        ULvlLam j scope -> eval k $ subst j i' (instantiate [(I,j)] scope)
        -- Otherwise, we can't do anything
        _ -> return $ ULvlApp x' i'

-- ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]

eval k (ULvlLam i scope) = do
    case instantiate [(I,i)] scope of
        -- If body ≡ (Y i) and i is not free in Y, do η-reduction:
        ULvlApp y (UVar j) | j == i && i `notElem` (fv y) -> eval k y
        -- Otherwise, we can't do anything
        _ -> return $ ULvlLam i scope

-- Otherwise...
-- Fun Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) -> B     [Fun "x" A (x. B)]
-- Undefined (Term v)                      -- ^ undefined : A    [Undefined A]
-- UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]
-- ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]

eval k x = return x


