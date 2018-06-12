{-# LANGUAGE TupleSections #-}

module Core.Check where

import Debug.Trace
import Control.Monad
import Data.Either

import Utils
import Core.Syntax
import Core.Context
import Core.Eval




-- | Given a 'WithCtx' action and a nonempty list of possibilities, applies
--   the action to each element of the list and segregating those which error
--   from those which do not. If only one remains error-free, 'resolveAmbig'
--   returns that one. Otherwise, errors are thrown appropriately.
resolveAmbig :: Show (t Name) => (t Name -> WithCtx Name b) -> [t Name] -> WithCtx Name b
resolveAmbig f ts = do
    ctx <- getCtx
    case partitionEithers $ fmap (runWithCtx ctx . f) ts of
        ([],[]) -> error "empty list passed to \'resolveAmbig\'"
        -- the 'no survivors' but 'single error' case:
        ([err],[]) -> throwError err
        -- the 'no survivors' but 'multiple errors' (i.e. worst) case:
        (errs,[]) -> throwError $ "irrecoverable ambiguity - none of the following readings are possible:"
                                   ++ (errs >>= ("\n- " ++))
        -- the 'one survivor' (i.e. best) case:
        (_,[x]) -> return x
        -- the 'multiple survivors case'
        (_,xs) -> throwError $ "term is ambiguous - could be read as any of:"
                               ++ (ts >>= (('\n':) . show))

-- | Given a 'Term', returns the term and its type. If an error occurs, it is
--   handled by the 'WithCtx' monad.
check :: Term Name -> WithCtx Name (Term Name, Term Name)

-- Var v                                   -- ^ x                [Var x]

check (Var v) = do
    -- Get the type of v from Γ
    ty <- fst <$> lookupTermVar v
    return (Var v, ty)

-- App (Term v) (Term v)                   -- ^ X Y              [App X Y]

check (App x y) = do
    -- Ensure that X : (z : A) -> B for some z, A, and B
    (x', (z, tyA, scope)) <- mapM ensureIsFun =<< check x
    -- Find the type of Y : C
    (y', tyC) <- check y
    -- Ensure the types match up, i.e. A = C
    equate tyA tyC
    -- We now know (X Y) : B[Y/z]
    return (App x' y', subst z y (instantiate [(V,z)] scope))

-- Lam Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) >-> X    [Lam "x" A (x. X)]

check (Lam x tyA scope) = do
    -- Ensure that A : 𝕋{i} for some i
    (tyA', i) <- mapM ensureIsUniverse =<< check tyA
    -- Add x to Γ, then find the type of X : B
    (body, tyB) <- extendCtx [termVar x tyA] $ do
        check (instantiate [(V,x)] scope)
    -- We now know ((x : A) >-> X) : (x : A) -> B
    return (Lam x tyA' (abstract [(x,V)] body), Fun x tyA' (abstract [(x,V)] tyB))

-- Fun Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) -> B     [Fun "x" A (x. B)]

check (Fun x tyA scope) = do
    -- Ensure that A : 𝕋{i} for some i
    (tyA', i) <- mapM ensureIsUniverse =<< check tyA
    -- Add x to Γ, then ensure that B : 𝕋{j} for some j
    (tyB, j) <- extendCtx [termVar x tyA] $ do
        tyB <- check (instantiate [(V,x)] scope)
        mapM ensureIsUniverse tyB
    -- At the very least, we now know ((x : A) -> B) : 𝕋{max i j}
    return $ (Fun x tyA' (abstract [(x,V)] tyB), Universe (UMax i j))

-- Undefined (Term v)                      -- ^ undefined : A    [Undefined A]

check (Undefined tyA) = do
    -- We know undefined : A
    return (Undefined tyA, tyA)

-- Universe (ULvl v)                       -- ^ 𝕋{i}             [Universe i]

check (Universe i) = do
    -- At the very least, we know 𝕋{i} : 𝕋{1 + i}
    return (Universe i, Universe (1 `addU` i))

-- UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]

check (UniverseTop) = throwError $ "𝕋{ω} has no type!"

-- ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]

check (ULvlApp x i) = do
    -- Ensure that X : ∀ j. B for some z, A, and B
    (x', (j, scope)) <- mapM ensureIsULvlFun =<< check x
    -- We now know (X i) : B[i/j]
    return (ULvlApp x' i, subst j i (instantiate [(I,j)] scope))

-- ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]

check (ULvlLam i scope) = do
    -- Add i to Γ, then find the type of A : B
    (body, tyB) <- extendCtx [ulvlVar i] $ do
        check (instantiate [(I,i)] scope)
    -- We now know (i >-> A) : ∀ i. B
    return (ULvlLam i (abstract [(i,I)] body), ULvlFun i (abstract [(i,I)] tyB))

-- ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]

check (ULvlFun i scope) = do
    -- Add i to Γ, then ensure that A : 𝕋{ω} or A : 𝕋{j} for some j
    (tyA, _) <- extendCtx [ulvlVar i] $ do
        tyA <- check (instantiate [(I,i)] scope)
        mapM ensureIsUniverseOrTop tyA
    -- Ensure that i is in the free variables of A
    unless (i `elem` (fv tyA))
           (throwError $ "[Warning] [Typecheck] Unused universe level quantification: " ++ i ++ " in " ++ ppr tyA)
    -- In either case, (∀ i. A) : 𝕋{ω}
    return $ (ULvlFun i (abstract [(i,I)] tyA), UniverseTop)


-- | Given a 'Decl', an returns the decl with a list of all things which must
--   be added to the context
checkDecl :: Decl Name -> WithCtx Name (Decl Name, [CtxElement Name])
checkDecl (Decl x tyA def) = do
    -- Find the type of X : B
    (def', tyB) <- check def
    -- Ensure the types match up, i.e. A = B
    equate tyA tyB
    -- Return what should be added to Γ
    return (Decl x tyA def', [termVarDef x tyA def'])
checkDecl decl = return (decl, [])

-- | Given a list of lists of possible readings of 'Decl's, returns the final
--   context Γ and the final list of unambiguous decls
checkFile :: [[Decl Name]] -> WithCtx Name (Ctx Name, [Decl Name])
checkFile (decls:xs) = do
    (decl, ctxElts) <- resolveAmbig checkDecl decls
    extendCtx ctxElts (fmap (++[decl]) <$> checkFile xs)
checkFile [] = do
    ctx <- getCtx
    return (ctx,[])





-- ========================

-- | Errors if the given 'Term' is not a 'Fun'. Otherwise returns its name,
--   type, and scope (see the definition of 'Fun')
ensureIsFun :: Term Name -> WithCtx Name (Name, Term Name, Scope VarTy Term Name)
ensureIsFun x = do
    x' <- eval WHNF x
    case x' of
        Fun z tyA scope -> return (z, tyA, scope)
        _ -> throwError $ "[Error] [Typecheck] " ++ ppr x
                          ++ (if x == x' then ""
                              else "(== " ++ ppr x' ++ ")") ++ " is not a function type"

-- | Errors if the given 'Term' is not a 'Universe'. Otherwise returns its
--   'ULvl' (see the definition of 'Universe')
ensureIsUniverse :: Term Name -> WithCtx Name (ULvl Name)
ensureIsUniverse x = do
    x' <- eval WHNF x
    case x' of
        Universe i -> return i
        _ -> throwError $ "[Error] [Typecheck] " ++ ppr x
                           ++ (if x == x' then ""
                              else "(== " ++ ppr x' ++ ")") ++ " is not a finite type universe"

-- | Errors if the given 'Term' is not a 'Universe' and not a 'UniverseTop'.
--   Otherwise returns its 'ULvl' if it has one (see the definitions of
--   'Universe' and 'UniverseTop')
ensureIsUniverseOrTop :: Term Name -> WithCtx Name (Maybe (ULvl Name))
ensureIsUniverseOrTop x = do
    x' <- eval WHNF x
    case x' of
        Universe i  -> return (Just i)
        UniverseTop -> return Nothing
        _ -> throwError $ "[Error] [Typecheck] " ++ ppr x
                           ++ (if x == x' then ""
                              else "(== " ++ ppr x' ++ ")") ++ " is not a type universe"

-- | Errors if the given 'Term' is not a 'ULvlFun'. Otherwise returns its name
--   and scope (see the definition of 'ULvlFun')
ensureIsULvlFun :: Term Name -> WithCtx Name (Name, Scope VarTy Term Name)
ensureIsULvlFun x = do
    x' <- eval WHNF x
    case x' of
        ULvlFun i scope -> return (i, scope)
        _ -> throwError $ "[Error] [Typecheck] " ++ ppr x
                           ++ (if x == x' then ""
                              else "(== " ++ ppr x' ++ ")") ++ " is not a universe-level function type"





-- ========================

-- | Errors if the two terms give are unequal modulo alpha-equivalence
equate :: Term Name -> Term Name -> WithCtx Name ()
equate t1 t2 = do
    t1' <- eval WHNF t1
    t2' <- eval WHNF t2
    -- Get out early if alpha-equiv
    if t1' == t2' then return ()
    -- Otherwise...
    else case (t1', t2') of
        -- Var v                                     -- ^ x                 [Var x]
        (Var v1, Var v2) | v1 == v2 -> return ()
        -- App (Term v) (Term v)                     -- ^ X Y               [App X Y]
        (App x1 y1, App x2 y2) -> do
            equate x1 x2
            equate x2 y2
        -- Lam Names (Term v) (Scope VarTy Term v)   -- ^ (x : A) >-> X     [Lam "x" A (x. X)]
        (Lam x1 ty1 scope1, Lam x2 ty2 scope2) -> do
            equate ty1 ty2
            extendCtx [termVar x1 ty1, termVar x2 ty2] $ do
                equate (instantiate [(V,x1)] scope1) (instantiate [(V,x2)] scope1)
        -- Fun Names (Term v) (Scope VarTy Term v)   -- ^ (x : A) -> B      [Fun "x" A (x. B)]
        (Fun x1 ty1 scope1, Fun x2 ty2 scope2) -> do
            equate ty1 ty2
            extendCtx [termVar x1 ty1, termVar x2 ty2] $ do
                equate (instantiate [(V,x1)] scope1) (instantiate [(V,x2)] scope1)
        -- Undefined (Term v)                        -- ^ undefined : A     [Undefined A]
        (Undefined ty1, Undefined ty2) -> do
            equate ty1 ty2
        -- Universe (ULvl v)                         -- ^ 𝕋{i}              [Universe i]
        (Universe i1, Universe i2) -> do
            i1' <- evalU i1
            i2' <- evalU i2
            if i1' == i2' then return ()
            else throwError $ "equate error for ulvls " ++ ppr i1 ++ " and " ++ ppr i2
        -- UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]
        (UniverseTop, UniverseTop) -> return ()
        -- ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]
        (ULvlApp x1 i1, ULvlApp x2 i2) -> do
            equate x1 x2
            i1' <- evalU i1
            i2' <- evalU i2
            if i1' == i2' then return ()
            else throwError $ "equate error for ulvls " ++ ppr i1 ++ " and " ++ ppr i2
        -- ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]
        (ULvlLam i1 scope1, ULvlLam i2 scope2) -> do
            extendCtx [ulvlVar i1, ulvlVar i2] $ do
                equate (instantiate [(I,i1)] scope1) (instantiate [(I,i2)] scope1)
        -- ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]
        (ULvlFun i1 scope1, ULvlFun i2 scope2) -> do
            extendCtx [ulvlVar i1, ulvlVar i2] $ do
                equate (instantiate [(I,i1)] scope1) (instantiate [(I,i2)] scope1)
        -- Otherwise:
        (x1, x2) -> throwError $ "equate error for terms " ++ ppr x1 ++ " and " ++ ppr x2


