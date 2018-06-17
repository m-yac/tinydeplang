
module Inductive where

import Utils
import Core.Syntax
import Core.Check

-- data IndType v = IndType Name (Term v) (Scope T TypeCons v)
-- data TypeCon v = Con Name (Term v)
--                | IdCon Name (Term v) (Term v)
-- newtype TypeCons v = TypeCons { unTypeCons :: [TypeCon v] }
-- 
-- data T = T deriving (Eq, Ord, Show)

-- data IndType v = IndType [(IndName, Term v)] (Scope Int TypeCons v)
-- newtype TypeCons v = TypeCons { unTypeCons :: [(ConName, Term v)] }

-- data IndType v = IndType [Sort v] [Con v]
-- data Sort v    = Sort IndName [Funct v] (ULvl v)
-- data Con v     = Con [Funct v] (Funct v)
-- 
-- type Funct v = Scope IndIdx Term v
-- data IndIdx = TyIdx Int | ConIdx Int



type QICntx v = [(Name, QIType v)]

data QIType v = QIUniverse
              | Promoted (QITerm v) -- must have type QIUniverse
              | QIFun Name (QIType v) (QIType v) -- Name implicitly in scope
              | TFun Name (Term v) (QIType v) -- Name implicitly in scope

data QITerm v = TmVar v
              | QIApp (QITerm v) (QITerm v)
              | TApp (QITerm v) (Term v)
              | QILam Name (QIType v) (QIType v) -- Name implicitly in scope
              | TLam Name (Term v) (QIType v) -- Name implicitly in scope

checkCtx :: Name -> [QIDec Name] -> Maybe (QIType Name)
checkCtx n ((QIDec n' ty):xs) | n = n' = Just ty
checkCtx _ (_:xs) = checkCtx xs
checkCtx [] [] = Nothing

componentOfCtx :: QICntx v -> [a] -> Name -> a
componentOfCtx ((x,tyA):_) (a:_) n | x == n = a
componentOfCtx (_:xs) (_:as) n = componentOfCtx xs as n
componentOfCtx [] [] n = error $ "name \'" ++ n ++ "\' not in scope!"
componentOfCtx _ _ _ = error $ "context mismatch!"

-- instance Functor QIType where
--   fmap f (QIUniverse)        = QIUniverse
--   fmap f (Promoted t)        = Promoted (f <$> t)
--   fmap f (QIFun n tyA scope) = QIFun n (f <$> tyA) (f <$> scope)
--   fmap f (TFun n tyA scope)  = TFun n (f <$> tyA) (f <$> scope)
-- 
-- instance Functor QITerm where
--   fmap f (TmVar x)           = TmVar (f x)
--   fmap f (QIApp a b)         = QIApp (f <$> a) (f <$> b)
--   fmap f (TApp a b)          = TApp (f <$> a) (f <$> b)
--   fmap f (QILam n tyA scope) = QILam n (f <$> tyA) (f <$> scope)
--   fmap f (TLam n tyA scope)  = TLam n (f <$> tyA) (f <$> scope)

type QICntx_C v = [Term v]

cntx_C :: QICntx v -> QICntx_C v
cntx_C [] = []
cntx_C ((x,tyA):xs) = (type_C xs (cntx_C xs) tyA):(cntx_C xs)

type QIType_C v = Term v

type_C :: QICntx v -> QICntx_C v -> QIType v -> QIType_C v
type_C xs cs (QIUniverse)        = mkUniverse (UVar "i")
type_C xs cs (Promoted tm)       = term_C xs cs tm
type_C xs cs (QIFun x tyA scope) = mkFun x (type_C xs cs tyA)
                                           (type_C ((TmVar x):xs) ((Var x):cs) scope)
type_C xs cs (TFun x tyA scope)  = mkFun x tyA (type_C xs cs scope)

type QITerm_C v = Term v

term_C :: QICntx v -> QICntx_C v -> QITerm v -> QITerm_C v
term_C xs cs (TmVar n)           = mkVar (componentOfCtx xs cs n)
term_C xs cs (QIApp x y)         = mkApp (term_C xs cs x) (term_C xs cs y)
term_C xs cs (TApp x y)          = mkApp (term_C xs cs x) y
term_C xs cs (QILam x tyA scope) = mkLam x (type_C xs cs tyA)
                                           (term_C ((TmVar x):xs) ((Var x):cs) scope)
term_C xs cs (TLam x tyA scope)  = mkLam x tyA (term_C xs cs scope)



type QICntx_M v = [Term v]

cntx_M :: QICntx v -> QICntx_C v -> QICntx_M v
cntx_M [] cs = []
cntx_M ((x,tyA):xs) (c:cs) = (type_M xs cs (cntx_M xs) tyA c):(cntx_M xs)

type QIType_M v = Term v

type_M :: QICntx v -> QICntx_C v -> QICntx_M v -> QIType v -> QIType_C v -> QIType_M v
type_M xs cs ms (QIUniverse) c        = mkFun "__" c (mkUniverse (UVar "i"))
type_M xs cs ms (Promoted tm) c       = mkApp (term_M xs cs ms tm) c
type_M xs cs ms (QIFun x tyA scope) c = -- ...
type_M xs cs ms (TFun x tyA scope) c  = mkFun x tyA (type_C xs cs scope)

type QITerm_M v = Term v

term_M :: QICntx v -> QICntx_C v -> QICntx_M v -> QITerm v -> QITerm_M v
term_M xs cs (TmVar n)           = mkVar (componentOfCtx xs cs n)
term_M xs cs (QIApp x y)         = mkApp (term_C xs cs x) (term_C xs cs y)
term_M xs cs (TApp x y)          = mkApp (term_C xs cs x) y
term_M xs cs (QILam x tyA scope) = mkLam x (type_C xs cs tyA)
                                           (term_C ((TmVar x):xs) ((Var x):cs) scope)
term_M xs cs (TLam x tyA scope)  = mkLam x tyA (term_C xs cs scope)



toQITerm :: [(Name,Term Name)] -> [(Name,Term Name)] -> [QIDec Name] -> QIIT Name

-- Var v                                   -- ^ x                [Var x]
toQITerm (Var v) ctx = TmVar v

-- App (Term v) (Term v)                   -- ^ X Y              [App X Y]
toQITerm (App x y) = 

-- Lam Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) >-> X    [Lam "x" A (x. X)]


-- Fun Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) -> B     [Fun "x" A (x. B)]
isPositiveWRT (Fun x tyA scope) ns = do
    when (notNull $ ns `intersect` (fv tyA))
         (throwError "strict positivity violated")
    extendCtx [termVar x tyA] $ do
        instantiate [(V,x)] scope

-- Undefined (Term v)                      -- ^ undefined : A    [Undefined A]


-- Universe (ULvl v)                       -- ^ 𝕋{i}             [Universe i]


-- UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]


-- ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]


-- ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]


-- ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]





