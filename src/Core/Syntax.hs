{-# LANGUAGE LambdaCase,
             RankNTypes,
             MultiParamTypeClasses,
             FlexibleContexts,
             TemplateHaskell,
             RecursiveDo #-}

module Core.Syntax (
  -- * The Syntax
  Decl(..), mkDecl,
  Term(..), mkVar, mkApp, mkLam, mkFun, mkUndefined, mkUniverse, mkUniverseTop,
  mkULvlApp, mkULvlLam, mkULvlFun, mkULift,
  ULvl(..), mkULvl, mkUSuc, mkUMax, mkUVar, leqU, addU, maxU,
  VarTy(..), Name,
  -- * Parsing and Printing
  tokenizeCore, decl, term,
  Pprable(..), ppr, ss, slvl, intercalateS
) where

import Control.Applicative
import Data.Functor.Classes
import Data.Deriving (deriveShow1) 
-- import Text.PrettyPrint
import Data.Char
import Data.List
import Text.Read

import Data.Natural

import Utils
import Parser





-- ==============
--   THE SYNTAX
-- ==============

-- Meta: ULvls are i
--       Naturals are n
--       Variables are x,y
--       Terms are X,Y
--       Type-like terms are A,B
--       IndType names are T
--       TypeCons are c or p

data Decl v = Decl Name (Term v) (Term v)             -- ^ def x : A = X    [Decl "x" A X]
            | IndDecl [(Name,Term v)] [(Name,Term v)] -- ^ def T : A by ..  [IndDecl ..]

data Term v = Var v                                   -- ^ x                [Var x]
         -- | Induction IndName                       -- ^ induction T      [Induction "T"]
            | App (Term v) (Term v)                   -- ^ X Y              [App X Y]
            | Lam Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) >-> X    [Lam "x" A (x. X)]
            | Fun Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) -> B     [Fun "x" A (x. B)]
            | Undefined (Term v)                      -- ^ undefined : A    [Undefined A]
            | Universe (ULvl v)                       -- ^ 𝕋{i}             [Universe i]
            | UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]
            | ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]
            | ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]
            | ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]
            | ULift Natural (Term v)                  -- ^ +n X             [ULift n X]

data ULvl v = ULvl Natural                            -- ^ n                [ULvl n]
            | USuc Natural (ULvl v)                   -- ^ n + i            [USuc n i]
            | UMax (ULvl v) (ULvl v)                  -- ^ max i j          [UMax i j]
            | UVar v                                  -- ^ i                [UVar i]


type Name = String

data VarTy = V | I deriving (Eq, Ord, Read, Show)





-- ====================
--   HELPER FUNCTIONS
-- ====================

mkDecl = Decl

mkIndDecl :: [(Name, Term Name)] -> [(Name, Term Name)] -> Decl Name
mkIndDecl ts cs = IndDecl ts cs

mkVar = Var
mkApp = App

mkLam :: Name -> Term Name -> Term Name -> Term Name
mkLam x tyA body = Lam x tyA (abstract [(x,V)] body)

mkFun :: Name -> Term Name -> Term Name -> Term Name
mkFun x tyA tyB = Fun x tyA (abstract [(x,V)] tyB)

mkUndefined = Undefined
mkUniverse = Universe
mkUniverseTop = UniverseTop
mkULvlApp = ULvlApp

mkULvlLam :: Name -> Term Name -> Term Name
mkULvlLam i body = ULvlLam i (abstract [(i,I)] body)

mkULvlFun :: Name -> Term Name -> Term Name
mkULvlFun i tyA = ULvlFun i (abstract [(i,I)] tyA)

mkULift = ULift

mkULvl = ULvl
mkUSuc = USuc
mkUMax = UMax
mkUVar = UVar

-- | @i `leqU` j@ @Just True@ if @i@ must be less than or euqual to @j@, 
--   @Just False@ if @i@ cannot be less than or equal to @j@, and @Nothing@ if
--   it cannot yet be determined (e.g. (UVar _) `leqU` (UVar _))
leqU :: ULvl v -> ULvl v -> Maybe Bool
leqU (ULvl n)   (ULvl m)   = Just (n <= m)
leqU (ULvl n)   (USuc m _) = if n <= m then Just True
                                       else Nothing
leqU (USuc n _) (ULvl m)   = if n > m then Just False
                                      else Nothing
leqU _ _                   = Nothing

-- | @n `addU' i@ adds @n@ to @i@ in the smallest way possible. For example,
--   @n `addU' (USuc m j) = USuc (n+m) j@. 
--   If @i@ is in normal form, the result will be as well.
addU :: Natural -> ULvl v -> ULvl v
addU n (ULvl m)   = ULvl (n+m)
addU n (USuc m j) = USuc (n+m) j
addU 0 j          = j
addU n j          = USuc n j

-- | @i `maxU' j@ takes the max of @i@ and @j@ in the smallest way possible
--   If @i@ and $j$ are in normal form, the result will be as well.
maxU :: ULvl v -> ULvl v -> ULvl v
maxU (ULvl n)   (ULvl m)   = ULvl (max n m)
maxU (ULvl n)   (USuc m i) = if n <= m then USuc m i
                                       else USuc m (UMax (ULvl (n-m)) i)
maxU (USuc n i) (ULvl m)   = if n >= m then USuc n i
                                       else USuc n (UMax i (ULvl (m-n)))
maxU (USuc n i) (USuc m j) = if n <= m then USuc n (UMax i (ULvl (m-n)))
                                       else USuc m (UMax (ULvl (n-m)) i)
maxU (ULvl 0)   j          = j
maxU i          (ULvl 0)   = i
maxU i          j          = UMax i j


-- =============
--   INSTANCES
-- =============

-- Encoding variable binding:
instance Functor ULvl where
    fmap f (ULvl n)             = ULvl n
    fmap f (USuc n i)           = USuc n (f <$> i)
    fmap f (UMax i j)           = UMax (f <$> i) (f <$> j)
    fmap f (UVar v)             = UVar (f v)
instance Functor Term where
    fmap f (Var v)              = Var (f v)
    fmap f (App x y)            = App (f <$> x) (f <$> y)
    fmap f (Lam n tyA scope)    = Lam n (f <$> tyA) (f <$> scope)
    fmap f (Fun n tyA scope)    = Fun n (f <$> tyA) (f <$> scope)
    fmap f (Undefined tyA)      = Undefined (f <$> tyA)
    fmap f (Universe i)         = Universe (f <$> i)
    fmap f (UniverseTop)        = UniverseTop
    fmap f (ULvlApp x i)        = ULvlApp (f <$> x) (f <$> i)
    fmap f (ULvlLam n scope)    = ULvlLam n (f <$> scope)
    fmap f (ULvlFun n scope)    = ULvlFun n (f <$> scope)
    fmap f (ULift n x)          = ULift n (f <$> x)

-- Encoding where our variables live:
instance Boxed ULvl where
    box = UVar
instance Boxed Term where
    box = Var

-- Encoding substitution:
instance Subst ULvl ULvl where
    (ULvl n) *>>= f             = ULvl n
    (USuc n i) *>>= f           = USuc n (i *>>= f)
    (UMax i j) *>>= f           = UMax (i *>>= f) (j *>>= f)
    (UVar v) *>>= f             = f v
instance Subst Term Term where
    (Var v) *>>= f              = f v
    (App x y) *>>= f            = App (x *>>= f) (y *>>= f)
    (Lam n tyA scope) *>>= f    = Lam n (tyA *>>= f) (scope *>>= f)
    (Fun n tyA scope) *>>= f    = Fun n (tyA *>>= f) (scope *>>= f)
    (Undefined tyA) *>>= f      = Undefined (tyA *>>= f)
    (Universe i) *>>= f         = Universe i
    (UniverseTop) *>>= f        = UniverseTop
    (ULvlApp x i) *>>= f        = ULvlApp (x *>>= f) i
    (ULvlLam n scope) *>>= f    = ULvlLam n (scope *>>= f)
    (ULvlFun n scope) *>>= f    = ULvlFun n (scope *>>= f)
    (ULift n x) *>>= f          = ULift n (x *>>= f)
instance Subst Term ULvl where
    (Var v) *>>= f              = Var v
    (App x y) *>>= f            = App (x *>>= f) (y *>>= f)
    (Lam n tyA scope) *>>= f    = Lam n (tyA *>>= f) (scope *>>= f)
    (Fun n tyA scope) *>>= f    = Fun n (tyA *>>= f) (scope *>>= f)
    (Undefined tyA) *>>= f      = Undefined (tyA *>>= f)
    (Universe i) *>>= f         = Universe (i *>>= f)
    (UniverseTop) *>>= f        = UniverseTop
    (ULvlApp x i) *>>= f        = ULvlApp (x *>>= f) (i *>>= f)
    (ULvlLam n scope) *>>= f    = ULvlLam n (scope *>>= f)
    (ULvlFun n scope) *>>= f    = ULvlFun n (scope *>>= f)
    (ULift n x) *>>= f          = ULift n (x *>>= f)

-- Encoding alpha-equivalence:
instance Eq1 ULvl where
    liftEq r (ULvl n) (ULvl m)                     = n == m
    liftEq r (USuc n i) (USuc m j)                 = n == m && liftEq r i j
    liftEq r (UMax i j) (UMax k l)                 = (    liftEq r i k && liftEq r j l ) -- Notice! 'max' is commutative
                                                     || ( liftEq r i l && liftEq r j k ) --          on the α-equiv level!!
    liftEq r (UVar v) (UVar w)                     = r v w
    liftEq _ _ _                                   = False
instance Eq1 Term where
    liftEq r (Var v) (Var w)                       = r v w
    liftEq r (App x y) (App z w)                   = liftEq r x z && liftEq r y w
    liftEq r (Lam _ tyA scope) (Lam _ tyB scope')  = liftEq r tyA tyB && liftEq r scope scope'
    liftEq r (Fun _ tyA scope) (Fun _ tyB scope')  = liftEq r tyA tyB && liftEq r scope scope'
    liftEq r (Undefined tyA) (Undefined tyB)       = liftEq r tyA tyB
    liftEq r (Universe i) (Universe j)             = liftEq r i j
    liftEq r (UniverseTop) (UniverseTop)           = True
    liftEq r (ULvlApp x i) (ULvlApp y j)           = liftEq r x y && liftEq r i j
    liftEq r (ULvlLam _ scope) (ULvlLam _ scope')  = liftEq r scope scope'
    liftEq r (ULvlFun _ scope) (ULvlFun _ scope')  = liftEq r scope scope'
    liftEq r (ULift n x) (ULift n' x')             = n == n' && liftEq r x x'
    liftEq _ _ _                                   = False
instance Eq1 Decl where
    liftEq r (Decl _ tyA rhs) (Decl _ tyB rhs')    = liftEq r tyA tyB && liftEq r rhs rhs'
    liftEq r (IndDecl ts cs) (IndDecl ts' cs')     = and (zipWith (\(_,tyA) (_,tyB) -> liftEq r tyA tyB) ts ts') &&
                                                     and (zipWith (\(_,tyA) (_,tyB) -> liftEq r tyA tyB) cs cs')

-- Useful for reasoning about free variables:
instance Foldable ULvl where
    foldMap f (ULvl n)             = mempty
    foldMap f (USuc n i)           = foldMap f i
    foldMap f (UMax i j)           = foldMap f i `mappend` foldMap f j
    foldMap f (UVar v)             = f v
instance Foldable Term where
    foldMap f (Var v)              = f v
    foldMap f (App x y)            = foldMap f x `mappend` foldMap f y
    foldMap f (Lam _ tyA scope)    = foldMap f tyA `mappend` foldMap f scope
    foldMap f (Fun _ tyA scope)    = foldMap f tyA `mappend` foldMap f scope
    foldMap f (Undefined tyA)      = foldMap f tyA
    foldMap f (Universe i)         = foldMap f i
    foldMap f (UniverseTop)        = mempty
    foldMap f (ULvlApp x i)        = foldMap f x `mappend` foldMap f i
    foldMap f (ULvlLam _ scope)    = foldMap f scope
    foldMap f (ULvlFun _ scope)    = foldMap f scope
    foldMap f (ULift _ x)          = foldMap f x
instance Traversable ULvl where
    traverse f (ULvl n)             = pure $ ULvl n
    traverse f (USuc n i)           = USuc n <$> traverse f i
    traverse f (UMax i j)           = UMax <$> traverse f i <*> traverse f j
    traverse f (UVar v)             = UVar <$> f v
instance Traversable Term where
    traverse f (Var v)              = Var <$> f v
    traverse f (App x y)            = App <$> traverse f x <*> traverse f y
    traverse f (Lam n tyA scope)    = Lam n <$> traverse f tyA <*> traverse f scope
    traverse f (Fun n tyA scope)    = Fun n <$> traverse f tyA <*> traverse f scope
    traverse f (Undefined tyA)      = Undefined <$> traverse f tyA
    traverse f (Universe i)         = Universe <$> traverse f i
    traverse f (UniverseTop)        = pure UniverseTop
    traverse f (ULvlApp x y)        = ULvlApp <$> traverse f x <*> traverse f y
    traverse f (ULvlLam n scope)    = ULvlLam n <$> traverse f scope
    traverse f (ULvlFun n scope)    = ULvlFun n <$> traverse f scope
    traverse f (ULift n x)          = ULift n <$> traverse f x

deriveShow1 ''ULvl
deriveShow1 ''Term
deriveShow1 ''Decl

-- Make standard Eq and Show instances from Eq1 and Show1:
instance   Eq a =>   Eq     (ULvl a) where      (==) = eq1
instance   Eq a =>   Eq     (Term a) where      (==) = eq1
instance   Eq a =>   Eq     (Decl a) where      (==) = eq1
instance Show a => Show     (ULvl a) where showsPrec = showsPrec1
instance Show a => Show     (Term a) where showsPrec = showsPrec1
instance Show a => Show     (Decl a) where showsPrec = showsPrec1




-- ========================
--   PARSING AND PRINTING
-- ========================

coreTkF :: TkFunction
coreTkF (':':'=':_) = Split 2
coreTkF ('𝕋':'{':_) = SplitIsolate 2
coreTkF ('@':'+':_) = Split 2
coreTkF (x:_) | x `elem` ":@𝕋\"" = Split 1
coreTkF (x:_) | x `elem` "{}()," = SplitIsolate 1
coreTkF _ = Continue

tokenizeCore :: String -> [Token]
tokenizeCore = tokenize coreTkF

varparseWild :: String -> Bool
varparseWild "_" = True
varparseWild xs = varparse xs

varparse :: String -> Bool
varparse (x:xs) = (x:xs) `notElem` keywords
                  && isAlpha x && x /= '𝕋'
                  && all (\y -> isAlphaNum y || y == '-' || y == '_')
                         (dropWhileEnd (== '\'') xs)
varparse _      = False

keywords :: [String]
keywords = ["forall", "undefined", "def"]

uvarparse :: String -> Bool
uvarparse (x:xs) = x `elem` ['i','j','k'] && all isDigit xs
uvarparse _      = False

declOrTerm :: EarleyPair Decl Term
declOrTerm = mdo
  let v    = varBy varparse
      vORw = varBy varparseWild
      nat = terminalBy readMaybe
      
  let vE    =     v <?> Thing "a variable"
      vORwE = (vORw <?> Thing "a variable") <?> Lit "_"

  i0 <- rule $  mkULvl <$> nat
            <|> mkUVar <$> varBy uvarparse
            <|> l "(" *>w*> i1 <*w<* l ")"

  i1 <- rule $  mkUSuc <$> nat <*w<* l "+" <*w<*> ulvl1
            <|> l "max" *>w*> (mkUMax <$> ulvl0) <*w<*> ulvl0
            <|> i0
  
  let [ulvl0,ulvl1] = (<?> Thing "a universe level") <$> [i0,i1]

  x0 <- rule $  mkVar <$> vE
            <|> l "𝕋{" *>w*> (mkUniverse <$> ulvl1) <*w<* lE "}"
            <|> l "𝕋{" *>w*> l "ω" *>w*> l "}" *> pure mkUniverseTop
            <|> l "(" *>w*> tm2 <*w<* lE ")"
  
  x1 <- rule $      mkApp <$> (x1) <*w         <*> (x0)
            <|> mkULvlApp <$> (x1) <*w<* l "@" <*> (i0)
            <|> l "@+" *> (mkULift <$> (nat <?> Thing "a number")) <*w<*> (tm0)
            <|> x0
  
  x2 <- rule $  xlam
            <|> l "forall" *>w*> xfalls
            <|> l "(" *>w*> (mkFun <$> vORwE) <*w<* lE ":" <*w<*> (ty2) <*w<* lE ")" <*w<* lE "->" <*w<*> (ty2)
            <|>             (mkFun "__")                      <$> (ty1)              <*w<* lE "->" <*w<*> (ty2)
            <|> l "∀" *>w*> (mkULvlFun <$> vE) <*w<* lE "," <*w<*> (ty2)
            <|> l "undefined" *>w*> lE ":" *>w*> (mkUndefined <$> ty2)
            <|> x1
  
  xlam <- rule $  l "(" *>w*>     (mkLam <$> vORwE) <*w<* lE ":" <*w<*> (ty2) <*w<* lE ")" <*w<*> (xlam)
              <|> l "(" *>w*>     (mkLam <$> vORwE) <*w<* lE ":" <*w<*> (ty2) <*w<* lE ")" <*w<* lE ">->" <*w<*> (tm2)
              <|> l "(" *>w*> (mkULvlLam <$> vORwE)                           <*w<* lE ")" <*w<*> (xlam)
              <|> l "(" *>w*> (mkULvlLam <$> vORwE)                           <*w<* lE ")" <*w<* lE ">->" <*w<*> (tm2)
  
  xfalls <- rule $  lE "(" *>w*> (mkFun <$> vORwE) <*w<* lE ":" <*w<*> (ty2) <*w<* lE ")" <*w<*> (xfalls)
                <|> lE "," *>w*> (ty2)
                
  let [tm0,tm1,tm2] = (<?> Thing "a term") <$> [x0,x1,x2]
  let [ty0,ty1,ty2] = (<?> Thing "a type") <$> [x0,x1,x2]
  
  ipair <- rule $ ((,) <$> v) <*w<* lE ":" <*w<*> ty2

  ipairs <- rule $  ((:) <$> ipair) <*w<* l "," <*w<*> cnstrs
                <|> ((:[]) <$> ipair)
  
  let sorts  = ipairs <?> Thing "a type or type family declaration"
  let cnstrs = ipairs <?> Thing "a constructor declaration"
  
  cds <- rule $ cnstrs <|> ((l "(" *>w*> pure [] <* l ")") <?> Lit "()")
  
  d4 <- rule $  lE "def" *>w*> (mkDecl <$> vE) <*w<* lE ":" <*w<*> ty2 <*w<* lE ":=" <*w<*> tm2
            <|> lE "def" *>w*> (mkIndDecl <$> sorts) <*w<* lE "by" <*w<*> cds
  
  return (d4, x2)

decl :: EarleyGrammar Decl
decl = fst <$> declOrTerm

term :: EarleyGrammar Term
term = snd <$> declOrTerm



-- Printing:

class Pprable t where
    pprS :: t String -> (Int, ShowS)

ppr :: Pprable t => t String -> String
ppr x = snd (pprS x) []

ss :: String -> ShowS
ss = showString

slvl :: Int -> (Int, ShowS) -> ShowS
slvl i (lvl, str) = if lvl > i then ss "(" . str . ss ")" else str

intercalateS :: ShowS -> [ShowS] -> ShowS
intercalateS _ [] = id
intercalateS sep (x:xs) = x . go xs
  where go []     = id
        go (x:xs) = sep . x . go xs

instance Pprable ULvl where
    pprS (UVar v)    = (0, ss v)
    pprS (ULvl n)    = (0, ss (show n))
    pprS (USuc n i)  = (1, ss (show n) . ss " + " . slvl 1 (pprS i))
    pprS (UMax i j)  = (1, ss "max " . slvl 0 (pprS i) . ss " " . slvl 0 (pprS j))

pprS_Lams :: Term String -> (Int, ShowS)
pprS_Lams (Lam n tyA scope) = (2, ss "(" . ss n . ss " : " . slvl 2 (pprS tyA) . ss ") " . slvl 2 (pprS_Lams $ instantiate [(V,n)] scope))
pprS_Lams (ULvlLam n scope) = (2, ss "(" . ss n                                . ss ") " . slvl 2 (pprS_Lams $ instantiate [(I,n)] scope))
pprS_Lams rhs               = (2, ss ">-> " . slvl 2 (pprS rhs))

instance Pprable Term where
    pprS (Var v)           = (0, ss v)
    pprS (App x y)         = (1, slvl 1 (pprS x) . ss " " . slvl 0 (pprS y))
    pprS (Lam n tyA scope) = pprS_Lams (Lam n tyA scope)
    pprS (Fun n tyA scope) = if n == "__"
                             then (2,                            slvl 1 (pprS tyA) . ss  " -> " . slvl 2 (pprS $ instantiate [(V,n)] scope))
                             else (2, ss "(" . ss n . ss " : " . slvl 2 (pprS tyA) . ss ") -> " . slvl 2 (pprS $ instantiate [(V,n)] scope))
    pprS (Undefined tyA)   = (2, ss "undefined : " . slvl 2 (pprS tyA))
    pprS (Universe i)      = (0, ss "𝕋{" . slvl 1 (pprS i) . ss "}")
    pprS (UniverseTop)     = (0, ss "𝕋{ω}")
    pprS (ULvlApp x i)     = (1, slvl 1 (pprS x) . ss " @" . slvl 0 (pprS i))
    pprS (ULvlLam n scope) = pprS_Lams (ULvlLam n scope)
    pprS (ULvlFun n scope) = (2, ss "∀ " . ss n . ss ", " . slvl 2 (pprS $ instantiate [(I,n)] scope))

instance Pprable Decl where
    pprS (Decl n ty defn)
      = (4, ss "def " . ss n . ss " : " . slvl 2 (pprS ty) . ss "\n" . ss (replicate (5 + length n) ' ') . ss ":= " . slvl 2 (pprS defn))
    pprS (IndDecl ts cs)
      = (4, ss "def " . intercalateS (ss ",\n    ") (fmap (\(n,ty) -> ss n . ss " : " . slvl 2 (pprS ty)) ts)
                      . (if null cs then ss " by ()" else ss " by\n    ")
                      . intercalateS (ss ",\n    ") (fmap (\(n,ty) -> ss n . ss " : " . slvl 2 (pprS ty)) cs))
