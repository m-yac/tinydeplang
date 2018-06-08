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
  mkULvlApp, mkULvlLam, mkULvlFun,
  ULvl(..), mkULvl, mkUSuc, mkUMax, mkUVar, leqU, addU,
  VarTy(..), Name,
  -- ** Inductive types
  IndType(..), TypeCon(..), TypeCons(..),
  -- * Parsing and Printing
  decl, term, interaction, Interaction(..),
  parseExcept, parseExceptIO, parseRaw, parseOneUnsafe,
  Pprable(..), ppr, ss, slvl
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
            | TypeDecl (IndType v)                    -- ^ def T : A by ..  [TypeDecl (IndType "T" A ..)]

data Term v = Var v                                   -- ^ x                [Var x]
         -- | IndTypeName IndName                     -- ^ T                [IndTypeName "T"]
         -- | ConName IndName                         -- ^ c                [ConName "c"]
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

data ULvl v = ULvl Natural                            -- ^ n                [ULvl n]
            | USuc Natural (ULvl v)                   -- ^ n + i            [USuc n i]
            | UMax (ULvl v) (ULvl v)                  -- ^ max i j          [UMax i j]
            | UVar v                                  -- ^ i                [UVar i]

-- Inductive Types:

data IndType v = IndType Name (Term v) (Scope T TypeCons v) -- ^ T : A -> 𝕋 by ..  [IndType "T" (A -> 𝕋) ..]
data TypeCon v = Con Name (Term v)                          -- ^ x : A             [Con "x" (T. A)]
               | IdCon Name (Term v) (Term v)               -- ^ p : X = Y         [PathCon "p" X Y]
newtype TypeCons v = TypeCons { unTypeCons :: [TypeCon v] }

data VarTy = V | I deriving (Eq, Ord, Read, Show)
data T     = T     deriving (Eq, Ord, Read, Show)

type Name = String
type IndName = String





-- ====================
--   HELPER FUNCTIONS
-- ====================

mkDecl = Decl

mkTypeDecl :: Name -> Term Name -> [TypeCon Name] -> Decl Name
mkTypeDecl x ty cs = TypeDecl (IndType x ty (abstract [(x,T)] (TypeCons cs)))

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
addU :: Natural -> ULvl v -> ULvl v
addU n (ULvl m)   = ULvl (n+m)
addU n (USuc m j) = USuc (n+m) j
addU n j          = USuc n j





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
instance Functor IndType where
    fmap f (IndType n ty cs)    = IndType n (f <$> ty) (f <$> cs)
instance Functor TypeCons where
    fmap f (TypeCons (c:cs))    = TypeCons ((f <$> c) : unTypeCons (f <$> TypeCons cs))
    fmap f (TypeCons [])        = TypeCons []
instance Functor TypeCon where
    fmap f (Con n ty)           = Con n (f <$> ty)
    fmap f (IdCon n tyA tyB)    = IdCon n (f <$> tyA) (f <$> tyB)

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
instance Subst IndType Term where
    (IndType n ty cs) *>>= f    = IndType n (ty *>>= f) (cs *>>= f)
instance Subst TypeCons Term where
    (TypeCons (c:cs)) *>>= f    = TypeCons ((c *>>= f) : unTypeCons (TypeCons cs *>>= f))
    (TypeCons []) *>>= f        = TypeCons []
instance Subst TypeCon Term where
    (Con n ty) *>>= f           = Con n (ty *>>= f)
    (IdCon n tyA tyB) *>>= f    = IdCon n (tyA *>>= f) (tyB *>>= f)

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
    liftEq _ _ _                                   = False
instance Eq1 Decl where
    liftEq r (Decl _ t x)  (Decl _ t' x')           = liftEq r t t' && liftEq r x x'
    liftEq r (TypeDecl it) (TypeDecl it')           = liftEq r it it'
    liftEq _ _ _                                    = False
instance Eq1 IndType where
    liftEq r (IndType _ t cs) (IndType _ t' cs')    = liftEq r t t' && liftEq r cs cs'
instance Eq1 TypeCons where
    liftEq r (TypeCons (c:cs)) (TypeCons (c':cs'))  = liftEq r c c' && liftEq r (TypeCons cs) (TypeCons cs')
    liftEq r (TypeCons [])     (TypeCons [])        = True
    liftEq _ _ _                                    = False
instance Eq1 TypeCon where
    liftEq r (Con _ t)         (Con _ t')           = liftEq r t t'
    liftEq r (IdCon _ tyA tyB) (IdCon _ tyA' tyB')  = liftEq r tyA tyA' && liftEq r tyB tyB'
    liftEq _ _ _                                    = False

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

deriveShow1 ''ULvl
deriveShow1 ''Term
deriveShow1 ''Decl
deriveShow1 ''IndType
deriveShow1 ''TypeCons
deriveShow1 ''TypeCon

-- Make standard Eq and Show instances from Eq1 and Show1:
instance   Eq a =>   Eq     (ULvl a) where      (==) = eq1
instance   Eq a =>   Eq     (Term a) where      (==) = eq1
instance   Eq a =>   Eq     (Decl a) where      (==) = eq1
instance   Eq a =>   Eq  (IndType a) where      (==) = eq1
instance   Eq a =>   Eq (TypeCons a) where      (==) = eq1
instance   Eq a =>   Eq  (TypeCon a) where      (==) = eq1
instance Show a => Show     (ULvl a) where showsPrec = showsPrec1
instance Show a => Show     (Term a) where showsPrec = showsPrec1
instance Show a => Show     (Decl a) where showsPrec = showsPrec1
instance Show a => Show  (IndType a) where showsPrec = showsPrec1
instance Show a => Show (TypeCons a) where showsPrec = showsPrec1
instance Show a => Show  (TypeCon a) where showsPrec = showsPrec1




-- ========================
--   PARSING AND PRINTING
-- ========================

varparseWild :: String -> Bool
varparseWild (x:xs) = ( x == '_' && null xs ) || varparse (x:xs)
varparseWild _      = False

varparse :: String -> Bool
varparse     (x:xs) = (x:xs) `notElem` keywords
                      && isAlpha x && x /= '𝕋'
                      && all (\y -> isAlphaNum y || y == '-' || y == '_') xs
varparse     _      = False

keywords :: [String]
keywords = ["forall", "undefined", "def"]

uvarparse :: String -> Bool
uvarparse (x:xs) = x `elem` ['i','j','k'] && all isDigit xs
uvarparse _      = False

declOrTerm :: EarleyPair Decl Term
declOrTerm = mdo
  let v    = satisfy varparse
      vORw = satisfy varparseWild
      nat = terminal readMaybe
      
  let vE    =     v <?> Thing "a variable"
      vORwE = (vORw <?> Thing "a variable") <?> Lit "_"

  i0 <- rule $  ULvl <$> nat
            <|> UVar <$> satisfy uvarparse
            <|> l "(" *> i1 <* l ")"

  i1 <- rule $  USuc <$> nat <* l " + " <*> ulvl1
            <|> l "max" *> (UMax <$> ulvl0) <*> ulvl0
            <|> i0
  
  let [ulvl0,ulvl1] = (<?> Thing "a universe level") <$> [i0,i1]

  x0 <- rule $  Var <$> v
            <|> l "𝕋{" *> (Universe <$> ulvl1) <* lE "}"
            <|> l "𝕋{ω}" *> pure UniverseTop
            <|> l "(" *> tm2 <* lE ")"
  
  x1 <- rule $      App <$> (x1)          <*> (x0)
            <|> ULvlApp <$> (x1) <* l "@" <*> (i0)
            <|> x0
  
  x2 <- rule $  xlam
            <|> l "forall" *> xfalls
            <|> l "(" *> (mkFun <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <* lE "->" <*> (ty2)
            <|>          (mkFun "__")                <$> (ty1)           <* lE "->" <*> (ty2)
            <|> l "∀" *> (mkULvlFun <$> vE)    <* lE "," <*> (ty2)
            <|> l "undefined" *> lE ":" *> (Undefined <$> ty2)
            <|> x1
  
  xlam <- rule $  l "(" *>     (mkLam <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <*> (xlam)
              <|> l "(" *>     (mkLam <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <* lE ">->" <*> (tm2)
              <|> l "(" *> (mkULvlLam <$> vORwE)                     <* lE ")" <*> (xlam)
              <|> l "(" *> (mkULvlLam <$> vORwE)                     <* lE ")" <* lE ">->" <*> (tm2)
  
  xfalls <- rule $  lE "(" *> (mkFun <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <*> (xfalls)
                <|> lE "," *> (ty2)
                
  let [tm0,tm1,tm2] = (<?> Thing "a term") <$> [x0,x1,x2]
  let [ty0,ty1,ty2] = (<?> Thing "a type") <$> [x0,x1,x2]
  
  c <- rule $  l "(" *> (Con <$> v) <* lE ":" <*> ty2 <* lE ")"
           <|>          (Con <$> v) <* lE ":" <*> ty2

  cs <- rule $  ((:) <$> c) <* l "," <*> cnstrs
            <|> ((:[]) <$> c)
  
  let cnstrs = cs <?> Thing "a constructor declaration"
  
  cds <- rule $ cnstrs <|> lE "(" *> pure [] <* lE ")"
  
  d4 <- rule $  lE "def" *> l "(" *>       (Decl <$> vE) <* lE ":" <*> ty2 <* lE ")" <* lE "=" <*> tm2
            <|> lE "def" *>                (Decl <$> vE) <* lE ":" <*> ty2 <*           lE "=" <*> tm2
            <|> lE "def" *> l "(" *> (mkTypeDecl <$> vE) <* lE ":" <*> ty2 <* lE ")" <* lE "by" <*> cds
            <|> lE "def" *>          (mkTypeDecl <$> vE) <* lE ":" <*> ty2 <*           lE "by" <*> cds
  
  return (d4,x2)

decl :: EarleyGrammar Decl
decl = fst <$> declOrTerm

term :: EarleyGrammar Term
term = snd <$> declOrTerm

data Interaction v = IDecl (Decl v)
                   | ITerm (Term v)
                   | ICmnd (String) [String]
                   deriving (Eq, Show)

interaction :: EarleyGrammar Interaction
interaction = mdo
  let cmd  = satisfy (all (\y -> isAlphaNum y || y == '-' || y == '_'))
      cmdE = cmd <?> Thing "a command"
  d <- decl
  t <- term
  
  string <- rule $  l "\"" *> satisfy (all (/= '\"')) <* lE "\""
                <|> satisfy (const True)
  
  args <- rule $ (:) <$> string <*> args <|> pure [] 
  
  rule $  (IDecl <$> d)
      <|> (ITerm <$> t)
      <|> l ":" *> (ICmnd <$> cmdE) <*> args


-- Printing:

class Pprable t where
    pprS :: t String -> (Int, ShowS)

ppr :: Pprable t => t String -> String
ppr x = snd (pprS x) []

ss :: String -> ShowS
ss = showString

slvl :: Int -> (Int, ShowS) -> ShowS
slvl i (lvl, str) = if lvl > i then ss "(" . str . ss ")" else str

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
      = (4, ss "def " . ss n . ss " : " . slvl 2 (pprS ty) . ss "\n" . ss (replicate (5 + length n) ' ') . ss "= " . slvl 2 (pprS defn))
    pprS (TypeDecl it)
      = (4, ss "def " . snd (pprS it))

instance Pprable IndType where
    pprS (IndType n ty scope)
      = (4, ss n . ss " : " . slvl 2 (pprS ty) . ss " by" . (if null (unTypeCons cs) then ss " ()" else snd (pprS cs)))
      where cs = instantiate [(T,n)] scope

pprS_TypeConsTail :: [TypeCon String] -> (Int, ShowS)
pprS_TypeConsTail (c:cs) = (4, ss ",\n    " . snd (pprS c) . snd (pprS_TypeConsTail cs))
pprS_TypeConsTail []     = (4, id)

instance Pprable TypeCons where
    pprS (TypeCons (c:cs)) = (4, ss "\n    " . snd (pprS c) . snd (pprS_TypeConsTail cs))
    pprS (TypeCons [])     = (4, id)

instance Pprable TypeCon where
    pprS (Con n ty) = (4, ss n . ss " : " . slvl 2 (pprS ty))
    pprS (IdCon n tyA tyB) = (4, ss n . ss " : " . slvl 1 (pprS tyA) . ss " = " . slvl 1 (pprS tyB))

instance Pprable Interaction where
    pprS (IDecl d) = pprS d
    pprS (ITerm t) = pprS t
    pprS (ICmnd cmd args) = (4, ss ":" . ss cmd . ss (if notNull args then " " else "") 
                                       . ss (intercalate " " args))