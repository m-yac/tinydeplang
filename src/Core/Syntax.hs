{-# LANGUAGE LambdaCase,
             RankNTypes,
             MultiParamTypeClasses,
             FlexibleContexts,
             TemplateHaskell,
             RecursiveDo #-}

module Core.Syntax (
  ULvl(..), Term(..), Decl(..), VarTy(..), Name,
  fun, ufun, lam, ulam, mkULvl, leqU, recVarTy,
  decl, term, interaction, Interaction(..),
  parseExcept, parseExceptIO, parseRaw, parseOneUnsafe,
  Pprable(..), ppr
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Data.Functor.Classes
import Data.Foldable
import Data.Traversable
import Data.Bifunctor
import Data.Deriving (deriveShow1) 
import Data.Maybe
import Data.List
import Text.PrettyPrint

import Text.Earley
import Data.Char
import Text.Read

import Utils





-- ==============
--   THE SYNTAX
-- ==============

-- Meta: UIndices are i
--       Variables are x,y
--       Terms are X,Y
--       Type-like terms are A,B

data ULvl v = UO                                      -- ^ 0                [UO]
            | USuc (ULvl v)                           -- ^ S i              [USuc i]
            | UMax (ULvl v) (ULvl v)                  -- ^ max i j          [UMax i j]
            | UVar v                                  -- ^ i                [UVar i]
data Term v = Var v                                   -- ^ x                [Var x]
            | App (Term v) (Term v)                   -- ^ X Y              [App X Y]
            | Lam Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) >-> X    [Lam "x" A (x. X)]
            | Fun Name (Term v) (Scope VarTy Term v)  -- ^ (x : A) -> B     [Fun "x" A (x. B)]
            | Undefined (Term v)                      -- ^ undefined : A    [Undefined A]
            | Universe (ULvl v)                       -- ^ 𝕋{i}             [Universe i]
            | UniverseTop                             -- ^ 𝕋{ω}             [UniverseTop]
            | ULvlApp (Term v) (ULvl v)               -- ^ X i              [ULvlApp X i]
            | ULvlLam Name (Scope VarTy Term v)       -- ^ i >-> A          [ULvlLam i (i. A)]
            | ULvlFun Name (Scope VarTy Term v)       -- ^ ∀ i. A           [ULvlLam i (i. A)]
data Decl v = Decl Name (Term v) (Term v)             -- ^ def (x : A) = X  [Decl "x" A X]
            | TypeDecl (IndType v)                    -- ^ def type ...     [TypeDecl ...]

-- Inductive types
data IndType v = IndType Name (Term v) (Scope IndTy TypeCons v)
data TypeCon v = TypeCon Name (Term v)
newtype TypeCons v = TypeCons { unTypeCons :: [TypeCon v] }

data VarTy = V | I deriving (Eq, Ord, Read, Show)
data IndTy = T     deriving (Eq, Ord, Read, Show)

type Name = String

-- Encoding variable binding:
instance Functor ULvl where
    fmap f (UO)                 = UO
    fmap f (USuc i)             = USuc (f <$> i)
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
    fmap f (TypeCon n ty)       = TypeCon n (f <$> ty)

-- Encoding where our variables live:
instance Boxed ULvl where
    box = UVar
instance Boxed Term where
    box = Var

-- Encoding substitution:
instance Subst ULvl ULvl where
    (UO) *>>= f                 = UO
    (USuc i) *>>= f             = USuc (i *>>= f)
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
    (TypeCon n ty) *>>= f       = TypeCon n (ty *>>= f)

-- Encoding alpha-equivalence:
instance Eq1 ULvl where
    liftEq r (UO) (UO)                             = True
    liftEq r (USuc i) (USuc j)                     = liftEq r i j
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
    liftEq r (TypeCon _ t)     (TypeCon _ t')       = liftEq r t t'

-- Useful for reasoning about free variables:
instance Foldable ULvl where
    foldMap f (UO)                 = mempty
    foldMap f (USuc i)             = foldMap f i
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
    traverse f (UO)                 = pure UO
    traverse f (USuc i)             = USuc <$> traverse f i
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





-- ====================
--   HELPER FUNCTIONS
-- ====================

usuc :: Int -> ULvl a -> ULvl a
usuc i = if i < 0 then error $ "Cannot have a negative ULevel " ++ show i
         else if i == 0 then id else usuc (i-1) . USuc

mkULvl :: Int -> ULvl a
mkULvl i = usuc i UO

lam :: Name -> Term Name -> Term Name -> Term Name
lam x tyA body = Lam x tyA (abstract [(x,V)] body)

fun :: Name -> Term Name -> Term Name -> Term Name
fun x tyA tyB = Fun x tyA (abstract [(x,V)] tyB)

ulam :: Name -> Term Name -> Term Name
ulam i body = ULvlLam i (abstract [(i,I)] body)

ufun :: Name -> Term Name -> Term Name
ufun i tyA = ULvlFun i (abstract [(i,I)] tyA)

tyDecl :: Name -> Term Name -> [TypeCon Name] -> Decl Name
tyDecl x ty cs = TypeDecl (IndType x ty (abstract [(x,T)] (TypeCons cs)))

-- Assuming both arguments are in normal form...
leqU :: ULvl v -> ULvl v -> Maybe Bool
leqU UO UO = Just True
leqU UO (USuc _) = Just True
leqU (USuc _) UO = Just False
leqU (USuc i) (USuc j) = leqU i j
leqU _ _ = Nothing

recVarTy :: a -> a -> VarTy -> a
recVarTy x _ V = x
recVarTy _ x I = x





-- ========================
--   PARSING AND PRINTING
-- ========================

data ParseExpect = Thing String | Lit String
                 deriving (Eq, Show)

flattenExpected :: [ParseExpect] -> [String]
flattenExpected xs = let (ts,ls) = sep xs in ts ++ ls
    where sep ((Thing str):xs) = first (str:) (sep xs)
          sep ((Lit   str):xs) = second (("\"" ++ str ++ "\""):) (sep xs)
          sep [] = ([],[])

keywords :: [String]
keywords = ["forall", "undefined", "def"]

varparseWild (x:xs) = ( x == '_' && null xs ) || varparse (x:xs)
varparseWild _      = False
varparse     (x:xs) = (x:xs) `notElem` keywords
                      && isAlpha x && x /= '𝕋'
                      && all (\y -> isAlphaNum y || y == '-' || y == '_') xs
varparse     _      = False

decl :: Grammar r (Prod r ParseExpect String (Decl Name))
decl = mdo
  let l = token
      v = satisfy varparse
  t <- term
  
  let lE s = l s <?> Lit s
      vE = v <?> Thing "a variable"
      ty = t <?> Thing "a type"
      tm = t <?> Thing "a term"
  
  c <- rule $  l "(" *> (TypeCon <$> v) <* lE ":" <*> ty <* lE ")"
           <|>          (TypeCon <$> v) <* lE ":" <*> ty

  cs <- rule $  ((:) <$> c) <* l "," <*> cnstr
            <|> ((:[]) <$> c)
  
  let cnstr = cs <?> Thing "a constructor declaration"
  
  cds <- rule $ cnstr <|> lE "(" *> pure [] <* lE ")"
  
  rule $  lE "def" *>              l "(" *>   (Decl <$> vE) <* lE ":" <*> ty <* lE ")" <* lE "=" <*> tm
      <|> lE "def" *>                         (Decl <$> vE) <* lE ":" <*> ty <*           lE "=" <*> tm
      <|> lE "def" *> lE "type" *> l "(" *> (tyDecl <$> vE) <* lE ":" <*> ty <* lE ")" <* lE "where" <*> cds
      <|> lE "def" *> lE "type" *>          (tyDecl <$> vE) <* lE ":" <*> ty <*           lE "where" <*> cds

term :: Grammar r (Prod r ParseExpect String (Term Name))
term = mdo
  let l    = token
      v    = satisfy varparse
      vORw = satisfy varparseWild
      integer = terminal (\x -> do { i <- readMaybe x ; if i < 0 then Nothing else Just i })
  
  let lE s = l s <?> Lit s
      vE = v <?> Thing "a variable"
      vORwE = (vORw <?> Thing "a variable") <?> Lit "_"

  i0 <- rule $  mkULvl <$> integer
            <|> UVar <$> v
            <|> l "(" *> i1 <* l ")"

  i1 <- rule $  usuc <$> integer <* l " + " <*> ulvl1
            <|> l "max" *> (UMax <$> ulvl0) <*> ulvl0
            <|> i0
  
  let [ulvl0,ulvl1] = (<?> Thing "a universe level") <$> [i0,i1]

  x0 <- rule $  Var <$> v
            <|> l "𝕋{" *> (Universe <$> ulvl1) <* lE "}"
            <|> l "𝕋{ω}" *> pure UniverseTop
            <|> l "(" *> tm2 <* lE ")"
  
  x1 <- rule $      App <$> (x1) <*> (x0)
            <|> ULvlApp <$> (x1) <*> (i0)
            <|> x0
  
  x2 <- rule $  xlam
            <|> l "forall" *> xfalls
            <|> l "(" *>  (fun <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <* lE "->" <*> (ty2)
            <|>           (fun "__")                <$> (ty1)           <* lE "->" <*> (ty2)
            <|> l "∀" *> (ufun <$> vE)    <* lE "," <*> (ty2)
            <|> l "undefined" *> lE ":" *> (Undefined <$> ty2)
            <|> x1
  
  let [tm0,tm1,tm2] = (<?> Thing "a term") <$> [x0,x1,x2]
  let [ty0,ty1,ty2] = (<?> Thing "a type") <$> [x0,x1,x2]
  
  xlam <- rule $  l "(" *>  (lam <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <*> (xlam)
              <|> l "(" *>  (lam <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <* lE ">->" <*> (tm2)
              <|> l "(" *> (ulam <$> vORwE)                     <* lE ")" <*> (xlam)
              <|> l "(" *> (ulam <$> vORwE)                     <* lE ")" <* lE ">->" <*> (tm2)
  
  xfalls <- rule $  lE "(" *> (fun <$> vORwE) <* lE ":" <*> (ty2) <* lE ")" <*> (xfalls)
                <|> lE "," *> (ty2)
  
  return x2

data Interaction v = IDecl (Decl v)
                   | ITerm (Term v)
                   | ICmnd (String) [String]
                   deriving (Eq, Show)

interaction :: Grammar r (Prod r ParseExpect String (Interaction Name))
interaction = mdo
  let l    = token
      lE s = l s <?> Lit s
      cmd  = satisfy (all (\y -> isAlphaNum y || y == '-' || y == '_'))
      cmdE = cmd <?> Thing "a command"
  d <- decl
  t <- term
  
  string <- rule $  l "\"" *> satisfy (all (/= '\"')) <* lE "\""
                <|> cmd
  
  args <- rule $ (:) <$> string <*> args <|> pure [] 
  
  rule $  (IDecl <$> d)
      <|> (ITerm <$> t)
      <|> l ":" *> (ICmnd <$> cmdE) <*> args

tokenize :: String -> StrExcept [String]
tokenize str = let refine acc ('𝕋':xs) = case xs of '{':'ω':'}':xs' -> (\x -> acc:"𝕋{ω}":x) <$> refine [] xs'
                                                    '{':xs'         -> (\x -> acc:"𝕋{"  :x) <$> refine [] xs'
                                                    -- 'I':'d':'x':xs' -> (acc : "𝕋Idx" :) <$> refine [] xs'
                                                    _ -> throwError $ "[Error] [Tokenize] Illegal use of 𝕋 in: " ++ show ('𝕋':xs) 
                   refine acc ('{':xs) = (\x -> acc:"{":x) <$> refine [] xs
                   refine acc ('}':xs) = (\x -> acc:"}":x) <$> refine [] xs
                   refine acc (':':xs) = (\x -> acc:":":x) <$> refine [] xs
                   refine acc ('(':xs) = (\x -> acc:"(":x) <$> refine [] xs
                   refine acc (')':xs) = (\x -> acc:")":x) <$> refine [] xs
                   refine acc (',':xs) = (\x -> acc:",":x) <$> refine [] xs
                   refine acc ('\"':xs) = (\x -> acc:"\"":x) <$> refine [] xs
                   refine acc (x:xs)   = refine (acc ++ [x]) xs
                   refine acc []       = return [acc]
                in do refined <- concat <$> mapM (refine []) (words str)
                      return (filter notNull refined)

-- TODO add support for strings...
untokenizeS :: [String] -> ShowS
untokenizeS (x:"}":xs) = ss x . untokenizeS ("}":xs)
untokenizeS (x:")":xs) = ss x . untokenizeS (")":xs)
untokenizeS (x:",":xs) = ss x . untokenizeS (",":xs)
untokenizeS ("𝕋{":xs) = ss "𝕋{" . untokenizeS xs
untokenizeS ("{":xs) = ss "{" . untokenizeS xs
untokenizeS ("(":xs) = ss "(" . untokenizeS xs
untokenizeS (x:xs) = ss x . ss " " . untokenizeS xs
untokenizeS [] = id

untokenize :: [String] -> String
untokenize x = untokenizeS x []

parseExcept :: (forall r. Grammar r (Prod r ParseExpect String (t Name))) -> String -> StrExcept [t Name]
parseExcept g str = do
  tks <- tokenize str
  case tks of
    [] -> return []
    (x:xs) -> case fullParses (parser g) tks of
        ([], Report pos expd _) ->
            throwError $ "[Error] [Parse] Parsing failed on:\n"
                ++ untokenize tks ++ "\n"
                ++ (replicate (length (untokenize (take pos tks))) ' ') ++ "^"
                ++ case nub (flattenExpected expd) of
                     []  -> ""
                     xs  -> "\nExpected " ++ (intercalate " or " xs) ++ ", got "
                            ++ (if pos < length tks then "\"" ++ (tks !! pos) ++ "\"." else "nothing.")
        (parses, Report _ _ _) -> return parses

parseExceptIO :: (forall r. Grammar r (Prod r ParseExpect String (t Name))) -> String -> IO [t Name]
parseExceptIO g = either (\err -> putStrLn err >> return []) (return) . runExcept . parseExcept g

parseRaw :: (forall r. Grammar r (Prod r ParseExpect String (t Name))) -> String -> ([t Name], Report ParseExpect [String])
parseRaw g str = case runExcept $ tokenize str of
                     Right tks -> fullParses (parser g) tks
                     Left err  -> error $ "\'tokenize\' hit an error: " ++ err

parseOneUnsafe :: Show (t Name) => (forall r. Grammar r (Prod r ParseExpect String (t Name))) -> String -> (t Name)
parseOneUnsafe g str = case runExcept $ parseExcept g str of
                           Right [x] -> x
                           Right xs  -> error $ "\'parseOneUnsafe\' did not recieve exactly one parse! We got: " ++ show xs
                           Left err  -> error $ "\'parseWithError g str\' hit an error: " ++ err

testParse :: String -> Bool -> IO ()
testParse str b = let (parsed, report) = parseRaw term str
                   in putStr . unlines . (if null (unconsumed report) then id else (:) ("Error: " ++ show report))
                       $ (\s -> (snd (pprS s) []) ++ (if b then "\n" ++ (show s) else "")) <$> (fst $ parseRaw term str)




-- Printing:

class Pprable t where
    pprS :: t String -> (Int, ShowS)

ppr :: Pprable t => t String -> String
ppr x = snd (pprS x) []

ss :: String -> ShowS
ss = showString

slvl :: Int -> (Int, ShowS) -> ShowS
slvl i (lvl, str) = if lvl > i then ss "(" . str . ss ")" else str


data ULvlPpr = ULvlInt Int | ULvlStr Int ShowS

pprSU' :: ULvl String -> (Int, ULvlPpr)
pprSU' (UVar v)          = (0, ULvlStr 0 $ ss v)
pprSU' (UO)              = (0, ULvlInt 0)
pprSU' (USuc i)          = case pprSU' i of (_, ULvlInt x  ) -> (0, ULvlInt (x+1)  )
                                            (_, ULvlStr x s) -> (1, ULvlStr (x+1) s)
pprSU' (UMax i j)        = (1, ULvlStr 0 $ ss "max " . slvl 0 (pprS i) . ss " " . slvl 0 (pprS j))

instance Pprable ULvl where
    pprS = fmap (\case ULvlInt i   -> ss (show i)
                       ULvlStr 0 s -> s
                       ULvlStr i s -> ss (show i) . ss " + " . s) . pprSU'


pprS_Lams :: Term String -> (Int, ShowS)
pprS_Lams (Lam n tyA scope) = (2, ss "(" . ss n . ss " : " . slvl 2 (pprS tyA) . ss ") " . slvl 2 (pprS_Lams $ instantiate [(V,n)] scope))
pprS_Lams (ULvlLam n scope) = (2, ss "(" . ss n                                . ss ") " . slvl 2 (pprS_Lams $ instantiate [(I,n)] scope))
pprS_Lams term              = (2, ss ">-> " . slvl 2 (pprS term))

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
    pprS (ULvlApp x i)     = (1, slvl 1 (pprS x) . ss " " . slvl 0 (pprS i))
    pprS (ULvlLam n scope) = pprS_Lams (ULvlLam n scope)
    pprS (ULvlFun n scope) = (2, ss "∀ " . ss n . ss ", " . slvl 2 (pprS $ instantiate [(I,n)] scope))

instance Pprable Decl where
    pprS (Decl n ty defn)
      = (4, ss "def " . ss n . ss " : " . slvl 2 (pprS ty) . ss "\n" . ss (replicate (5 + length n) ' ') . ss "= " . slvl 2 (pprS defn))
    pprS (TypeDecl it)
      = (4, ss "def " . snd (pprS it))

instance Pprable IndType where
    pprS (IndType n ty scope)
      = (4, ss "type " . ss n . ss " : " . slvl 2 (pprS ty) . ss " where" . (if null (unTypeCons cs) then ss " ()" else snd (pprS cs)))
      where cs = instantiate [(T,n)] scope

pprS_TypeConsTail :: [TypeCon String] -> (Int, ShowS)
pprS_TypeConsTail (c:cs) = (4, ss ",\n    " . snd (pprS c) . snd (pprS_TypeConsTail cs))
pprS_TypeConsTail []     = (4, id)

instance Pprable TypeCons where
    pprS (TypeCons (c:cs)) = (4, ss "\n    " . snd (pprS c) . snd (pprS_TypeConsTail cs))
    pprS (TypeCons [])     = (4, id)

instance Pprable TypeCon where
    pprS (TypeCon n ty) = (4, ss n . ss " : " . slvl 2 (pprS ty))


