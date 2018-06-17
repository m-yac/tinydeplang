{-# LANGUAGE ExplicitForAll, RankNTypes, FlexibleContexts,
             DeriveFunctor, DeriveFoldable, DeriveTraversable,
             TypeSynonymInstances, FlexibleInstances  #-}

-- | This module builds on the Earley Haskell library to provide an interface
-- for parsing. The intention is to evenutally replace the functions
-- 'tokenize' and 'untokenize' with something far more robust.
module Parser (
    -- * Parsing
    ParseExpect(..), flattenExpected,
    EarleyGrammar, EarleyPair, l, lE, w, wo, dnl, varBy, terminalBy,
    parseExcept, parseExceptIO, parseRaw, parseOneUnsafe,
    -- ** Exported from the Earley Haskell library
    rule, satisfy, terminal, (<?>),
    -- * Tokenizing
    Token, GenToken(..), isStr, isWhitespace, isMultiNewLine,
    unToken, untokenize, untokenizeS,
    TkFunction, TkAction(..), tokenize, separateLines
) where

import Debug.Trace
import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import Data.List
import Data.Char

import Text.Earley

import Utils



-- ==============
--   TOKENIZING
-- ==============

data GenToken v = Str v
                | Whitespace String
                | MultiNewLine String
                deriving (Eq, Functor, Foldable, Traversable)

instance Applicative GenToken where
    pure = Str
    (Str f) <*> x = fmap f x
    (Whitespace s) <*> _ = Whitespace s
    (MultiNewLine s) <*> _ = MultiNewLine s

instance Monad GenToken where
    (Str x) >>= f = f x
    (Whitespace s) >>= f = Whitespace s
    (MultiNewLine s) >>= f = MultiNewLine s

isStr :: GenToken v -> Bool
isStr (Str _) = True
isStr _ = False

isWhitespace :: GenToken v -> Bool
isWhitespace (Whitespace _) = True
isWhitespace _ = False

isMultiNewLine :: GenToken v -> Bool
isMultiNewLine (MultiNewLine _) = True
isMultiNewLine _ = False

-- | The type of a token, can be a string of non-whitespace characters ('Str'),
-- a string of whitespace characters ('Whitespace'), or a string of two or more
-- newline characters ('MultiNewLine'). 'Whitespace' can include substrings of
-- less than two newline characters.
type Token = GenToken String

instance Show Token where
    show (Str s) = show s
    show (Whitespace s) = show s
    show (MultiNewLine s) = show s

-- | Turns a token back into a 'String'
unToken :: Token -> String
unToken (Str s) = s
unToken (Whitespace s) = s
unToken (MultiNewLine s) = s

untokenizeS :: [Token] -> ShowS
untokenizeS = foldr (\a b -> showString (unToken a) . b) id

-- | Turns a sequence of tokens back into a 'String'
untokenize :: [Token] -> String
untokenize ts = untokenizeS ts []

-- | The type of a tokenizer function (see 'tokenize')
type TkFunction = String -> TkAction

-- | ...
data TkAction = Continue         -- ^ Advances to the next character
              | SplitLeft        -- ^ Splits to the left of the current character,
                                 --   then advances
              | SplitRight       -- ^ Splits to the right of the current character,
                                 --   then advances
              | Split Int        -- ^ Splits to the left of the current character
                                 --   and n units to the right (Split 0 ~ SplitLeft),
                                 --   then advances
              | SplitIsolate Int -- ^ If n > 0, splits to the left of the current
                                 --   character and n units to the right, buffering
                                 --   each split with invisible whitespace, then advances

-- | ...
tokenize :: TkFunction -> String -> [Token]
tokenize f str = dropWhile isWhitespace . dropWhileEnd isWhitespace
                 . concat_whitespace $ split_multi_new_line str
                                       =>>= split_wspace
                                       =>>= split_special f

(=>>=) :: (Monad m, Traversable n, Monad n) => m (n a) -> (a -> m (n a)) -> m (n a)
x =>>= f = x >>= (fmap join . traverse f)

split_multi_new_line :: String -> [Token]
split_multi_new_line = filter (all notNull) . go []
    where go accum [] = [Str accum]
          go accum (x:xs) = let (nls,rest) = span (== '\n') (x:xs)
                             in case nls of
                                  _:_:_ -> (Str accum) : (MultiNewLine nls)
                                                       : (go [] rest)
                                  _ -> go (accum ++ [x]) xs

split_wspace :: String -> [Token]
split_wspace str = case span isSpace str of 
    ([],[]) -> []
    (sp,xs) -> let (nsp,xs') = break isSpace xs
                in case sp of
                     [] -> (Str nsp) : split_wspace xs'
                     _  -> (Whitespace sp) : (Str nsp) : split_wspace xs'

-- Note: SplitIsolate leaves weird 'Whitespace' tokens when the result of this
-- function is used in a broader scope! Must run 'concat_whitespace' before using!!
split_special :: TkFunction -> String -> [Token]
split_special f = filter (all notNull) . go []
    where go acc (x:xs) = case f (x:xs) of
                              Continue -> go (acc ++ [x]) xs
                              SplitLeft -> (Str acc) : (go [x] xs)
                              SplitRight -> (Str (acc ++ [x])) : (go [] xs)
                              Split n -> if n <= 0 then (Str acc) : (go [x] xs)
                                         else let (xsl,xsr) = splitAt n (x:xs)
                                               in (Str acc) : (Str xsl) : (go [] xsr)
                              SplitIsolate n
                                -> if n <= 0 then go (acc ++ [x]) xs
                                   else let (xsl,xsr) = splitAt n (x:xs)
                                         in (Str acc) : (Whitespace "")
                                                      : (Str xsl)
                                                      : (Whitespace "")
                                                      : (go [] xsr)
          go acc [] = [Str acc]

concat_whitespace :: [Token] -> [Token]
concat_whitespace ((Whitespace s1):(Whitespace s2):xs)
    = concat_whitespace ((Whitespace (s1++s2)):xs)
concat_whitespace ((MultiNewLine s1):(MultiNewLine s2):xs) -- just to be safe
    = concat_whitespace ((MultiNewLine (s1++s2)):xs)
concat_whitespace (x:xs) = x : concat_whitespace xs
concat_whitespace [] = []

-- | ...
separateLines :: [Token] -> [[Token]]
separateLines = go []
  where go accum ((MultiNewLine _):xs) = accum : go [] xs
        go accum (x:xs) = go (accum ++ [x]) xs
        go accum [] = if null accum then [] else [accum]


-- ===========
--   PARSING
-- ===========
-- using the Earley Haskell library

-- | Used to report what is expected next on a failed parse
data ParseExpect = Thing String | Lit String
                 deriving (Eq, Show)

-- | Given a list of Expected values, returns a list of strings with each
-- properly printed, and the set in proper order.
flattenExpected :: [ParseExpect] -> [String]
flattenExpected tls = let (ts,ls) = sep tls in ts ++ ls
    where sep ((Thing str):xs) = first (str:) (sep xs)
          sep ((Lit   str):xs) = second (("\"" ++ str ++ "\""):) (sep xs)
          sep [] = ([],[])

-- | Type synonym for an Earley 'Prod'
type EarleyProd r a = Prod r ParseExpect Token a

-- | Type synonym for an Earley 'Grammar'
type EarleyGrammar t  = forall r. Grammar r (EarleyProd r (t String))
-- | Type synonym for a pair of Earley 'Grammar's
type EarleyPair t1 t2 = forall r. Grammar r (EarleyProd r (t1 String),
                                             EarleyProd r (t2 String))

-- | Shorthand for a literal in a grammar definition. Will not be reported as
-- expected on a failed parse.
l :: String -> EarleyProd r Token
l = token . Str

-- | Like 'l', but will be reported as expected on a failed parse.
lE :: String -> EarleyProd r Token
lE s = l s <?> Lit s

-- | Shorthand for any nonzero ammount of whitespace
w :: EarleyProd r Token
w = satisfy isWhitespace

-- | Shorthand for either whitespace or nothing
wo :: EarleyProd r (Maybe Token)
wo = optional w

-- | Shorthand for a multi-newline
dnl :: EarleyProd r Token
dnl = satisfy isMultiNewLine

-- | ...
varBy :: (String -> Bool) -> EarleyProd r String
varBy f = terminalBy (\s -> if f s then Just s else Nothing)

-- | ...
terminalBy :: (String -> Maybe a) -> EarleyProd r a
terminalBy f = terminal (\a -> case a of Str s -> f s
                                         _     -> Nothing)

-- | Given an 'EarleyGrammar', parses a list of tokens. Throws an error with
-- 'StrExcept' in the event of a parsing error.
parseExcept :: EarleyGrammar t -> [Token] -> StrExcept [t String]
parseExcept g tks = case tks of
    [] -> return []
    _  -> case fullParses (parser g) tks of
        ([], Report pos expd _) ->
            throwError $ "[Error] [Parse] Parsing failed on:\n"
                ++ untokenize tks ++ "\n"
                ++ (replicate (length (untokenize (take pos tks))) ' ') ++ "^"
                ++ case nub (flattenExpected expd) of
                     []  -> ""
                     xs  -> "\nExpected " ++ (intercalate " or " xs) ++ ", got "
                            ++ (if pos < length tks then show (tks !! pos) ++ "."
                                                    else "nothing.")
        (parses, Report _ _ _) -> return parses

-- | Like 'parseExcept', but if an error occurs it is printed and @[]@ is returned
parseExceptIO :: EarleyGrammar t -> [Token] -> IO [t String]
parseExceptIO g = either (\err -> putStrLn err >> return []) (return) . runExcept . parseExcept g

-- | The raw output of a parse
parseRaw :: EarleyGrammar t -> [Token] -> ([t String], Report ParseExpect [Token])
parseRaw g = fullParses (parser g)

-- | Like 'parseExcept', but fails if an error is thrown or the parse is ambiguous
parseOneUnsafe :: Show (t String) => EarleyGrammar t -> [Token] -> (t String)
parseOneUnsafe g tks = case runExcept $ parseExcept g tks of
    Right [x] -> x
    Right xs  -> trace ("\'parseOneUnsafe\' did not recieve exactly one parse! We got: " ++ show xs) (head xs)
    Left err  -> error ("\'parseWithError\' hit an error: " ++ err)