{-# LANGUAGE ExplicitForAll, RankNTypes, FlexibleContexts #-}

-- | This module builds on the Earley Haskell library to provide an interface
-- for parsing. The intention is to evenutally replace the functions
-- 'tokenize' and 'untokenize' with something far more robust.
module Parser (
    -- * Parsing
    ParseExpect(..), flattenExpected,
    EarleyGrammar, EarleyPair, l, lE,
    parseExcept, parseExceptIO, parseRaw, parseOneUnsafe,
    -- ** Exported from the Earley Haskell library
    rule, satisfy, terminal, (<?>),
    -- * Tokenizing
    tokenize, untokenizeS, untokenize
) where

import Debug.Trace
import Control.Monad.Except
import Data.Bifunctor
import Data.List

import Text.Earley

import Utils



-- ==============
--   TOKENIZING
-- ==============
-- a temporary solution...

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
                   refine acc ('@':xs) = (\x -> acc:"@":x) <$> refine [] xs
                   refine acc ('\"':xs) = (\x -> acc:"\"":x) <$> refine [] xs
                   refine acc ('+':xs) = (\x -> acc:"+":x) <$> refine [] xs -- <- TEMPORARY
                   refine acc (x:xs)   = refine (acc ++ [x]) xs
                   refine acc []       = return [acc]
                in do refined <- concat <$> mapM (refine []) (words str)
                      return (filter notNull refined)

untokenizeS :: [String] -> ShowS
untokenizeS (x:"}":xs) = showString x . untokenizeS ("}":xs)
untokenizeS (x:")":xs) = showString x . untokenizeS (")":xs)
untokenizeS (x:",":xs) = showString x . untokenizeS (",":xs)
untokenizeS ("𝕋{":xs) = showString "𝕋{" . untokenizeS xs
untokenizeS ("{":xs) = showString "{" . untokenizeS xs
untokenizeS ("(":xs) = showString "(" . untokenizeS xs
untokenizeS ("@":xs) = showString "@" . untokenizeS xs
untokenizeS ("+":xs) = showString "+" . untokenizeS xs
untokenizeS (x:xs) = showString x . showString " " . untokenizeS xs
untokenizeS [] = id
-- ^ currently does not support \"-delimited strings!!

untokenize :: [String] -> String
untokenize x = untokenizeS x []



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

-- | Type synonym for an Earley 'Grammar'
type EarleyGrammar t  = forall r. Grammar r (Prod r ParseExpect String (t String))
-- | Type synonym for a pair of Earley 'Grammar's
type EarleyPair t1 t2 = forall r. Grammar r (Prod r ParseExpect String (t1 String), Prod r ParseExpect String (t2 String))

-- | Shorthand for a literal in a grammar definition. Will not be reported as
-- expected on a failed parse.
l :: String -> Prod r ParseExpect String String
l = token

-- | Like 'l', but will be reported as expected on a failed parse.
lE :: String -> Prod r ParseExpect String String
lE s = token s <?> Lit s

-- | Given an 'EarleyGrammar' and a 'String', tokenizes and parses the string
-- according to 'tokenize' and the given grammar. Throws an error with 'StrExcept'
-- in the event of a tokenizing or parsing error.
parseExcept :: EarleyGrammar t -> String -> StrExcept [t String]
parseExcept g str = do
  tks <- tokenize str
  case tks of
    [] -> return []
    _  -> case fullParses (parser g) tks of
        ([], Report pos expd _) ->
            throwError $ "[Error] [Parse] Parsing failed on:\n"
                ++ untokenize tks ++ "\n"
                ++ (replicate (length (untokenize (take pos tks))) ' ') ++ "^"
                ++ case nub (flattenExpected expd) of
                     []  -> ""
                     xs  -> "\nExpected " ++ (intercalate " or " xs) ++ ", got "
                            ++ (if pos < length tks then "\"" ++ (tks !! pos) ++ "\"." else "nothing.")
        (parses, Report _ _ _) -> return parses

-- | Like 'parseExcept', but if an error occurs it is printed and @[]@ is returned
parseExceptIO :: EarleyGrammar t -> String -> IO [t String]
parseExceptIO g = either (\err -> putStrLn err >> return []) (return) . runExcept . parseExcept g

-- | The raw output of a parse. 'tokenize' must not throw an error
parseRaw :: EarleyGrammar t -> String -> ([t String], Report ParseExpect [String])
parseRaw g str = case runExcept $ tokenize str of
                     Right tks -> fullParses (parser g) tks
                     Left err  -> error $ "\'tokenize\' hit an error: " ++ err

-- | Like 'parseExcept', but fails if an error is thrown or the parse is ambiguous
parseOneUnsafe :: Show (t String) => EarleyGrammar t -> String -> (t String)
parseOneUnsafe g str = case runExcept $ parseExcept g str of
                           Right [x] -> x
                           Right xs  -> trace ("\'parseOneUnsafe\' did not recieve exactly one parse! We got: " ++ show xs) (head xs)
                           Left err  -> error ("\'parseWithError\' hit an error: " ++ err)