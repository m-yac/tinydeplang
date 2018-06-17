{-# LANGUAGE LambdaCase, RecursiveDo #-}

module Main where

import System.IO
import System.Environment
import Control.Applicative
import Data.Char
import Data.List

import Utils
import Parser
import Core.Syntax
import Core.Context
import Core.Eval
import Core.Check

putStrFlush :: String -> IO ()
putStrFlush s = putStr s >> hFlush stdout

loadFile :: String -> IO (Maybe (Ctx Name, [Decl Name]))
loadFile filename = do
    file <- readFile filename
    decls <- mapM (parseExceptIO decl) (separateLines $ tokenizeCore file)
    if null `any` decls then return Nothing
    else case runWithEmptyCtx (checkFile decls) of
           Left err -> putStrLn err >> return Nothing
           Right (ctx, declsUnamb) -> return (Just (ctx, declsUnamb))

runFile :: String -> IO ()
runFile filename = loadFile filename >>= \case
    Nothing -> return ()
    Just (ctx, declsUnamb) -> do
      putStrLn $ intercalate "\n\n" (reverse (ppr <$> declsUnamb))
      let (TermVar _ _ (Just mainBody)) = head $ filter ((== "main") . getName) ctx
      case runWithCtx ctx (eval NF mainBody) of
        Left err -> putStrLn err
        Right mainNF -> putStrLn $ "\nmain = " ++ ppr mainNF

data Interaction v = IDecl (Decl v)
                   | ITerm (Term v)
                   | ICmnd (String) [Token]
                   deriving (Eq, Show)

interaction :: EarleyGrammar Interaction
interaction = mdo
  let cmd  = varBy (all (\y -> isAlphaNum y || y == '-' || y == '_'))
      cmdE = cmd <?> Thing "a command"
  d <- decl
  t <- term
    
  args <- rule $ (:) <$> satisfy (const True) <*> args
              <|> pure [] 
  
  rule $  (IDecl <$> d)
       <|> (ITerm <$> t)
       <|> l ":" *> (ICmnd <$> cmdE) <*> pure [] 
       <|> l ":" *> (ICmnd <$> cmdE) <*w<*> args

interactive :: Ctx Name -> IO ()
interactive ctx = do
    putStrFlush "hom-core> "
    hSetBuffering stdin LineBuffering
    line <- getLine
    hSetBuffering stdin NoBuffering
    ambs <- parseExceptIO interaction (tokenizeCore line)
    if null ambs then interactive ctx
    else case runWithCtx ctx $ resolveAmbig checkInteraction ambs of
           Left err                        -> putStrLn err
                                              >> interactive ctx
           Right (IAddToCtx ctxElts)       -> interactive (unionBy nominallyEq ctxElts ctx)
           Right (IEvalResult (term, ty))  -> do putStrLn . ppr $ execWithCtx ctx (eval NF term)
                                                 putStrLn $ ": " ++ ppr (execWithCtx ctx (eval NF ty))
                                                 interactive ctx
           Right (IDoCommand IQuit)        -> return ()
           Right (IDoCommand (ILoad arg))  -> loadFile arg >>= \case
                                                Nothing -> do putStrLn $ "[Error] [Interactive] Loading of " ++ arg ++ " failed"
                                                              interactive ctx
                                                Just (ctxElts,ds) -> do putStrLn $ "[Interactive] Loaded " ++ arg
                                                                        putStrLn $ intercalate "\n\n" (reverse (ppr <$> ds))
                                                                        interactive (unionBy nominallyEq ctxElts ctx)
           Right (IDoCommand (IGetType s)) -> do tm <- parseExceptIO term s
                                                 case runWithCtx ctx $ resolveAmbig check tm of
                                                   Left err -> putStrLn err
                                                               >> interactive ctx
                                                   Right ty -> putStrLn (ppr (snd ty))
                                                               >> interactive ctx
           Right (IDoCommand (IGetDefn s)) -> do case runWithCtx ctx $ lookupTermVar s of
                                                   Left err -> putStrLn err
                                                               >> interactive ctx
                                                   Right (ty, (Just def))
                                                            -> putStrLn (s ++ " : " ++ ppr ty)
                                                               >> putStr (replicate (length s) ' ')
                                                               >> putStrLn (" := " ++ ppr def)
                                                               >> interactive ctx
                                                   Right (ty, Nothing)
                                                            -> putStrLn ("\'" ++ s ++ "\' has no definition")
                                                               >> interactive ctx
           Right (IDoCommand IUnknown)     -> putStrLn "[Error] [Interactive] Command not recognized"
                                              >> interactive ctx

data InteractionResult v = IAddToCtx [CtxElement v]
                         | IEvalResult (Term v, Term v)
                         | IDoCommand ICommand

data ICommand = IQuit
              | ILoad String
              | IGetType [Token]
              | IGetDefn String
              | IUnknown

parseCmnd :: String -> [Token] -> ICommand
parseCmnd s []      | s == "quit" || s == "q" = IQuit
parseCmnd s as      | s == "load"             = ILoad (untokenize as)
parseCmnd s as      | s == "type" || s == "t" = IGetType as
parseCmnd s [Str a] | s == "defn" || s == "d" = IGetDefn a
parseCmnd _ _                                 = IUnknown

checkInteraction :: Interaction Name -> WithCtx Name (InteractionResult Name)
checkInteraction (IDecl d)    = IAddToCtx . snd <$> checkDecl d
checkInteraction (ITerm t)    = IEvalResult <$> check t
checkInteraction (ICmnd c as) = pure (IDoCommand $ parseCmnd c as)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ("-i":flags) -> interactive []
        ("-interactive":flags) -> interactive []
        (filename:flags) -> runFile filename
        [] -> error "No source file given. Use the command \"-i\" or \"-interactive\" to start an interactive session."


