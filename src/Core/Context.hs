{-# LANGUAGE FlexibleContexts #-}

module Core.Context (
    StrExcept,
    CtxElement(..), getName, nominallyEq, getDecls,
    Ctx, emptyCtx, termVar, termVarDef, ulvlVar, ulvlVarDef,
    WithCtx, runWithCtx, runWithEmptyCtx, execWithCtx, execWithEmptyCtx,
    extendCtx, extendCtxReW, modifyCtx, getCtx,
    lookupTermVarMaybe, lookupTermVar, lookupULvlVarMaybe, lookupULvlVar,
    throwError
) where

import Control.Monad.Reader
import Control.Monad.Except
import Data.Maybe
import Data.List

import Utils
import Core.Syntax



data CtxElement v = TermVar Name (Term v) (Maybe (Term v))
                  | ULvlVar Name (Maybe (ULvl v))

getName :: CtxElement v -> Name
getName (TermVar x _ _) = x
getName (ULvlVar i _)   = i

nominallyEq :: CtxElement v -> CtxElement v -> Bool
nominallyEq (TermVar x _ _) (TermVar y _ _) = x == y
nominallyEq (ULvlVar i _)   (ULvlVar j _)   = i == j
nominallyEq _ _ = False

getDecls :: [CtxElement v] -> [Decl v]
getDecls ((TermVar n tyA (Just defn)):xs) = (Decl n tyA defn) : (getDecls xs)
getDecls (_:xs) = getDecls xs
getDecls [] = []


-- The type of a context Γ = (x_1 : T := ?) ... (x_i : T := ?)
type Ctx v = [CtxElement v]

-- The empty context ·
emptyCtx :: Ctx v
emptyCtx = ([])

termVar :: Name -> Term v -> CtxElement v
termVar x ty = TermVar x ty Nothing

termVarDef :: Name -> Term v -> Term v -> CtxElement v
termVarDef x ty def = TermVar x ty (Just def)

ulvlVar :: Name -> CtxElement v
ulvlVar x = ULvlVar x Nothing

ulvlVarDef :: Name -> ULvl v -> CtxElement v
ulvlVarDef x def = ULvlVar x (Just def)


-- A except monad which keeps a context Γ and a list of in-scope universe level variables
type WithCtx v = ReaderT (Ctx v) StrExcept

getCtx :: WithCtx v (Ctx v)
getCtx = ask

extendCtx :: Ctx v -> WithCtx v a -> WithCtx v a
extendCtx xs thing = do
  ctx <- getCtx
  case (getName <$> xs) `intersect` (getName <$> ctx) of
    []  -> local (\ctx -> xs ++ ctx) thing
    [n] -> throwError $ "[Error] [Internal] Name " ++ n ++ " already defined"
    ns  -> throwError $ "[Error] [Internal] Names " ++ (intercalate ", " ns) ++ " already defined"

extendCtxReW ::Ctx v -> WithCtx v a -> WithCtx v a
extendCtxReW xs = local (unionBy nominallyEq xs)

modifyCtx :: (CtxElement v -> CtxElement v) -> WithCtx v a -> WithCtx v a
modifyCtx f = local (map f)


runWithCtx :: Ctx v -> WithCtx v a -> Either String a
runWithCtx ctx x = runExcept (runReaderT x ctx)

execWithCtx :: Ctx v -> WithCtx v a -> a
execWithCtx ctx x = either (\e -> error e) id (runWithCtx ctx x)

runWithEmptyCtx :: WithCtx v a -> Either String a
runWithEmptyCtx = runWithCtx emptyCtx

execWithEmptyCtx :: WithCtx v a -> a
execWithEmptyCtx = execWithCtx emptyCtx



lookupTermVarMaybe :: Name -> WithCtx v (Maybe (Term v, Maybe (Term v)))
lookupTermVarMaybe n = do
  ctx <- ask
  return $ listToMaybe [(ty,def) | TermVar n' ty def <- ctx, n == n'] 

lookupTermVar :: Name -> WithCtx v (Term v, Maybe (Term v))
lookupTermVar n = do
    x <- lookupTermVarMaybe n
    maybe (throwError $ "[Error] [Internal] The variable " ++ show n ++ " is not in scope.") return x

lookupULvlVarMaybe :: Name -> WithCtx v (Maybe (Maybe (ULvl v)))
lookupULvlVarMaybe n = do
  ctx <- ask
  return $ listToMaybe [def | ULvlVar n' def <- ctx, n == n'] 

lookupULvlVar :: Name -> WithCtx v (Maybe (ULvl v))
lookupULvlVar n = do 
    x <- lookupULvlVarMaybe n
    maybe (throwError $ "[Error] [Internal] The variable " ++ show n ++ " is not in scope.") return x

