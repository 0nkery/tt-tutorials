module Checker (
  check,
  checkTop,
  TypeError(..)
) where

import           Control.Monad.Except
import           Control.Monad.Reader

import           Pretty
import           Syntax

type Env = [(Name, Type)]

extend :: (Name, Type) -> Env -> Env
extend xt env = xt : env

data TypeError
  = Mismatch Type Type
  | NotFunction Type
  | NotInScope Name

instance Show TypeError where
  show (Mismatch a b)  = "Expecting " ++ pptype b ++ " but got " ++ pptype a
  show (NotFunction a) = "Tried to apply to non-function type: " ++ pptype a
  show (NotInScope a)  = "Variable " ++ a ++ " is not in scope"

type Check = ExceptT TypeError (Reader Env)

inEnv :: (Name, Type) -> Check a -> Check a
inEnv (x, t) = local (extend (x, t))

lookupVar :: Name -> Check Type
lookupVar x = do
  env <- ask
  case lookup x env of
    Just e  -> return e
    Nothing -> throwError $ NotInScope x

check :: Expr -> Check Type
check (Lit LInt{})  = return TInt
check (Lit LBool{}) = return TBool
check (Lam x t e) = do
  rhs <- inEnv (x, t) (check e)
  return (TArr t rhs)
check (App e1 e2) = do
  t1 <- check e1
  t2 <- check e2
  case t1 of
    (TArr a b) | a == t2 -> return b
               | otherwise -> throwError $ Mismatch t2 a
    ty -> throwError $ NotFunction ty
check (Var x) = lookupVar x

runCheck :: Env -> Check a -> Either TypeError a
runCheck env = flip runReader env . runExceptT

checkTop :: Env -> Expr -> Either TypeError Type
checkTop env x = runCheck env $ check x
