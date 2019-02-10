module Eval where

import           Syntax

import           Control.Monad.Identity
import qualified Data.Map               as Map

data Value
  = VInt Integer
  | VBool Bool
  | VClosure String Expr TermEnv

type TermEnv = Map.Map String Value
type Interpreter t = Identity t

emptyTmenv :: TermEnv
emptyTmenv = Map.empty

instance Show Value where
  show (VInt n)   = show n
  show (VBool n)  = show n
  show VClosure{} = "<<closure>>"

binop :: Binop -> Integer -> Integer -> Value
binop Add a b = VInt $ a + b
binop Mul a b = VInt $ a * b
binop Sub a b = VInt $ a - b
binop Eql a b = VBool $ a == b

eval :: TermEnv -> Expr -> Interpreter Value
eval env expr = case expr of
  Lit _ (LInt k)  -> return $ VInt k
  Lit _ (LBool k) -> return $ VBool k

  Var _ x -> do
    let Just v = Map.lookup x env
    return v

  Op _ op a b -> do
    VInt a' <- eval env a
    VInt b' <- eval env b
    return $ binop op a' b'

  Lam _ x body -> return (VClosure x body env)

  App _ fun arg -> do
    VClosure x body clo <- eval env fun
    argv <- eval env arg
    let nenv = Map.insert x argv clo
    eval nenv body

  Let _ x e body -> do
    e' <- eval env e
    let nenv = Map.insert x e' env
    eval nenv body

  If _ cond tr fl -> do
    VBool br <- eval env cond
    if br
      then eval env tr
      else eval env fl

  Fix l e -> eval env (App l e (Fix l e))

runEval :: TermEnv -> String -> Expr -> (Value, TermEnv)
runEval env nm ex =
  let
    res = runIdentity (eval env ex)
  in
    (res, Map.insert nm res env)
