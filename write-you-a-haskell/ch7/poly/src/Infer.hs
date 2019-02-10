{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Infer (
  Constraint,
  TypeError(..),
  Subst(..),
  inferTop,
  constraintsExpr
) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.List              (nub)
import qualified Data.Map               as Map
import qualified Data.Set               as Set

import           Env
import           Syntax
import           Type

-- Types

type Infer a =
  (
    ReaderT
      Env
      (
        StateT
        InferState
        (
          Except TypeError
        )
      )
      a
  )

newtype InferState = InferState { count :: Int }

initInfer :: InferState
initInfer = InferState { count = 0 }

type Constraint = (Type, Type)

type Unifier = (Subst, [Constraint])

type Solve a = ExceptT TypeError Identity a

newtype Subst = Subst (Map.Map TVar Type)
  deriving (Eq, Ord, Show, Monoid)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set TVar

instance Substitutable Type where
  apply _ (TCon l a)           = TCon l a
  apply (Subst s) t@(TVar _ a) = Map.findWithDefault t a s
  apply s (TArr l t1 t2)       = TArr l (apply s t1) (apply s t2)

  ftv (TCon _ _)     = Set.empty
  ftv (TVar _ a)     = Set.singleton a
  ftv (TArr _ t1 t2) = ftv t1 `Set.union` ftv t2

instance Substitutable Scheme where
  apply (Subst s) (Forall as t) = Forall as $ apply s' t
    where
      s' = Subst $ foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable Constraint where
  apply s (t1, t2) = (apply s t1, apply s t2)
  ftv (t1, t2) = ftv t1 `Set.union` ftv t2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv = foldr (Set.union . ftv) Set.empty

instance Substitutable Env where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env

data TypeError
  = UnificationFail Type Loc Type Loc
  | InfiniteType TVar Loc Type
  | UnboundVariable Name
  | Ambigious [Constraint]
  | UnificationMismatch [Type] [Type]

-- Inference

runInfer :: Env -> Infer (Type, [Constraint]) -> Either TypeError (Type, [Constraint])
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Loc -> Infer Type
fresh l = do
  s <- get
  put s { count = count s + 1 }
  return $ TVar l $ TV (letters !! count s)

instantiate :: Loc -> Scheme -> Infer Type
instantiate l (Forall as t) = do
  as' <- mapM (const (fresh l)) as
  let s = Subst $ Map.fromList $ zip as as'
  return $ apply s t

generalize :: Env -> Type -> Scheme
generalize env t = Forall as t
  where
    as = Set.toList $ ftv t `Set.difference` ftv env

lookupEnv :: Loc -> Name -> Infer Type
lookupEnv l x = do
  (TypeEnv env) <- ask
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable x
    Just s  -> instantiate l s

inEnv :: (Name, Scheme) -> Infer a -> Infer a
inEnv (x, sc) m = do
  let scope e = remove e x `extend` (x, sc)
  local scope m

ops :: Loc -> Binop -> Type
ops l Add = TArr l typeInt (TArr l typeInt typeInt)
ops l Mul = TArr l typeInt (TArr l typeInt typeInt)
ops l Sub = TArr l typeInt (TArr l typeInt typeInt)
ops l Eql = TArr l typeInt (TArr l typeInt typeBool)

infer :: Expr -> Infer (Type, [Constraint])
infer expr = case expr of
  Lit l (LInt _)  -> return (setLoc l typeInt, [])
  Lit l (LBool _) -> return (setLoc l typeBool, [])

  Var l x -> do
    t <- lookupEnv l x
    return (t, [])

  Lam l x e -> do
    tv <- fresh l
    (t, c) <- inEnv (x, Forall [] tv) (infer e)
    return (TArr l tv t, c)

  App l e1 e2 -> do
    (t1, c1) <- infer e1
    (t2, c2) <- infer e2
    tv <- fresh l
    return (tv, c1 ++ c2 ++ [(t1, TArr l t2 tv)])

  Let l x e1 e2 -> do
    env <- ask
    (t1, c1) <- infer e1
    case runSolve c1 of
      Left err -> throwError err
      Right sub -> do
        let sc = generalize (apply sub env) (apply sub t1)
        (t2, c2) <- inEnv (x, sc) $ local (apply sub) (infer e2)
        return (t2, c1 ++ c2)

  Fix l e1 -> do
    (t1, c1) <- infer e1
    tv <- fresh l
    return (tv, c1 ++ [(TArr l tv tv, t1)])

  Op l op e1 e2 -> do
    (t1, c1) <- infer e1
    (t2, c2) <- infer e2
    tv <- fresh l
    let
      u1 = TArr l t1 (TArr l t2 tv)
      u2 = ops l op
    return (tv, c1 ++ c2 ++ [(u1, u2)])

  If l cond tr fl -> do
    (t1, c1) <- infer cond
    (t2, c2) <- infer tr
    (t3, c3) <- infer fl
    return (t2, c1 ++ c2 ++ c3 ++ [(t1, setLoc l typeBool), (t2, t3)])

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar _ a)   = [a]
    fv (TArr _ a b) = fv a ++ fv b
    fv (TCon _ _)   = []

    normtype (TArr l a b) = TArr l (normtype a) (normtype b)
    normtype (TCon l a) = TCon l a
    normtype (TVar l a) = case Prelude.lookup a ord of
      Just x  -> TVar l x
      Nothing -> error "type variable not in signature"

closeOver :: Type -> Scheme
closeOver = normalize . generalize Env.empty

inferExpr :: Env -> Expr -> Either TypeError Scheme
inferExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err    -> Left err
    Right subst -> Right $ closeOver $ apply subst ty

inferTop :: Env -> [(String, Expr)] -> Either TypeError Env
inferTop env [] = Right env
inferTop env ((name, ex) : xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs

constraintsExpr :: Env -> Expr -> Either TypeError ([Constraint], Subst, Type, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where
        sc = closeOver $ apply subst ty

-- Constraint solver

emptySubst :: Subst
emptySubst = mempty

compose :: Subst -> Subst -> Subst
compose (Subst s1) (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

unifyMany :: [Type] -> [Type] -> Solve Subst
unifyMany [] [] = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) = do
  su1 <- unifies t1 t2
  su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
  return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

bind :: TVar -> Type -> Solve Subst
bind a t | eqLoc t a = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a (getLoc t) t
         | otherwise = return (Subst $ Map.singleton a t)

-- | Type variables equal up to location
eqLoc :: Type -> TVar -> Bool
eqLoc (TVar _ a) b = a == b
eqLoc _ _          = False

unifies :: Type -> Type -> Solve Subst
unifies t1 t2                         | t1 == t2 = return emptySubst
unifies (TVar _ v) t                  = bind v t
unifies t (TVar _ v)                  = bind v t
unifies (TArr _ t1 t2) (TArr _ t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies t1 t2                         = throwError $ UnificationFail t1 (getLoc t1) t2 (getLoc t2)

solver :: Unifier -> Solve Subst
solver (su, cs) = case cs of
  [] -> return su
  ((t1, t2) : cs0) -> do
    su1 <- unifies t1 t2
    solver (su1 `compose` su, apply su1 cs0)

runSolve :: [Constraint] -> Either TypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where
    st = (emptySubst, cs)
