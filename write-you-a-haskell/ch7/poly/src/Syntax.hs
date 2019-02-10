module Syntax where

type Name = String

data Expr
  = Var Loc Name
  | App Loc Expr Expr
  | Lam Loc Name Expr
  | Let Loc Name Expr Expr
  | Lit Loc Lit
  | If Loc Expr Expr Expr
  | Fix Loc Expr
  | Op Loc Binop Expr Expr
  deriving (Show, Eq, Ord)

data Lit
  = LInt Integer
  | LBool Bool
  deriving (Show, Eq, Ord)

data Binop = Add | Sub | Mul | Eql
  deriving (Show, Eq, Ord)

type Decl = (String, Expr)

data Program = Program [Decl] Expr deriving (Show, Eq)

data Loc = NoLoc | Located Int
  deriving (Show, Eq, Ord)
