{-# LANGUAGE OverloadedStrings #-}

module Parser (
  parseExpr,
  parseModule,
) where

import           Text.Parsec
import           Text.Parsec.Text.Lazy (Parser)

import qualified Text.Parsec.Expr      as Ex
import qualified Text.Parsec.Token     as Tok

import           Data.Monoid
import           Data.Text.Lazy        as L hiding (foldl, foldr)

import           Lexer
import           Syntax

integer :: Parser Integer
integer = Tok.natural lexer

variable :: Parser Expr
variable = do
  x <- identifier
  l <- sourceLine <$> getPosition
  return $ Var (Located l) x

number :: Parser Expr
number = do
  n <- integer
  l <- sourceLine <$> getPosition
  return (Lit (Located l) (LInt (fromIntegral n)))

bool :: Parser Expr
bool = (reserved "True" >>
    do
      l <- sourceLine <$> getPosition
      return (Lit (Located l) (LBool True))
  )
  <|> (reserved "False" >>
    do
      l <- sourceLine <$> getPosition
      return (Lit (Located l) (LBool False))
  )

fix :: Parser Expr
fix = do
  reservedOp "fix"
  l <- sourceLine <$> getPosition
  ex <- expr
  return $ Fix (Located l) ex

lambda :: Parser Expr
lambda = do
  reservedOp "\\"
  l <- sourceLine <$> getPosition
  args <- many identifier
  reservedOp "->"
  body <- expr
  return $ foldr (Lam (Located l)) body args

letin :: Parser Expr
letin = do
  reserved "let"
  l <- sourceLine <$> getPosition
  x <- identifier
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return (Let (Located l) x e1 e2)

letrecin :: Parser Expr
letrecin = do
  reserved "let"
  reserved "rec"
  l <- sourceLine <$> getPosition
  x <- identifier
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return (Let (Located l) x e1 e2)

ifthen :: Parser Expr
ifthen = do
  reserved "if"
  l <- sourceLine <$> getPosition
  cond <- expr
  reservedOp "then"
  tr <- expr
  reserved "else"
  fl <- expr
  return (If (Located l) cond tr fl)

aexp :: Parser Expr
aexp =
      parens expr
  <|> bool
  <|> number
  <|> ifthen
  <|> fix
  <|> try letrecin
  <|> letin
  <|> lambda
  <|> variable

term :: Parser Expr
term = do
  r <- many1 aexp
  l <- sourceLine <$> getPosition
  return $ Prelude.foldl1 (App (Located l)) r

infixOp :: String -> (a -> a -> a) -> Ex.Assoc -> Op a
infixOp x f = Ex.Infix (reservedOp x >> return f)

table :: Operators Expr
table = [
    [
      infixOp "*" (Op NoLoc Mul) Ex.AssocLeft
    ],
    [
      infixOp "+" (Op NoLoc Add) Ex.AssocLeft,
      infixOp "-" (Op NoLoc Sub) Ex.AssocLeft
    ],
    [
      infixOp "==" (Op NoLoc Eql) Ex.AssocLeft
    ]
  ]

expr :: Parser Expr
expr = Ex.buildExpressionParser table term

type Binding = (String, Expr)

letdecl :: Parser Binding
letdecl = do
  reserved "let"
  l <- sourceLine <$> getPosition
  name <- identifier
  args <- many identifier
  reservedOp "="
  body <- expr
  return (name, foldr (Lam (Located l)) body args)

letrecdecl :: Parser (String, Expr)
letrecdecl = do
  reserved "let"
  reserved "rec"
  l <- sourceLine <$> getPosition
  name <- identifier
  args <- many identifier
  reservedOp "="
  body <- expr
  return (name, Fix (Located l) $ foldr (Lam NoLoc) body (name : args))

val :: Parser Binding
val = do
  ex <- expr
  return ("it", ex)

decl :: Parser Binding
decl = try letrecdecl <|> letdecl <|> val

top :: Parser Binding
top = do
  x <- decl
  optional semi
  return x

modl :: Parser [Binding]
modl = many top

parseExpr :: L.Text -> Either ParseError Expr
parseExpr = parse (contents expr) "<stdin>"

parseModule :: FilePath -> L.Text -> Either ParseError [Binding]
parseModule = parse (contents modl)
