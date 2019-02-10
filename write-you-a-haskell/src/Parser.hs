module Parser (parseExpr) where

import           Data.Char

import           Text.Parsec
import           Text.Parsec.Language (haskellStyle)
import           Text.Parsec.String   (Parser)

import qualified Text.Parsec.Expr     as Ex
import qualified Text.Parsec.Token    as Tok

import           Syntax

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["->", "\\", "+", "*", "-", "="]
    names = []
    style = haskellStyle {
      Tok.reservedOpNames = ops,
      Tok.reservedNames = names,
      Tok.commentLine = "#"
    }

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser String
identifier = Tok.identifier lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

contents :: Parser a -> Parser a
contents p = do
  Tok.whiteSpace lexer
  r <- p
  eof
  return r

natural :: Parser Integer
natural = Tok.natural lexer

-- Expressions

variable :: Parser Expr
variable = Var <$> identifier

number :: Parser Expr
number = Lit . LInt . fromIntegral <$> natural

lambda :: Parser Expr
lambda = do
  reservedOp "\\"
  x <- identifier
  reservedOp ":"
  t <- type'
  reservedOp "."
  e <- expr
  return $ Lam x t e

bool :: Parser Expr
bool = (reserved "True" >> return (Lit (LBool True)))
   <|> (reserved "False" >> return (Lit (LBool False)))

term :: Parser Expr
term = parens expr <|> bool <|> number <|> variable <|> lambda

expr :: Parser Expr
expr = do
  es <- many1 term
  return (foldl1 App es)

-- Types

tyatom :: Parser Type
tyatom = tylit <|> parens type'

tylit :: Parser Type
tylit = (reservedOp "Bool" >> return TBool) <|> (reservedOp "Int" >> return TInt)

type' :: Parser Type
type' = Ex.buildExpressionParser tyops tyatom
  where
    infixOp x f = Ex.Infix (reservedOp x >> return f)
    tyops =
      [
        [infixOp "->" TArr Ex.AssocRight]
      ]

parseExpr = parse (contents expr) "<stdin>"
