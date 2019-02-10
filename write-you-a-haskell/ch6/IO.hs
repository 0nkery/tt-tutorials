{-# LANGUAGE RankNTypes #-}

import           Control.Monad

type Name = String

data ExprP a
  = VarP a
  | GlobalP Name
  | AppP (ExprP a) (ExprP a)
  | LamP (a -> ExprP a)
  | LitP Char
  | EffectP a

data Value
  = VChar Char
  | VFun (Value -> Value)
  | VEffect (IO Value)
  | VUnit

instance Show Value where
  show (VChar x) = show x
  show VUnit     = "()"
  show (VFun _)  = "<<function>>"
  show VEffect{} = "<<effect>>"

newtype Expr = Expr { unExpr :: forall a . ExprP a }

fromVFun :: Value -> (Value -> Value)
fromVFun (VFun f) = f
fromVFun _        = error "not a function"

fromVChar :: Value -> Char
fromVChar (VChar c) = c
fromVChar _         = error "not a char"

fromVEff :: Value -> IO Value
fromVEff (VEffect eff) = eff
fromVEff _             = error "not an effect"

lam :: (Value -> Value) -> Value
lam = VFun

unary :: (Value -> Value) -> Value
unary f = lam $ \a -> f a

binary :: (Value -> Value -> Value) -> Value
binary f = lam $ \a -> lam $ \b -> f a b

prim :: Name -> Value
prim "putChar#" = unary $ \x -> VEffect $ do
  putChar (fromVChar x)
  return VUnit
prim "getChar#" = VEffect $ VChar <$> getChar
prim "bindIO#" = binary $ \x y -> bindIO x y
prim "returnIO#" = unary $ \x -> returnIO x
prim "thenIO#" = binary $ \x y -> thenIO x y

bindIO :: Value -> Value -> Value
bindIO (VEffect f) (VFun g) = VEffect (f >>= fromVEff . g)

thenIO :: Value -> Value -> Value
thenIO (VEffect f) (VEffect g) = VEffect (f >> g)

returnIO :: Value -> Value
returnIO a = VEffect $ return a

eval :: Expr -> Value
eval e = ev (unExpr e) where
  ev (LamP f)     = VFun (ev . f)
  ev (AppP e1 e2) = fromVFun (ev e1) (ev e2)
  ev (LitP c)     = VChar c
  ev (EffectP v)  = v
  ev (VarP v)     = v
  ev (GlobalP op) = prim op

run :: Expr -> IO ()
run f = void (fromVEff (eval f))

gets, puts, bind, seqn :: ExprP a
gets = GlobalP "getChar#"
puts = GlobalP "putChar#"
bind = GlobalP "bindIO#"
seqn = GlobalP "thenIO#"

example1 :: IO ()
example1 = run $ Expr (AppP (AppP bind gets) puts)

example2 :: IO ()
example2 = run $ Expr $ foldr1 seq (str "Hello Haskell!\n")
  where
    seq a = AppP (AppP seqn a)
    str = fmap (AppP puts . LitP)
