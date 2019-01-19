import           Control.Monad

data TermInferable
  = Ann TermCheckable Type
  | Bound Int
  | Free Name
  | TermInferable :@: TermCheckable
  deriving (Show, Eq)

data TermCheckable
  = Inf TermInferable
  | Lam TermCheckable
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | Fun Type Type
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

type Env = [Value]

evalInferable :: TermInferable -> Env -> Value
evalInferable (Ann e _) d  = evalCheckable e d
evalInferable (Free x) d   = vfree x
evalInferable (Bound i) d  = d !! i
evalInferable (e :@: e') d = vapp (evalInferable e d) (evalCheckable e' d)

vapp :: Value -> Value -> Value
vapp (VLam f) v     = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalCheckable :: TermCheckable -> Env -> Value
evalCheckable (Inf i) d = evalInferable i d
evalCheckable (Lam e) d = VLam (\x -> evalCheckable e (x : d))

data Kind = Star
  deriving Show

data Info
  = HasKind Kind
  | HasType Type
  deriving Show

type Context = [(Name, Info)]

type Result a = Either String a

throwError :: String -> Result a
throwError = Left

kindCheckable :: Context -> Type -> Kind -> Result ()
kindCheckable gamma (TFree x) Star = case lookup x gamma of
  Just (HasKind Star) -> return ()
  Nothing             -> throwError "unknown identifier"
kindCheckable gamma (Fun k k') Star = do
  kindCheckable gamma k Star
  kindCheckable gamma k' Star

typeInferableZero :: Context -> TermInferable -> Result Type
typeInferableZero = typeInferable 0

typeInferable :: Int -> Context -> TermInferable -> Result Type
typeInferable i gamma (Ann e t) = do
  kindCheckable gamma t Star
  typeCheckable i gamma e t
  return t
typeInferable i gamma (Free x) = case lookup x gamma of
  Just (HasType t) -> return t
  Nothing          -> throwError "unknown identifier"
typeInferable i gamma (e :@: e') = do
  sigma <- typeInferable i gamma e
  case sigma of
    Fun t t' -> do
      typeCheckable i gamma e' t
      return t'
    _ -> throwError "illegal application"

typeCheckable :: Int -> Context -> TermCheckable -> Type -> Result ()
typeCheckable i gamma (Inf e) t = do
  t' <- typeInferable i gamma e
  unless (t == t') (throwError "type mismatch")
typeCheckable i gamma (Lam e) (Fun t t') =
  typeCheckable (i + 1) ((Local i, HasType t) : gamma) (substCheckable 0 (Free (Local i)) e) t'
typeCheckable i gamma _ _ = throwError "type mismatch"

substInferable :: Int -> TermInferable -> TermInferable -> TermInferable
substInferable i r (Ann e t)  = Ann (substCheckable i r e) t
substInferable i r (Bound j)  = if i == j then r else Bound j
substInferable i r (Free y)   = Free y
substInferable i r (e :@: e') = substInferable i r e :@: substCheckable i r e'

substCheckable :: Int -> TermInferable -> TermCheckable -> TermCheckable
substCheckable i r (Inf e) = Inf (substInferable i r e)
substCheckable i r (Lam e) = Lam (substCheckable (i + 1) r e)

quoteZero :: Value -> TermCheckable
quoteZero = quote 0

quote :: Int -> Value -> TermCheckable
quote i (VLam f)     = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermInferable
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermInferable
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x

id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 0)))

tfree a = TFree (Global a)
free x = Inf (Free (Global x))

term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"
term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                        (Fun (tfree "a")
                             (Fun (tfree "b") (tfree "b"))))
        :@: id' :@: free "y"

env1 = [
    (Global "y", HasType (tfree "a")),
    (Global "a", HasKind Star)
  ]
env2 = (Global "b", HasKind Star) : env1
