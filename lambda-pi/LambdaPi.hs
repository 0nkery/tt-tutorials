import           Control.Monad

data TermInferable
  = Ann TermCheckable TermCheckable
  | Star
  | Pi TermCheckable TermCheckable
  | Bound Int
  | Free Name
  | TermInferable :@: TermCheckable
  | Nat
  | NatElim TermCheckable TermCheckable TermCheckable TermCheckable
  | Zero
  | Succ TermCheckable
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

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral
  | VNat
  | VZero
  | VSucc Value

data Neutral
  = NFree Name
  | NApp Neutral Value
  | NNatElim Value Value Value Neutral

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

id' = Lam (Inf (Bound 0))
bool' = Inf Star
false' = Inf (Free (Global "False"))
falseTerm = Ann false' bool'

type Env = [Value]

evalInferable :: TermInferable -> Env -> Value
evalInferable (Ann e _) d  = evalCheckable e d
evalInferable Star d       = VStar
evalInferable (Pi t t') d = VPi (evalCheckable t d) (\x -> evalCheckable t' (x : d))
evalInferable (Free x) d   = vfree x
evalInferable (Bound i) d  = d !! i
evalInferable (e :@: e') d = vapp (evalInferable e d) (evalCheckable e' d)
evalInferable Nat d = VNat
evalInferable Zero d = VZero
evalInferable (Succ k) d = VSucc (evalCheckable k d)
evalInferable (NatElim m mz ms k) d =
  let
    mzVal = evalCheckable mz d
    msVal = evalCheckable ms d
    rec kVal =
      case kVal of
        VZero      -> mzVal
        VSucc l    -> msVal `vapp` l `vapp` rec l
        VNeutral k -> VNeutral (NNatElim (evalCheckable m d) mzVal msVal k)
        _          -> error "internal: eval natElim"
  in rec (evalCheckable k d)

vapp :: Value -> Value -> Value
vapp (VLam f) v     = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalCheckable :: TermCheckable -> Env -> Value
evalCheckable (Inf i) d = evalInferable i d
evalCheckable (Lam e) d = VLam (\x -> evalCheckable e (x : d))

type Type = Value
type Context = [(Name, Type)]

type Result a = Either String a

throwError :: String -> Result a
throwError = Left

typeInferableZero :: Context -> TermInferable -> Result Type
typeInferableZero = typeInferable 0

typeInferable :: Int -> Context -> TermInferable -> Result Type
typeInferable i gamma (Ann e p) = do
  typeCheckable i gamma p VStar
  let t = evalCheckable p []
  typeCheckable i gamma e t
  return t
typeInferable i gamma Star = return VStar
typeInferable i gamma (Pi p p') = do
  typeCheckable i gamma p VStar
  let t = evalCheckable p []
  typeCheckable (i + 1) ((Local i, t) : gamma) (substCheckable 0 (Free (Local i)) p') VStar
  return VStar
typeInferable i gamma (Free x) = case lookup x gamma of
  Just t  -> return t
  Nothing -> throwError "unknown identifier"
typeInferable i gamma (e :@: e') = do
  sigma <- typeInferable i gamma e
  case sigma of
    VPi t t' -> do
      typeCheckable i gamma e' t
      return (t' (evalCheckable e' []))
    _ -> throwError "illegal application"
typeInferable i gamma Nat = return VStar
typeInferable i gamma Zero = return VNat
typeInferable i gamma (Succ k) =
  do
    typeCheckable i gamma k VNat
    return VNat
typeInferable i gamma (NatElim m mz ms k) =
  do
    typeCheckable i gamma m (VPi VNat (const VStar))
    let mVal = evalCheckable m []
    typeCheckable i gamma mz (mVal `vapp` VZero)
    typeCheckable i gamma ms (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
    typeCheckable i gamma k VNat
    let kVal = evalCheckable k []
    return (mVal `vapp` kVal)

typeCheckable :: Int -> Context -> TermCheckable -> Type -> Result ()
typeCheckable i gamma (Inf e) v = do
  v' <- typeInferable i gamma e
  unless (quote0 v == quote0 v') (throwError "type mismatch")
typeCheckable i gamma (Lam e) (VPi t t') =
  typeCheckable (i + 1) ((Local i, t) : gamma) (substCheckable 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeCheckable i gamma _ _ = throwError "type mismatch"

substInferable :: Int -> TermInferable -> TermInferable -> TermInferable
substInferable i r (Ann e t)  = Ann (substCheckable i r e) t
substInferable i r Star       = Star
substInferable i r (Pi t t') = Pi (substCheckable i r t) (substCheckable (i + 1) r t')
substInferable i r (Bound j)  = if i == j then r else Bound j
substInferable i r (Free y)   = Free y
substInferable i r (e :@: e') = substInferable i r e :@: substCheckable i r e'

substCheckable :: Int -> TermInferable -> TermCheckable -> TermCheckable
substCheckable i r (Inf e) = Inf (substInferable i r e)
substCheckable i r (Lam e) = Lam (substCheckable (i + 1) r e)

quote0 :: Value -> TermCheckable
quote0 = quote 0

quote :: Int -> Value -> TermCheckable
quote i (VLam f)     = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i VStar        = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermInferable
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermInferable
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x
