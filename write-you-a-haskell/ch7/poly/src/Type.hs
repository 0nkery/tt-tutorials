module Type where

import           Syntax (Loc (..), Name)

newtype TVar = TV String
  deriving (Show, Eq, Ord)

data Type
  = TVar Loc TVar
  | TCon Loc Name
  | TArr Loc Type Type
  deriving (Show, Eq, Ord)

infixr `TArr`

setLoc :: Loc -> Type -> Type
setLoc l (TVar _ a)   = TVar l a
setLoc l (TCon _ a)   = TCon l a
setLoc l (TArr _ a b) = TArr l a b

getLoc :: Type -> Loc
getLoc (TVar l _)   = l
getLoc (TCon l _)   = l
getLoc (TArr l _ _) = l

typeInt, typeBool :: Type
typeInt = TCon NoLoc "Int"
typeBool = TCon NoLoc "Bool"

data Scheme = Forall [TVar] Type
  deriving (Show, Eq, Ord)
