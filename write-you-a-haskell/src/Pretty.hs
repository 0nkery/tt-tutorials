{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Pretty (ppexpr, pptype) where

import           Text.PrettyPrint

import           Syntax

class Pretty p where
  ppr :: Int -> p -> Doc

  pp :: p -> Doc
  pp = ppr 0

parensIf ::  Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

instance Pretty Name where
  ppr _ = text

instance Pretty Expr where
  ppr _ (Var x)         = text x
  ppr _ (Lit (LInt a))  = text (show a)
  ppr _ (Lit (LBool a)) = text (show a)
  ppr p (App a b) = parensIf (p > 0) (ppr (p + 1) a) <+> ppr p b
  ppr p (Lam x t a) = parensIf (p > 0) $
        char '\\'
    <+> parens (text x <+> char ':' <+> ppr p t)
    <+> text "->"
    <+> ppr (p + 1) a

ppexpr :: Expr -> String
ppexpr = render . ppr 0

instance Pretty Type where
  ppr _ TInt       = text "Int"
  ppr _ TBool      = text "Bool"
  ppr p (TArr a b) = parensIf (isArrow a) (ppr p a) <+> text "->" <+> ppr p b
    where
      isArrow TArr{} = True
      isArrow _      = False

pptype :: Type -> String
pptype = render . ppr 0
