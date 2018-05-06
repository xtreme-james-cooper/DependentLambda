module Values

import BooleanHelper
import Data.Vect
import Index
import Ty
import Lambda

%default total

public export
freeVar : {env : Vect n (Ty tn)} -> Index env t -> Vect n Bool
freeVar (IxZ t as) = True :: replicate _ False
freeVar (IxS b ix) = False :: freeVar ix

public export
freeVarsXs : {env : Vect n (Ty tn)} -> VarArgs env ts -> Vect n Bool
freeVarsXs [] = replicate _ False
freeVarsXs (x :: xs) = zipWith or (freeVar x) (freeVarsXs xs)

mutual
  public export
  freeVars : {env : Vect n (Ty tn)} -> Expr env t -> Vect n Bool
  freeVars (Var ix) = freeVar ix
  freeVars (Num n) = replicate _ False
  freeVars (Prim f e1 e2) = zipWith or (freeVars e1) (freeVars e2)
  freeVars (IsZero e1 e2 e3) =
      zipWith or (freeVars e1) (zipWith or (freeVars e2) (freeVars e3))
  freeVars (App e1 e2) = zipWith or (freeVars e1) (freeVars e2)
  freeVars (Abs t1 e) = tail (freeVars e)
  freeVars (Let e1 e2) = zipWith or (freeVars e1) (tail (freeVars e2))
  freeVars (Fix e) = freeVars e
  freeVars (Constr tag xs) = freeVarsXs xs
  freeVars (Case e as) = zipWith or (freeVars e) (freeVarsAs as)
  freeVars (TyApp e t' eq) = freeVars e
  freeVars (TyAbs e) = freeVars e
  freeVars (Fold e) = freeVars e
  freeVars (Unfold e eq) = freeVars e

  public export
  freeVarsAs : {env : Vect n (Ty tn)} -> Alts env ctrs t -> Vect n Bool
  freeVarsAs Fail = replicate _ False
  freeVarsAs (Alt e as) = zipWith or (drop _ (freeVars e)) (freeVarsAs as)

public export
data IsValue : {env : Vect n (Ty tn)} -> Expr env t -> Vect n Bool -> Type where
  IntVal : IsValue (Num n) (replicate _ False)
  ArrowVal : IsValue (Abs t e) (tail (freeVars e))
  DataVal : IsValue (Constr tag es) (freeVarsXs es)
  ForallVal : IsValue (TyAbs e) (freeVars e)
  FixVal : IsValue (Fold e) (freeVars e)
  LetVal : IsValue e2 fv -> index FZ fv = True ->
      IsValue (Let e1 e2) (zipWith or (freeVars e1) (tail (freeVars e2)))

public export
data IsVarHeaded : Expr env t -> Index env t' -> Type where
  VarVar : IsVarHeaded (Var ix) ix
  PrimVarL : IsVarHeaded e1 ix -> IsVarHeaded (Prim f e1 e2) ix
  PrimVarR : IsVarHeaded e2 ix -> IsVarHeaded (Prim f (Num n) e2) ix
  IsZeroVar : IsVarHeaded e1 ix -> IsVarHeaded (IsZero e1 e2 e3) ix
  AppVar : IsVarHeaded e1 ix -> IsVarHeaded (App e1 e2) ix
  LetVarL : IsVarHeaded e2 (IxZ t1 env) -> IsVarHeaded e1 ix -> IsVarHeaded (Let e1 e2) ix
  LetVarR : IsVarHeaded e2 (IxS b ix) -> IsVarHeaded (Let e1 e2) ix
  FixVar : IsVarHeaded e ix -> IsVarHeaded (Fix e) ix
  CaseVar : IsVarHeaded e ix -> IsVarHeaded (Case e as) ix
  TyAppVar : IsVarHeaded e ix -> IsVarHeaded (TyApp e t eq) ix
  UnfoldVar : IsVarHeaded e ix -> IsVarHeaded (Unfold e eq) ix
