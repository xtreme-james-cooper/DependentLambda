module Lambda

import Data.Vect
import Index
import Ty

%default total

public export
data VarArgs : Vect n (Ty tn) -> Vect m (Ty tn) -> Type where
  Nil : VarArgs env []
  (::) : Index env t -> VarArgs env ts -> VarArgs env (t :: ts)

mutual
  public export
  data Expr : Vect n (Ty tn) -> Ty tn -> Type where
    Var : Index env t -> Expr env t
    Num : Int -> Expr env IntTy
    Prim : (Int -> Int -> Int) -> Expr env IntTy -> Expr env IntTy -> Expr env IntTy
    IsZero : Expr env IntTy -> Expr env t -> Expr env t -> Expr env t
    App : Expr env (ArrowTy t1 t2) -> Expr env t1 -> Expr env t2
    Abs : (t1 : Ty tn) -> Expr (t1 :: env) t2 -> Expr env (ArrowTy t1 t2)
    Let : Expr env t1 -> Expr (t1 :: env) t2 -> Expr env t2
    Fix : Expr env (ArrowTy t t) -> Expr env t
    Constr : {ctrs : Vect m (n ** Vect n (Ty tn))} -> (tag : Fin m) ->
        VarArgs env (snd (index tag ctrs)) -> Expr env (DataTy ctrs)
    Case : Expr env (DataTy ctrs) -> Alts env ctrs t -> Expr env t
    TyApp : Expr env (ForallTy t) -> (t' : Ty tn) -> tt = tsubst FZ t' t -> Expr env tt
    TyAbs : Expr (map (tyincr FZ) env) t -> Expr env (ForallTy t)
    Fold : Expr env (tsubst FZ (FixTy t) t) -> Expr env (FixTy t)
    Unfold : Expr env (FixTy t) -> tt = tsubst FZ (FixTy t) t -> Expr env tt

  public export
  data Alts : Vect n (Ty tn) -> Vect m (p ** Vect p (Ty tn)) -> Ty tn -> Type where
    Fail : Alts env [] t
    Alt : Expr (xs ++ env) t -> Alts env ctrs t -> Alts env ((p ** xs) :: ctrs) t

public export
data ValueType : Type where
  PrimValTy : ValueType
  StructValTy : ValueType
  LetValTy : ValueType

public export
data IsValue : Expr env t -> ValueType -> Type where
  IntVal : IsValue (Num x) PrimValTy
  ArrowVal : IsValue (Abs t e) StructValTy
  DataVal : IsValue (Constr tag es) StructValTy
  ForallVal : IsValue (TyAbs e) StructValTy
  FixVal : IsValue (Fold e) StructValTy
  LetVal : IsValue e2 b -> Not (b = PrimValTy) -> IsValue (Let e1 e2) LetValTy

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
