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
    App : Expr env (ArrowTy t1 t2) -> Expr env t1 -> Expr env t2
    Abs : (t1 : Ty tn) -> Expr (t1 :: env) t2 -> Expr env (ArrowTy t1 t2)
    Let : Expr env t1 -> Expr (t1 :: env) t2 -> Expr env t2
    Fix : Expr env (ArrowTy t t) -> Expr env t
    Constr : {ctrs : Vect m (n ** Vect n (Ty tn))} -> (tag : Fin m) ->
        VarArgs env (snd (index tag ctrs)) -> Expr env (DataTy ctrs)
    Case : Expr env (DataTy ctrs) -> Alts env ctrs t -> Expr env t
    TyApp : Expr env (ForallTy t) -> (t' : Ty tn) -> tt = tsubst FZ t' t -> Expr env tt
    TyAbs : Expr (map (tyincr FZ) env) t -> Expr env (ForallTy t)

  public export
  data Alts : Vect n (Ty tn) -> Vect m (p ** Vect p (Ty tn)) -> Ty tn -> Type where
    Fail : Alts env [] t
    Alt : Expr (xs ++ env) t -> Alts env ctrs t -> Alts env ((p ** xs) :: ctrs) t

public export
data IsValue : Expr env t -> Bool -> Type where
  IntVal : IsValue (Num x) True
  ArrowVal : IsValue (Abs t e) True
  DataVal : IsValue (Constr tag es) True
  ForallVal : IsValue (TyAbs e) True
  LetVal : IsValue e2 b -> IsValue (Let e1 e2) False

public export
data IsVarHeaded : Expr env t -> Index env t' -> Type where
  VarVar : IsVarHeaded (Var ix) ix
  PrimVarL : IsVarHeaded e1 ix -> IsVarHeaded (Prim f e1 e2) ix
  PrimVarR : IsValue e1 b -> IsVarHeaded e2 ix -> IsVarHeaded (Prim f e1 e2) ix
  AppVar : IsVarHeaded e1 ix -> IsVarHeaded (App e1 e2) ix
  LetVarL : IsVarHeaded e2 (IxZ t1 env) -> IsVarHeaded e1 ix -> IsVarHeaded (Let e1 e2) ix
  LetVarR : IsVarHeaded e2 (IxS b ix) -> IsVarHeaded (Let e1 e2) ix
  FixVar : IsVarHeaded e ix -> IsVarHeaded (Fix e) ix
  CaseVar : IsVarHeaded e ix -> IsVarHeaded (Case e as) ix
  TyAppVar : IsVarHeaded e ix -> IsVarHeaded (TyApp e t eq) ix
