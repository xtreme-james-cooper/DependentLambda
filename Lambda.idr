module Lambda

import Data.Vect
import Index

%default total

public export
data Ty : Type where
  ArrowTy : Ty -> Ty -> Ty
  IntTy : Ty
  DataTy : Vect m (n ** Vect n Ty) -> Ty

public export
data VarArgs : Vect n Ty -> Vect m Ty -> Type where
  Nil : VarArgs env []
  (::) : Index env t -> VarArgs env ts -> VarArgs env (t :: ts)

mutual
  public export
  data Expr : Vect n Ty -> Ty -> Type where
    Var : Index env t -> Expr env t
    Num : Int -> Expr env IntTy
    App : Expr env (ArrowTy t1 t2) -> Expr env t1 -> Expr env t2
    Abs : (t1 : Ty) -> Expr (t1 :: env) t2 -> Expr env (ArrowTy t1 t2)
    Let : Expr env t1 -> Expr (t1 :: env) t2 -> Expr env t2
    Fix : Expr env (ArrowTy t t) -> Expr env t
    Constr : {ctrs : Vect m (n ** Vect n Ty)} -> (tag : Fin m) ->
        VarArgs env (snd (index tag ctrs)) -> Expr env (DataTy ctrs)
    Case : Expr env (DataTy ctrs) -> Alts env ctrs t -> Expr env t

  public export
  data Alts : Vect n Ty -> Vect m (p ** Vect p Ty) -> Ty -> Type where
    Fail : Alts env [] t
    Alt : Expr (xs ++ env) t -> Alts env ctrs t -> Alts env ((p ** xs) :: ctrs) t

public export
data IsValue : Expr env t -> Type where
  IntVal : IsValue (Num x)
  ArrowVal : IsValue (Abs t e)
  DataVal : IsValue (Constr tag es)
  LetVal : IsValue e2 -> IsValue (Let e1 e2)

public export
data IsVarHeaded : Expr env t -> Index env t' -> Type where
  VarVar : IsVarHeaded (Var ix) ix
  AppVar : IsVarHeaded e1 ix -> IsVarHeaded (App e1 e2) ix
  LetVarL : IsVarHeaded e2 (IxZ t1 env) -> IsVarHeaded e1 ix -> IsVarHeaded (Let e1 e2) ix
  LetVarR : IsVarHeaded e2 (IxS b ix) -> IsVarHeaded (Let e1 e2) ix
  FixVar : IsVarHeaded e ix -> IsVarHeaded (Fix e) ix
  CaseVar : IsVarHeaded e ix -> IsVarHeaded (Case e as) ix
