module Lambda.Lambda

import public Utils.Index
import public Type.Ty

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
