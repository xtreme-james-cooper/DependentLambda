module Named.NamedLambda

import public Type.Ty
import public Utils.FiniteMap

%default total

public export
Name : Type
Name = String

public export
data NVarArgs : FinMap Name (Ty tn) -> Vect m (Ty tn) -> Type where
  Nil : NVarArgs env []
  Cons : (x : Name) -> NVarArgs env ts -> lookup env x = Just t -> NVarArgs env (t :: ts)

mutual
  public export
  data NExpr : FinMap Name (Ty tn) -> Ty tn -> Type where
    Var : (x : Name) -> lookup env x = Just t -> NExpr env t
    Num : Int -> NExpr env IntTy
    Prim : (Int -> Int -> Int) -> NExpr env IntTy -> NExpr env IntTy -> NExpr env IntTy
    IsZero : NExpr env IntTy -> NExpr env t -> NExpr env t -> NExpr env t
    App : NExpr env (ArrowTy t1 t2) -> NExpr env t1 -> NExpr env t2
    Abs : (x : Name) -> (t1 : Ty tn) -> NExpr (extend env x t1) t2 ->
        NExpr env (ArrowTy t1 t2)
    Let : (x : Name) -> NExpr env t1 -> NExpr (extend env x t1) t2 ->
        NExpr env t2
    Fix : NExpr env (ArrowTy t t) -> NExpr env t
    Constr : {ctrs : Vect m (n ** Vect n (Ty tn))} -> (tag : Fin m) ->
        NVarArgs env (snd (index tag ctrs)) -> NExpr env (DataTy ctrs)
    Case : NExpr env (DataTy ctrs) -> NAlts env ctrs t -> NExpr env t
    TyApp : NExpr env (ForallTy t) -> (t' : Ty tn) -> tt = tsubst FZ t' t -> NExpr env tt
    TyAbs : NExpr (fmap (tyincr FZ) env) t -> NExpr env (ForallTy t)
    Fold : NExpr env (tsubst FZ (FixTy t) t) -> NExpr env (FixTy t)
    Unfold : NExpr env (FixTy t) -> tt = tsubst FZ (FixTy t) t -> NExpr env tt

  public export
  data NAlts : FinMap Name (Ty tn) -> Vect m (p ** Vect p (Ty tn)) -> Ty tn -> Type where
    Fail : NAlts env [] t
    Alt : (xs : Vect p Name) -> NExpr (multiExtend env xs ts) t ->
        NAlts env ctrs t -> NAlts env ((p ** ts) :: ctrs) t
