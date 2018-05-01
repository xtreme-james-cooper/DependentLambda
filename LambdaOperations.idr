module LambdaOperations

import Data.Vect
import Lambda
import VectHelper
import FinHelper
import Index
import Ty
import TyLemmas

%default total

export
incrvs : (x : Fin (S n)) -> (tt : Ty tn) -> VarArgs env ts ->
    VarArgs (insertAt x tt env) ts
incrvs x tt [] = []
incrvs x tt (ix :: ixs) = indexInsert tt x ix :: incrvs x tt ixs

mutual
  export
  incr : (x : Fin (S n)) -> (tt : Ty tn) -> Expr env t -> Expr (insertAt x tt env) t
  incr x tt (Var ix) = Var (indexInsert tt x ix)
  incr x tt (Num n) = Num n
  incr x tt (Prim f e1 e2) = Prim f (incr x tt e1) (incr x tt e2)
  incr x tt (IsZero e1 e2 e3) = IsZero (incr x tt e1) (incr x tt e2) (incr x tt e3)
  incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
  incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)
  incr x tt (Let e1 e2) = Let (incr x tt e1) (incr (FS x) tt e2)
  incr x tt (Fix e) = Fix (incr x tt e)
  incr x tt (Constr tag es) = Constr tag (incrvs x tt es)
  incr x tt (Case e as) = Case (incr x tt e) (incra x tt as)
  incr x tt (TyApp e t' eq) = TyApp (incr x tt e) t' eq
  incr x tt (TyAbs e) {env = env} =
      TyAbs (rewrite insertAtMap (tyincr FZ) x tt env in incr x (tyincr FZ tt) e)
  incr x tt (Fold e) = Fold (incr x tt e)
  incr x tt (Unfold e eq) = Unfold (incr x tt e) eq

  export
  incra : (x : Fin (S n)) -> (tt : Ty tn) -> Alts env ctrs ts -> Alts (insertAt x tt env) ctrs ts
  incra x tt Fail = Fail
  incra {env = env} {ctrs = (p ** xs) :: ctrs} x tt (Alt e as) =
      let e' : Expr (xs ++ insertAt x tt env) ts =
            rewrite appendInsert xs env x tt in incr (extendFin p x) tt e
      in Alt e' (incra x tt as)

export
multiincr : Expr env t -> Expr (ts ++ env) t
multiincr {ts = []} e = e
multiincr {ts = t :: ts} e = incr FZ t (multiincr e)

export
multiincra : Alts env ctrs ts -> Alts (ts' ++ env) ctrs ts
multiincra {ts' = []} as = as
multiincra {ts' = t :: ts'} as = incra FZ t (multiincra as)

export
subst : {ix : Index env t'} -> (e' : Expr env t') -> (e : Expr env t) ->
    IsVarHeaded e ix -> Expr env t
subst e' (Var ix) VarVar = e'
subst e' (Prim f e1 e2) (PrimVarL vh) = Prim f (subst e' e1 vh) e2
subst e' (Prim f (Num n) e2) (PrimVarR vh) = Prim f (Num n) (subst e' e2 vh)
subst e' (IsZero e1 e2 e3) (IsZeroVar vh) = IsZero (subst e' e1 vh) e2 e3
subst e' (App e1 e2) (AppVar vh) = App (subst e' e1 vh) e2
subst e' (Let e1 e2) (LetVarL vh2 vh1) = Let (subst e' e1 vh1) e2
subst e' (Let e1 e2) (LetVarR vh2) = Let e1 (subst (incr FZ _ e') e2 vh2)
subst e' (Fix e) (FixVar vh) = Fix (subst e' e vh)
subst e' (Case e as) (CaseVar vh) = Case (subst e' e vh) as
subst e' (TyApp e t eq) (TyAppVar vh) = TyApp (subst e' e vh) t eq
subst e' (Unfold e eq) (UnfoldVar vh) = Unfold (subst e' e vh) eq

varsSubst : (x : Fin (S n)) -> Index env t' -> VarArgs (insertAt x t' env) ts -> VarArgs env ts
varsSubst x ix' [] = []
varsSubst x ix' (ix :: ixs) = indexSubst x ix' ix :: varsSubst x ix' ixs

mutual
  varSubst : (x : Fin (S n)) -> Index env t' -> Expr (insertAt x t' env) t -> Expr env t
  varSubst x ix' (Var ix) = Var (indexSubst x ix' ix)
  varSubst x ix' (Num n) = Num n
  varSubst x ix' (Prim f e1 e2) = Prim f (varSubst x ix' e1) (varSubst x ix' e2)
  varSubst x ix' (IsZero e1 e2 e3) =
      IsZero (varSubst x ix' e1) (varSubst x ix' e2) (varSubst x ix' e3)
  varSubst x ix' (App e1 e2) = App (varSubst x ix' e1) (varSubst x ix' e2)
  varSubst x ix' (Abs t1 e) = Abs t1 (varSubst (FS x) (IxS _ ix') e)
  varSubst x ix' (Let e1 e2) = Let (varSubst x ix' e1) (varSubst (FS x) (IxS _ ix') e2)
  varSubst x ix' (Fix e) = Fix (varSubst x ix' e)
  varSubst x ix' (Constr tag es) = Constr tag (varsSubst x ix' es)
  varSubst x ix' (Case e as) = Case (varSubst x ix' e) (varSubsta x ix' as)
  varSubst x ix' (TyApp e t eq) = TyApp (varSubst x ix' e) t eq
  varSubst x ix' (TyAbs e) {t' = t'} {env = env} {t = ForallTy t} =
      let ep : Expr (insertAt x (tyincr FZ t') (map (tyincr FZ) env)) t =
          rewrite sym (insertAtMap (tyincr FZ) x t' env) in e
      in let small_ep : Expr (insertAt x (tyincr FZ t') (map (tyincr FZ) env)) t =
          assert_smaller (TyAbs e) ep
      in TyAbs (varSubst x (indexMap (tyincr FZ) ix') small_ep)
  varSubst x ix' (Fold e) = Fold (varSubst x ix' e)
  varSubst x ix' (Unfold e eq) = Unfold (varSubst x ix' e) eq

  varSubsta : (x : Fin (S n)) -> Index env t' -> Alts (insertAt x t' env) ctrs t -> Alts env ctrs t
  varSubsta x ix' Fail = Fail
  varSubsta {t' = t'} {env = env} {ctrs = (p ** xs) :: ctrs} x ix' (Alt e as) =
      let ep : Expr (insertAt (extendFin p x) t' (xs ++ env)) t =
          rewrite sym (appendInsert xs env x t') in e
      in let small_ep : Expr (insertAt (extendFin p x) t' (xs ++ env)) t =
          assert_smaller (Alt e as) ep
      in Alt (varSubst (extendFin p x) (indexLeftExtend xs ix') small_ep)
             (varSubsta x ix' as)

export
multisubst : VarArgs env ts -> Expr (ts ++ env) t -> Expr env t
multisubst [] e = e
multisubst {ts = t :: ts} (ix :: ixs) e =
    multisubst ixs (varSubst FZ (indexLeftExtend ts ix) e)

export
altEval : (x : Fin n) -> Alts env ctrs t -> VarArgs env (snd (index x ctrs)) -> Expr env t
altEval FZ (Alt e as) es = multisubst es e
altEval (FS x) (Alt e as) es = altEval x as es

tyVarsSubst : (x : Fin (S tn)) -> (t' : Ty tn) -> VarArgs env ctr ->
    VarArgs (map (tsubst x t') env) (ctrsubst x t' ctr)
tyVarsSubst x t' [] = []
tyVarsSubst x t' (v :: vs) = indexMap (tsubst x t') v :: tyVarsSubst x t' vs

mutual
  tySubst' : (x : Fin (S tn)) -> (t' : Ty tn) -> Expr env t ->
      Expr (map (tsubst x t') env) (tsubst x t' t)
  tySubst' x t' (Var ix) = Var (indexMap (tsubst x t') ix)
  tySubst' x t' (Num n) = Num n
  tySubst' x t' (Prim f e1 e2) = Prim f (tySubst' x t' e1) (tySubst' x t' e2)
  tySubst' x t' (IsZero e1 e2 e3) =
      IsZero (tySubst' x t' e1) (tySubst' x t' e2) (tySubst' x t' e3)
  tySubst' x t' (App e1 e2) = App (tySubst' x t' e1) (tySubst' x t' e2)
  tySubst' x t' (Abs t1 e) = Abs (tsubst x t' t1) (tySubst' x t' e)
  tySubst' x t' (Let e1 e2) = Let (tySubst' x t' e1) (tySubst' x t' e2)
  tySubst' x t' (Fix e) = Fix (tySubst' x t' e)
  tySubst' x t' (Constr {ctrs = ctrs} tag es) =
      Constr tag (rewrite ctrSubstSnd x t' tag ctrs in tyVarsSubst x t' es)
  tySubst' x t' (Case e as) = Case (tySubst' x t' e) (tySubsta' x t' as)
  tySubst' x t' (TyApp {t = tt} e t Refl) =
      TyApp (tySubst' x t' e) (tsubst x t' t) (sym (tsubstTsubst x FZ t' t tt ZLeX))
  tySubst' x t' (TyAbs e) {env = env} =
      TyAbs (rewrite sym (tsubstTincrList x t' env) in tySubst' (FS x) (tyincr FZ t') e)
  tySubst' x t' (Fold {t = tt} e) =
      Fold (rewrite tsubstTsubst x FZ t' (FixTy tt) tt ZLeX in tySubst' x t' e)
  tySubst' x t' (Unfold {t = tt} e Refl) =
      Unfold (tySubst' x t' e) (sym (tsubstTsubst x FZ t' (FixTy tt) tt ZLeX))

  tySubsta' : (x : Fin (S tn)) -> (t' : Ty tn) -> Alts env ctrs t ->
      Alts (map (tsubst x t') env) (ctrssubst x t' ctrs) (tsubst x t' t)
  tySubsta' x t' Fail = Fail
  tySubsta' x t' (Alt {xs = xs} e as) {env = env} {t = t} =
      let ep : Expr (ctrsubst x t' xs ++ map (tsubst x t') env) (tsubst x t' t) =
          rewrite ctrsubstMap x t' xs in rewrite mapAppend (tsubst x t') xs env
          in tySubst' x t' e
      in Alt ep (tySubsta' x t' as)

export
tySubst : (t' : Ty tn) -> Expr (map (tyincr FZ) env) t -> Expr env (tsubst FZ t' t)
tySubst t' e {env = env} =
    rewrite sym (tsubstIncrSameList FZ t' env) in tySubst' FZ t' e
