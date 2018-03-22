module Lambda

import Data.Vect
import Index
import VectHelper

%default total

public export
data Ty : Type where
  ArrowTy : Ty -> Ty -> Ty
  IntTy : Ty
  DataTy : Vect m (n ** Vect n Ty) -> Ty

mutual
  public export
  data Expr : Vect n Ty -> Ty -> Type where
    Var : Index env t -> Expr env t
    Num : Int -> Expr env IntTy
    App : Expr env (ArrowTy t1 t2) -> Expr env t1 -> Expr env t2
    Abs : (t1 : Ty) -> Expr (t1 :: env) t2 -> Expr env (ArrowTy t1 t2)
    Let : Expr env t1 -> Expr (t1 :: env) t2 -> Expr env t2
    Letrec : {n : Nat} -> (ts : Vect n Ty) -> Exprs (ts ++ env) ts ->
        Expr (ts ++ env) t -> Expr env t
    Constr : {ctrs : Vect m (n ** Vect n Ty)} -> (tag : Fin m) ->
        Exprs env (snd (index tag ctrs)) -> Expr env (DataTy ctrs)
    Case : Expr env (DataTy ctrs) -> Alts env ctrs t -> Expr env t

  public export
  data Exprs : Vect n Ty -> Vect m Ty -> Type where
    Nil : Exprs env []
    (::) : Expr env t -> Exprs env ts -> Exprs env (t :: ts)

  public export
  data Alts : Vect n Ty -> Vect m (p ** Vect p Ty) -> Ty -> Type where
    Fail : Alts env [] t
    Alt : Expr (xs ++ env) t -> Alts env ctrs t -> Alts env ((p ** xs) :: ctrs) t

mutual
  export
  incr : (x : Fin (S n)) -> (tt : Ty) -> Expr env t -> Expr (insertAt x tt env) t
  incr x tt (Var ix) = Var (indexInsert tt x ix)
  incr x tt (Num n) = Num n
  incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
  incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)
  incr x tt (Let e1 e2) = Let (incr x tt e1) (incr (FS x) tt e2)
  incr x tt (Letrec {n = n} {t = t} ts es e) {env = env} = ?dontCommit
      --let es' : Exprs (ts ++ insertAt x tt env) ts =
      --      rewrite appendInsert ts env x tt in incrs (extendFin n x) tt es
      --    e' : Expr (ts ++ insertAt x tt env) t =
      --      rewrite appendInsert ts env x tt in incr (extendFin n x) tt e
      --in Letrec ts es' e'
  incr x tt (Constr tag es) = Constr tag (incrs x tt es)
  incr x tt (Case e as) = Case (incr x tt e) (incra x tt as)

  incrs : (x : Fin (S n)) -> (tt : Ty) -> Exprs env ts -> Exprs (insertAt x tt env) ts
  incrs x tt [] = []
  incrs x tt (e :: es) = incr x tt e :: incrs x tt es

  export
  incra : (x : Fin (S n)) -> (tt : Ty) -> Alts env ctrs ts -> Alts (insertAt x tt env) ctrs ts
  incra x tt Fail = Fail
  incra {env = env} {ctrs = (p ** xs) :: ctrs} x tt (Alt e as) = ?dontCommit3
      --let e' : Expr (xs ++ insertAt x tt env) ts =
      --    rewrite appendInsert xs env x tt in incr (extendFin p x) tt e
      --in Alt e' (incra x tt as)

export
multiincr : Expr env t -> Expr (ts ++ env) t
multiincr {ts = []} e = e
multiincr {ts = t :: ts} e = incr FZ t (multiincr e)

mutual
  export
  subst : (x : Fin (S n)) -> Expr env t' -> Expr (insertAt x t' env) t -> Expr env t
  subst x e' (Var ix) {t' = t'} {env = env} with (compareFinToIndex x ix)
    subst x e' (Var ix) {t' = t'} {env = env} | Yes eq with (indexOfIndex x ix eq)
      subst x e' (Var ix) {t' = t'} {env = env} | Yes eq | Refl =
          rewrite indexInsertAt x t' env in e'
    subst x e' (Var ix) {t' = t'} {env = env} | No npf = Var (indexSubr _ x ix npf)
  subst x e' (Num n) = Num n
  subst x e' (App e1 e2) = App (subst x e' e1) (subst x e' e2)
  subst x e' (Abs t1 e) = Abs t1 (subst (FS x) (incr FZ t1 e') e)
  subst x e' (Let e1 e2) = Let (subst x e' e1) (subst (FS x) (incr FZ _ e') e2)
  subst x e' (Letrec {n = n} {t = t} ts es e) {env = env} {t' = t'} = ?dontCommit2
      --let es' : Exprs (insertAt (extendFin n x) t' (ts ++ env)) ts =
      --      rewrite sym (appendInsert ts env x t') in es
      --    e1' : Expr (insertAt (extendFin n x) t' (ts ++ env)) t =
      --      rewrite sym (appendInsert ts env x t') in e
      --in Letrec ts (substs (extendFin n x) (multiincr e') es')
      --             (subst (extendFin n x) (multiincr e') e1')
  subst x e' (Constr tag es) = Constr tag (substs x e' es)
  subst x e' (Case e as) = Case (subst x e' e) (substa x e' as)

  substs : (x : Fin (S n)) -> Expr env t' -> Exprs (insertAt x t' env) ts -> Exprs env ts
  substs x e' [] = []
  substs x e' (e :: es) = subst x e' e :: substs x e' es

  substa : (x : Fin (S n)) -> Expr env t' -> Alts (insertAt x t' env) ctrs ts -> Alts env ctrs ts
  substa x e' Fail = Fail
  substa {t' = t'} {env = env} {ctrs = (p ** xs) :: ctrs} x e' (Alt e as) = ?dontCommit4
      --let ep : Expr (insertAt (extendFin p x) t' (xs ++ env)) ts =
      --    rewrite sym (appendInsert xs env x t') in e
      --in Alt (subst (extendFin p x) (multiincr e') ep) (substa x e' as)

export
multisubst : Exprs env ts -> Expr (ts ++ env) t -> Expr env t
multisubst [] e = e
multisubst (e' :: es) e = multisubst es (subst FZ (multiincr e') e)
