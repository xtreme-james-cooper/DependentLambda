module LambdaOperations

import Data.Vect
import Lambda
import VectHelper
import Index

mutual
  export
  incr : (x : Fin (S n)) -> (tt : Ty) -> Expr env t -> Expr (insertAt x tt env) t
  incr x tt (Var ix) = Var (indexInsert tt x ix)
  incr x tt (Num n) = Num n
  incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
  incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)
  incr x tt (Let e1 e2) = Let (incr x tt e1) (incr (FS x) tt e2)
  incr x tt (Fix e) = Fix (incr x tt e)
  incr x tt (Constr tag es) = Constr tag (incrs x tt es)
  incr x tt (Case e as) = Case (incr x tt e) (incra x tt as)

  export
  incrs : (x : Fin (S n)) -> (tt : Ty) -> Exprs env ts -> Exprs (insertAt x tt env) ts
  incrs x tt [] = []
  incrs x tt (e :: es) = incr x tt e :: incrs x tt es

  export
  incra : (x : Fin (S n)) -> (tt : Ty) -> Alts env ctrs ts -> Alts (insertAt x tt env) ctrs ts
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
  subst x e' (Fix e) = Fix (subst x e' e)
  subst x e' (Constr tag es) = Constr tag (substs x e' es)
  subst x e' (Case e as) = Case (subst x e' e) (substa x e' as)

  substs : (x : Fin (S n)) -> Expr env t' -> Exprs (insertAt x t' env) ts -> Exprs env ts
  substs x e' [] = []
  substs x e' (e :: es) = subst x e' e :: substs x e' es

  substa : (x : Fin (S n)) -> Expr env t' -> Alts (insertAt x t' env) ctrs ts -> Alts env ctrs ts
  substa x e' Fail = Fail
  substa {t' = t'} {env = env} {ctrs = (p ** xs) :: ctrs} x e' (Alt e as) =
      let ep : Expr (insertAt (extendFin p x) t' (xs ++ env)) ts =
            rewrite sym (appendInsert xs env x t') in e
      in let small_ep : Expr (insertAt (extendFin p x) t' (xs ++ env)) ts =
            assert_smaller (Alt e as) ep
      in Alt (subst (extendFin p x) (multiincr e') small_ep) (substa x e' as)

export
multisubst : Exprs env ts -> Expr (ts ++ env) t -> Expr env t
multisubst [] e = e
multisubst (e' :: es) e = multisubst es (subst FZ (multiincr e') e)

export
altEval : (x : Fin n) -> Alts env ctrs t -> Exprs env (snd (index x ctrs)) -> Expr env t
altEval FZ (Alt e as) es = multisubst es e
altEval (FS x) (Alt e as) es = altEval x as es

anfCtor : (ctr : Vect p Ty) -> (es : Exprs env ctr) ->
    ({t : Ty} -> Expr (ctr ++ env) t -> Expr env t, Exprs (ctr ++ env) ctr)
anfCtor [] [] = (id, [])
anfCtor (t :: ts) (e :: es) = case anfCtor ts es of
    (letf, ctrArgs) =>
        (\e' => letf (Let (multiincr e) e'), (Var (IxZ t _)) :: incrs FZ t ctrArgs)

export
sharingSubst : {e' : Expr env t'} -> (x : Fin (S n)) -> IsValue e' ->
    Expr (insertAt x t' env) t -> Expr env t
sharingSubst {e' = Num n} x IntVal e = subst x (Num n) e
sharingSubst {e' = Abs t e'} x ArrowVal e = subst x (Abs t e') e
sharingSubst {env = env} {t = t} {e' = Constr {ctrs = ctrs} tag es} x DataVal e =
    case anfCtor (snd (index tag ctrs)) es of
        (letf, newArgs) =>
            let e' : Expr (insertAt (extendFin (fst (index tag ctrs)) x)
                                    (DataTy ctrs)
                                    (snd (index tag ctrs) ++ env)) t =
                rewrite sym (appendInsert (snd (index tag ctrs)) env x (DataTy ctrs))
                in multiincr e
            in letf (subst (extendFin (fst (index tag ctrs)) x) (Constr tag newArgs) e')
sharingSubst {e' = Let e1 e2} x (LetVal v) e =
    Let e1 (sharingSubst (FS x) v (incr FZ _ e))
