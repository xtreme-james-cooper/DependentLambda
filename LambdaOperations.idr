module LambdaOperations

import Data.Vect
import Lambda
import VectHelper
import Index

%default total

export
incrvs : (x : Fin (S n)) -> (tt : Ty) -> VarArgs env ts -> VarArgs (insertAt x tt env) ts
incrvs x tt [] = []
incrvs x tt (ix :: ixs) = indexInsert tt x ix :: incrvs x tt ixs

mutual
  export
  incr : (x : Fin (S n)) -> (tt : Ty) -> Expr env t -> Expr (insertAt x tt env) t
  incr x tt (Var ix) = Var (indexInsert tt x ix)
  incr x tt (Num n) = Num n
  incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
  incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)
  incr x tt (Let e1 e2) = Let (incr x tt e1) (incr (FS x) tt e2)
  incr x tt (Fix e) = Fix (incr x tt e)
  incr x tt (Constr tag es) = Constr tag (incrvs x tt es)
  incr x tt (Case e as) = Case (incr x tt e) (incra x tt as)

  export
  incra : (x : Fin (S n)) -> (tt : Ty) -> Alts env ctrs ts -> Alts (insertAt x tt env) ctrs ts
  incra x tt Fail = Fail
  incra {env = env} {ctrs = (p ** xs) :: ctrs} x tt (Alt e as) =
      let e' : Expr (xs ++ insertAt x tt env) ts =
            rewrite appendInsert xs env x tt in incr (extendFin p x) tt e
      in Alt e' (incra x tt as)

incrIsVal : (x : Fin (S n)) -> IsValue e -> IsValue (incr x t e)
incrIsVal x IntVal = IntVal
incrIsVal x ArrowVal = ArrowVal
incrIsVal x DataVal = DataVal
incrIsVal x (LetVal v) = LetVal (incrIsVal (FS x) v)

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
    IsValue e' -> IsVarHeaded e ix -> (e'' : Expr env t ** Not (e'' = e))
subst e' (Var ix) v VarVar = (e' ** ?subst1)
subst e' (App e1 e2) v (AppVar vh) with (subst e' e1 v vh)
  subst e' (App e1 e2) v (AppVar vh) | (e1' ** neq) =
      (App e1' e2 ** ?subst2)
subst e' (Let e1 e2) v (LetVarL vh2 vh1) with (subst e' e1 v vh1)
  subst e' (Let e1 e2) v (LetVarL vh2 vh1) | (e1' ** neq) =
      (Let e1' e2 ** ?subst3)
subst e' (Let e1 e2) v (LetVarR vh2) with (subst (incr FZ _ e') e2 (incrIsVal FZ v) vh2)
  subst e' (Let e1 e2) v (LetVarR vh2) | (e2' ** neq) =
      (Let e1 e2' ** ?subst4)
subst e' (Fix e) v (FixVar vh) with (subst e' e v vh)
  subst e' (Fix e) v (FixVar vh) | (e1' ** neq) =
      (Fix e1' ** ?subst5)
subst e' (Case e as) v (CaseVar vh) with (subst e' e v vh)
  subst e' (Case e as) v (CaseVar vh) | (e1' ** neq) =
      (Case e1' as ** ?subst6)

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
