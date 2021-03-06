module Lambda.LambdaOperations

import public Lambda.Values
import public Type.TyLemmas

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

varsMap : {env : Vect n (Ty tn)} -> {env' : Vect m (Ty tn)} ->
    IndexMap env env' -> VarArgs env ts -> VarArgs env' ts
varsMap m [] = []
varsMap m (ix :: ixs) = m ix :: varsMap m ixs

mutual
  export
  varMap : {env : Vect n (Ty tn)} -> {env' : Vect m (Ty tn)} ->
      IndexMap env env' -> Expr env t -> Expr env' t
  varMap m (Var x) = Var (m x)
  varMap m (Num n) = Num n
  varMap m (Prim f e1 e2) = Prim f (varMap m e1) (varMap m e2)
  varMap m (IsZero e1 e2 e3) =
      IsZero (varMap m e1) (varMap m e2) (varMap m e3)
  varMap m (App e1 e2) = App (varMap m e1) (varMap m e2)
  varMap m (Abs t1 e) = Abs t1 (varMap (extendIndexMap m t1) e)
  varMap m (Let e1 e2) = Let (varMap m e1) (varMap (extendIndexMap m _) e2)
  varMap m (Fix e) = Fix (varMap m e)
  varMap m (Constr tag xs) = Constr tag (varsMap m xs)
  varMap m (Case e as) = Case (varMap m e) (varMapa m as)
  varMap m (TyApp e t' eq) = TyApp (varMap m e) t' eq
  varMap m (TyAbs e) = TyAbs (varMap (mapIndexMap (tyincr FZ) m) e)
  varMap m (Fold e) = Fold (varMap m e)
  varMap m (Unfold e eq) = Unfold (varMap m e) eq

  varMapa : {env : Vect n (Ty tn)} -> {env' : Vect m (Ty tn)} ->
      IndexMap env env' -> Alts env ctrs t -> Alts env' ctrs t
  varMapa m Fail = Fail
  varMapa m (Alt e as) =
      Alt (varMap (extendsIndexMap m _) e) (varMapa m as)

indexMapFromVarArgs : VarArgs env xs -> IndexMap (xs ++ env) env
indexMapFromVarArgs [] ix = ix
indexMapFromVarArgs (x :: xs) (IxZ _ _) = x
indexMapFromVarArgs (x :: xs) (IxS _ ix) = indexMapFromVarArgs xs ix

export
altEval : (x : Fin n) -> Alts env ctrs t -> VarArgs env (snd (index x ctrs)) -> Expr env t
altEval FZ (Alt e as) es = varMap (indexMapFromVarArgs es) e
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

reduceIx : (x : Fin (S n)) -> (tt : Ty tn) -> (ix : Index (insertAt x tt env) t) ->
    index x (freeVar ix) = False -> Index env t
reduceIx FZ tt (IxZ tt env) Refl impossible
reduceIx FZ tt (IxS tt ix) nfv = ix
reduceIx (FS x) tt ix nfv {env = []} impossible
reduceIx (FS x) tt (IxZ t _) nfv {env = t :: env} = IxZ t env
reduceIx (FS x) tt (IxS t ix) nfv {env = t :: env} = IxS t (reduceIx x tt ix nfv)

reduceXs : (x : Fin (S n)) -> (tt : Ty tn) -> (xs : VarArgs (insertAt x tt env) t) ->
    index x (freeVarsXs xs) = False -> VarArgs env t
reduceXs x tt [] nfv = []
reduceXs x tt (y :: xs) nfv =
    reduceIx x tt y (orLeftF nfv) :: reduceXs x tt xs (orRightF nfv)

mutual
  export
  reduce : (x : Fin (S n)) -> (tt : Ty tn) -> (e : Expr (insertAt x tt env) t) ->
      index x (freeVars e) = False -> Expr env t
  reduce x tt (Var ix) nfv = Var (reduceIx x tt ix nfv)
  reduce x tt (Num n) nfv = Num n
  reduce x tt (Prim f e1 e2) nfv =
      Prim f (reduce x tt e1 (orLeftF nfv)) (reduce x tt e2 (orRightF nfv))
  reduce x tt (IsZero e1 e2 e3) nfv =
      IsZero (reduce x tt e1 (orLeftF nfv)) (reduce x tt e2 (orLeftF (orRightF nfv)))
             (reduce x tt e3 (orRightF (orRightF nfv)))
  reduce x tt (App e1 e2) nfv =
      App (reduce x tt e1 (orLeftF nfv)) (reduce x tt e2 (orRightF nfv))
  reduce x tt (Abs t1 e) nfv = Abs t1 (reduce (FS x) tt e (orTailF nfv))
  reduce x tt (Let e1 e2) nfv =
      Let (reduce x tt e1 (orLeftF nfv)) (reduce (FS x) tt e2 (orTailF (orRightF nfv)))
  reduce x tt (Fix e) nfv = Fix (reduce x tt e nfv)
  reduce x tt (Constr tag xs) nfv = Constr tag (reduceXs x tt xs nfv)
  reduce x tt (Case e as) nfv =
      Case (reduce x tt e (orLeftF nfv)) (reduceAs x tt as (orRightF nfv))
  reduce x tt (TyApp e t' eq) nfv = TyApp (reduce x tt e nfv) t' eq
  reduce x tt (TyAbs e) nfv {env = env} {t = ForallTy t} =
      let ep : Expr (insertAt x (tyincr FZ tt) (map (tyincr FZ) env)) t =
          rewrite sym (insertAtMap (tyincr FZ) x tt env) in e
      in let small_ep : Expr (insertAt x (tyincr FZ tt) (map (tyincr FZ) env)) t =
          assert_smaller (TyAbs e) ep
      in TyAbs (reduce x (tyincr FZ tt) small_ep (believe_me nfv))
  reduce x tt (Fold e) nfv = Fold (reduce x tt e nfv)
  reduce x tt (Unfold e eq) nfv = Unfold (reduce x tt e nfv) eq

  reduceAs : (x : Fin (S n)) -> (tt : Ty tn) -> (as : Alts (insertAt x tt env) ctrs t) ->
      index x (freeVarsAs as) = False -> Alts env ctrs t
  reduceAs x tt Fail nfv = Fail
  reduceAs x tt (Alt {p = p} {xs = xs} e as) nfv {env = env} =
      let ep : Expr (insertAt (extendFin p x) tt (xs ++ env)) t =
          rewrite sym (appendInsert xs env x tt) in e
      in let small_ep : Expr (insertAt (extendFin p x) tt (xs ++ env)) t =
          assert_smaller (Alt e as) ep
      in let nfvp : (index (extendFin' p x) (freeVars e) = False) =
          orDropF (orLeftF nfv)
      in Alt (reduce (extendFin p x) tt small_ep (believe_me nfvp))
             (reduceAs x tt as (orRightF nfv))
