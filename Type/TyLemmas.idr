module Type.TyLemmas

import public Type.Ty

%default total

export
ctrsubstMap : (x : Fin (S n)) -> (t' : Ty n) -> (ts : Vect k (Ty (S n))) ->
    ctrsubst x t' ts = map (tsubst x t') ts
ctrsubstMap x t' [] = Refl
ctrsubstMap x t' (t :: ts) = rewrite ctrsubstMap x t' ts in Refl

mutual
  tincrTincr : (x : Fin (S n)) -> (y : Fin (S n)) -> (t : Ty n) ->
      y `FinLessEqThan` x -> tyincr (FS x) (tyincr y t) = tyincr (weaken y) (tyincr x t)
  tincrTincr x y (TyVar ix) le = rewrite fincrFincr x y ix le in Refl
  tincrTincr x y (ArrowTy t1 t2) le =
      rewrite tincrTincr x y t1 le in rewrite tincrTincr x y t2 le in Refl
  tincrTincr x y IntTy le = Refl
  tincrTincr x y (DataTy ctrs) le = rewrite tincrTincrCtrs x y ctrs le in Refl
  tincrTincr x y (ForallTy t) le =
      rewrite tincrTincr (FS x) (FS y) t (SLeS le) in Refl
  tincrTincr x y (FixTy t) le =
      rewrite tincrTincr (FS x) (FS y) t (SLeS le) in Refl

  tincrTincrCtrs : (x : Fin (S n)) -> (y : Fin (S n)) ->
      (ctrs : Vect m (k ** Vect k (Ty n))) -> y `FinLessEqThan` x ->
          ctrsincrs (FS x) (ctrsincrs y ctrs) = ctrsincrs (weaken y) (ctrsincrs x ctrs)
  tincrTincrCtrs x y [] le = Refl
  tincrTincrCtrs x y ((k ** ctr) :: ctrs) le =
      rewrite tincrTincrCtrs x y ctrs le in rewrite tincrTincrCtr x y ctr le
      in Refl

  tincrTincrCtr : (x : Fin (S n)) -> (y : Fin (S n)) ->
      (ctr : Vect k (Ty n)) -> y `FinLessEqThan` x ->
          ctrincr (FS x) (ctrincr y ctr) = ctrincr (weaken y) (ctrincr x ctr)
  tincrTincrCtr x y [] le = Refl
  tincrTincrCtr x y (t :: ts) le =
      rewrite tincrTincr x y t le in rewrite tincrTincrCtr x y ts le in Refl

mutual
  tsubstIncrSame : (x : Fin (S n)) -> (t' : Ty n) -> (t : Ty n) -> tsubst x t' (tyincr x t) = t
  tsubstIncrSame x t' (TyVar y) with (decEq (fincr x y) x)
    tsubstIncrSame x t' (TyVar y) | Yes eq = void (fincrNeverEq x y eq)
    tsubstIncrSame x t' (TyVar y) | No neq = rewrite fincrFdecr x y neq in Refl
  tsubstIncrSame x t' (ArrowTy t1 t2) =
      rewrite tsubstIncrSame x t' t1 in rewrite tsubstIncrSame x t' t2 in Refl
  tsubstIncrSame x t' IntTy = Refl
  tsubstIncrSame x t' (DataTy ctrs) = rewrite tsubstIncrSameCtrs x t' ctrs in Refl
  tsubstIncrSame x t' (ForallTy t) =
      rewrite tsubstIncrSame (FS x) (tyincr FZ t') t in Refl
  tsubstIncrSame x t' (FixTy t) =
      rewrite tsubstIncrSame (FS x) (tyincr FZ t') t in Refl

  tsubstIncrSameCtrs : (x : Fin (S n)) -> (t' : Ty n) ->
      (ctrs : Vect m (k ** Vect k (Ty n))) -> ctrssubst x t' (ctrsincrs x ctrs) = ctrs
  tsubstIncrSameCtrs x t' [] = Refl
  tsubstIncrSameCtrs x t' ((k ** ctr) :: ctrs) =
      rewrite tsubstIncrSameCtrs x t' ctrs in rewrite tsubstIncrSameCtr x t' ctr
      in Refl

  tsubstIncrSameCtr : (x : Fin (S n)) -> (t' : Ty n) ->
      (ctr : Vect k (Ty n)) -> ctrsubst x t' (ctrincr x ctr) = ctr
  tsubstIncrSameCtr x t' [] = Refl
  tsubstIncrSameCtr x t' (t :: ts) =
      rewrite tsubstIncrSame x t' t in rewrite tsubstIncrSameCtr x t' ts in Refl

export
tsubstIncrSameList : (x : Fin (S n)) -> (t' : Ty n) -> (ts : Vect k (Ty n)) ->
    map (tsubst x t') (map (tyincr x) ts) = ts
tsubstIncrSameList x t' [] = Refl
tsubstIncrSameList x t' (t :: ts) =
    rewrite tsubstIncrSame x t' t in rewrite tsubstIncrSameList x t' ts in Refl

mutual
  tsubstTincr : (x : Fin (S n)) -> (y : Fin (S n)) -> (t' : Ty n) -> (t : Ty (S n)) ->
      y `FinLessEqThan` x ->
          tsubst (FS x) (tyincr y t') (tyincr (weaken y) t) = tyincr y (tsubst x t' t)
  tsubstTincr x y t' (TyVar ix) le with (decEq ix x)
    tsubstTincr x y t' (TyVar ix) le | Yes eq with (decEq (fincr (weaken y) ix) (FS x))
      tsubstTincr x y t' (TyVar ix) le | Yes eq | Yes eq' = Refl
      tsubstTincr x y t' (TyVar x) le | Yes Refl | No neq =
          void (neq (fincrLessThan x y le))
    tsubstTincr x y t' (TyVar ix) le | No neq with (decEq (fincr (weaken y) ix) (FS x))
      tsubstTincr x y t' (TyVar ix) le | No neq | Yes eq =
          void (neq (fincrLessThanDown ix y x eq le))
      tsubstTincr x y t' (TyVar ix) le | No neq | No neq' =
          rewrite fincrFdecrLe x y ix neq neq' le in Refl
  tsubstTincr x y t' (ArrowTy t1 t2) le =
      rewrite tsubstTincr x y t' t1 le in rewrite tsubstTincr x y t' t2 le in Refl
  tsubstTincr x y t' IntTy le = Refl
  tsubstTincr x y t' (DataTy ctrs) le =
      rewrite tsubstTincrCtrs x y t' ctrs le in Refl
  tsubstTincr x y t' (ForallTy t) le =
      rewrite sym (tsubstTincr (FS x) (FS y) (tyincr FZ t') t (SLeS le)) in
      rewrite tincrTincr y FZ t' ZLeX in Refl
  tsubstTincr x y t' (FixTy t) le =
      rewrite sym (tsubstTincr (FS x) (FS y) (tyincr FZ t') t (SLeS le)) in
      rewrite tincrTincr y FZ t' ZLeX in Refl

  tsubstTincrCtrs : (x : Fin (S n)) -> (y : Fin (S n)) -> (t' : Ty n) ->
      (ctrs : Vect m (k ** Vect k (Ty (S n)))) -> y `FinLessEqThan` x ->
          ctrssubst (FS x) (tyincr y t') (ctrsincrs (weaken y) ctrs) =
              ctrsincrs y (ctrssubst x t' ctrs)
  tsubstTincrCtrs x y t' [] le = Refl
  tsubstTincrCtrs x y t' ((k ** ctr) :: ctrs) le =
      rewrite tsubstTincrCtrs x y t' ctrs le in rewrite tsubstTincrCtr x y t' ctr le
      in Refl

  tsubstTincrCtr : (x : Fin (S n)) -> (y : Fin (S n)) -> (t' : Ty n) ->
      (ctr : Vect k (Ty (S n))) -> y `FinLessEqThan` x ->
          ctrsubst (FS x) (tyincr y t') (ctrincr (weaken y) ctr) =
              ctrincr y (ctrsubst x t' ctr)
  tsubstTincrCtr x y t' [] le = Refl
  tsubstTincrCtr x y t' (t :: ts) le =
      rewrite tsubstTincrCtr x y t' ts le in rewrite tsubstTincr x y t' t le in Refl

export
tsubstTincrList : (x : Fin (S n)) -> (t' : Ty n) -> (ts : Vect k (Ty (S n))) ->
    map (tsubst (FS x) (tyincr FZ t')) (map (tyincr FZ) ts) = map (tyincr FZ) (map (tsubst x t') ts)
tsubstTincrList x t' [] = Refl
tsubstTincrList x t' (t :: ts) =
    rewrite tsubstTincrList x t' ts in rewrite tsubstTincr x FZ t' t ZLeX in Refl

mutual
  export
  tsubstTsubst : (x : Fin (S tn)) -> (y : Fin (S tn)) -> (t1 : Ty tn) ->
      (t2 : Ty (S tn)) -> (t : Ty (S (S tn))) -> y `FinLessEqThan` x ->
          tsubst y (tsubst x t1 t2) (tsubst (FS x) (tyincr y t1) t) = tsubst x t1 (tsubst (weaken y) t2 t)
  tsubstTsubst x y t1 t2 (TyVar z) le with (decEq z (FS x))
    tsubstTsubst x y t1 t2 (TyVar z) le | Yes eq with (decEq z (weaken y))
      tsubstTsubst x y t1 t2 (TyVar z) le | Yes eq | Yes eq' =
          void (lessThanFS le (rewrite sym eq in eq'))
      tsubstTsubst x y t1 t2 (TyVar z) le | Yes eq | No neq' with (decEq (fdecr z neq') x)
        tsubstTsubst x y t1 t2 (TyVar z) le | Yes eq | No neq' | Yes eq'' =
            tsubstIncrSame y (tsubst x t1 t2) t1
        tsubstTsubst x y t1 t2 (TyVar z) le | Yes eq | No neq' | No neq'' =
            void (neq'' (case eq of Refl => fdecrLessThan le neq'))
    tsubstTsubst x y t1 t2 (TyVar z) le | No neq with (decEq (fdecr z neq) y)
      tsubstTsubst x y t1 t2 (TyVar z) le | No neq | Yes eq' with (decEq z (weaken y))
        tsubstTsubst x y t1 t2 (TyVar z) le | No neq | Yes eq' | Yes eq'' = Refl
        tsubstTsubst x y t1 t2 (TyVar z) le | No neq | Yes eq' | No neq'' =
            void (tsubstLemma neq neq'' le eq')
      tsubstTsubst x y t1 t2 (TyVar z) le | No neq | No neq' with (decEq z (weaken y))
        tsubstTsubst x y t1 t2 (TyVar (weaken y)) le | No neq | No neq' | Yes Refl =
            void (neq' (fdecrLessThan2 le neq))
        tsubstTsubst x y t1 t2 (TyVar z) le | No neq | No neq' | No neq'' with (decEq (fdecr z neq'') x)
          tsubstTsubst (fdecr z neq'') y t1 t2 (TyVar z) le | No neq | No neq' | No neq'' | Yes Refl =
              void (tsubstLemma2 neq'' neq le)
          tsubstTsubst x y t1 t2 (TyVar z) le | No neq | No neq' | No neq'' | No neq''' =
              rewrite fdecrSwap neq neq' neq'' neq''' le in Refl
  tsubstTsubst x y t1 t2 (ArrowTy tt1 tt2) le =
      rewrite tsubstTsubst x y t1 t2 tt1 le in rewrite tsubstTsubst x y t1 t2 tt2 le
      in Refl
  tsubstTsubst x y t1 t2 IntTy le = Refl
  tsubstTsubst x y t1 t2 (DataTy ctrs) le =
      rewrite tsubstTsubstCtrs x y t1 t2 ctrs le in Refl
  tsubstTsubst x y t1 t2 (ForallTy t) le =
      rewrite sym (tsubstTincr x FZ t1 t2 ZLeX) in rewrite sym (tincrTincr y FZ t1 ZLeX)
      in rewrite tsubstTsubst (FS x) (FS y) (tyincr FZ t1) (tyincr FZ t2) t (SLeS le)
      in Refl
  tsubstTsubst x y t1 t2 (FixTy t) le =
      rewrite sym (tsubstTincr x FZ t1 t2 ZLeX) in rewrite sym (tincrTincr y FZ t1 ZLeX)
      in rewrite tsubstTsubst (FS x) (FS y) (tyincr FZ t1) (tyincr FZ t2) t (SLeS le)
      in Refl

  tsubstTsubstCtrs : (x : Fin (S tn)) -> (y : Fin (S tn)) -> (t1 : Ty tn) ->
      (t2 : Ty (S tn)) -> (ctrs : Vect m (k ** Vect k (Ty (S (S tn))))) -> y `FinLessEqThan` x ->
          ctrssubst y (tsubst x t1 t2) (ctrssubst (FS x) (tyincr y t1) ctrs) =
              ctrssubst x t1 (ctrssubst (weaken y) t2 ctrs)
  tsubstTsubstCtrs x y t1 t2 [] le = Refl
  tsubstTsubstCtrs x y t1 t2 ((k ** ctr) :: ctrs) le =
      rewrite tsubstTsubstCtrs x y t1 t2 ctrs le
      in rewrite tsubstTsubstCtr x y t1 t2 ctr le in Refl

  tsubstTsubstCtr : (x : Fin (S tn)) -> (y : Fin (S tn)) -> (t1 : Ty tn) ->
      (t2 : Ty (S tn)) -> (ctr : Vect k (Ty (S (S tn)))) -> y `FinLessEqThan` x ->
          ctrsubst y (tsubst x t1 t2) (ctrsubst (FS x) (tyincr y t1) ctr) =
              ctrsubst x t1 (ctrsubst (weaken y) t2 ctr)
  tsubstTsubstCtr x y t1 t2 [] le = Refl
  tsubstTsubstCtr x y t1 t2 (t :: ts) le =
      rewrite tsubstTsubstCtr x y t1 t2 ts le
      in rewrite tsubstTsubst x y t1 t2 t le in Refl

export
ctrSubstSnd : (x : Fin (S tn)) -> (t' : Ty tn) -> (tag : Fin m) ->
    (ctrs : Vect m (n ** Vect n (Ty (S tn)))) ->
        snd (index tag (ctrssubst x t' ctrs)) = ctrsubst x t' (snd (index tag ctrs))
ctrSubstSnd x t' FZ ((n ** ctr) :: ctrs) = Refl
ctrSubstSnd x t' (FS tag) ((n ** ctr) :: ctrs) = ctrSubstSnd x t' tag ctrs
