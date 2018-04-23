module TyLemmas

import Data.Vect
import VectHelper
import Ty

%default total

export
ctrsubstMap : (x : Fin (S n)) -> (t' : Ty n) -> (ts : Vect k (Ty (S n))) ->
    ctrsubst x t' ts = map (tsubst x t') ts
ctrsubstMap x t' [] = Refl
ctrsubstMap x t' (t :: ts) = rewrite ctrsubstMap x t' ts in Refl

mutual
  tsubstTincr : (x : Fin (S n)) -> (t' : Ty n) -> (t : Ty (S n)) ->
      tsubst (FS x) (tyincr FZ t') (tyincr FZ t) = tyincr FZ (tsubst x t' t)
  tsubstTincr x t' (TyVar y) with (decEq y x)
    tsubstTincr x t' (TyVar x) | Yes Refl = Refl
    tsubstTincr x t' (TyVar y) | No neq = ?argl2
  tsubstTincr x t' (ArrowTy t1 t2) =
      rewrite tsubstTincr x t' t1 in rewrite tsubstTincr x t' t2 in Refl
  tsubstTincr x t' IntTy = Refl
  tsubstTincr x t' (DataTy ctrs) = rewrite tsubstTincrCtrs x t' ctrs in Refl
  tsubstTincr x t' (ForallTy t) = ?aghhh_5

  tsubstTincrCtrs : (x : Fin (S n)) -> (t' : Ty n) -> (ctrs : Vect m (k ** Vect k (Ty (S n)))) ->
      ctrssubst (FS x) (tyincr FZ t') (ctrsincrs FZ ctrs) = ctrsincrs FZ (ctrssubst x t' ctrs)
  tsubstTincrCtrs x t' [] = Refl
  tsubstTincrCtrs x t' ((k ** ctr) :: ctrs) =
      rewrite tsubstTincrCtrs x t' ctrs in rewrite tsubstTincrCtr x t' ctr in Refl

  tsubstTincrCtr : (x : Fin (S n)) -> (t' : Ty n) -> (ctr : Vect k (Ty (S n))) ->
      ctrsubst (FS x) (tyincr FZ t') (ctrincr FZ ctr) = ctrincr FZ (ctrsubst x t' ctr)
  tsubstTincrCtr x t' [] = Refl
  tsubstTincrCtr x t' (t :: ts) =
      rewrite tsubstTincrCtr x t' ts in rewrite tsubstTincr x t' t in Refl

export
tsubstTincrList : (x : Fin (S n)) -> (t' : Ty n) -> (ts : Vect k (Ty (S n))) ->
    map (tsubst (FS x) (tyincr FZ t')) (map (tyincr FZ) ts) = map (tyincr FZ) (map (tsubst x t') ts)
tsubstTincrList x t' [] = Refl
tsubstTincrList x t' (t :: ts) =
    rewrite tsubstTincrList x t' ts in rewrite tsubstTincr x t' t in Refl

export
ctrSubstSnd : (x : Fin (S tn)) -> (t' : Ty tn) -> (tag : Fin m) ->
    (ctrs : Vect m (n ** Vect n (Ty (S tn)))) ->
        snd (index tag (ctrssubst x t' ctrs)) = ctrsubst x t' (snd (index tag ctrs))
ctrSubstSnd x t' FZ ((n ** ctr) :: ctrs) = Refl
ctrSubstSnd x t' (FS tag) ((n ** ctr) :: ctrs) = ctrSubstSnd x t' tag ctrs
