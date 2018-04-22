module Ty

import Data.Vect
import VectHelper

%default total

public export
data Ty : Nat -> Type where
  TyVar : Fin n -> Ty n
  ArrowTy : Ty n -> Ty n -> Ty n
  IntTy : Ty n
  DataTy : Vect m (k ** Vect k (Ty n)) -> Ty n
  ForallTy : Ty (S n) -> Ty n

mutual
  public export
  tyincr : Fin (S n) -> Ty n -> Ty (S n)
  tyincr ix (TyVar x) = TyVar (fincr ix x)
  tyincr ix (ArrowTy t1 t2) = ArrowTy (tyincr ix t1) (tyincr ix t2)
  tyincr ix IntTy = IntTy
  tyincr ix (DataTy ctrs) = DataTy (ctrsincrs ix ctrs)
  tyincr ix (ForallTy t) = ForallTy (tyincr (FS ix) t)

  public export
  ctrsincrs : Fin (S n) -> Vect m (k ** Vect k (Ty n)) -> Vect m (k ** Vect k (Ty (S n)))
  ctrsincrs ix [] = []
  ctrsincrs ix ((k ** ctr) :: ctrs) = (k ** ctrincr ix ctr) :: ctrsincrs ix ctrs

  public export
  ctrincr : Fin (S n) -> Vect k (Ty n) -> Vect k (Ty (S n))
  ctrincr ix [] = []
  ctrincr ix (t :: ts) = tyincr ix t :: ctrincr ix ts

mutual
  public export
  tsubst : Fin (S n) -> Ty n -> Ty (S n) -> Ty n
  tsubst ix t' (TyVar x) with (decEq x ix)
    tsubst ix t' (TyVar ix) | Yes Refl = t'
    tsubst ix t' (TyVar x) | No neq = TyVar (fdecr x neq)
  tsubst ix t' (ArrowTy t1 t2) = ArrowTy (tsubst ix t' t1) (tsubst ix t' t2)
  tsubst ix t' IntTy = IntTy
  tsubst ix t' (DataTy ctrs) = DataTy (ctrssubst ix t' ctrs)
  tsubst ix t' (ForallTy t) = ForallTy (tsubst (FS ix) (tyincr 0 t') t)

  public export
  ctrssubst : Fin (S n) -> Ty n -> Vect m (k ** Vect k (Ty (S n))) -> Vect m (k ** Vect k (Ty n))
  ctrssubst ix t' [] = []
  ctrssubst ix t' ((k ** ctr) :: ctrs) = (k ** ctrsubst ix t' ctr) :: ctrssubst ix t' ctrs

  public export
  ctrsubst : Fin (S n) -> Ty n -> Vect k (Ty (S n)) -> Vect k (Ty n)
  ctrsubst ix t' [] = []
  ctrsubst ix t' (t :: ts) = tsubst ix t' t :: ctrsubst ix t' ts

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
