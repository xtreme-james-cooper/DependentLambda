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
  export
  tyincr : Fin (S n) -> Ty n -> Ty (S n)
  tyincr ix (TyVar x) = TyVar (fincr ix x)
  tyincr ix (ArrowTy t1 t2) = ArrowTy (tyincr ix t1) (tyincr ix t2)
  tyincr ix IntTy = IntTy
  tyincr ix (DataTy ctrs) = DataTy (ctrsincrs ix ctrs)
  tyincr ix (ForallTy t) = ForallTy (tyincr (FS ix) t)

  ctrsincrs : Fin (S n) -> Vect m (k ** Vect k (Ty n)) -> Vect m (k ** Vect k (Ty (S n)))
  ctrsincrs ix [] = []
  ctrsincrs ix ((k ** ctr) :: ctrs) = (k ** ctrincr ix ctr) :: ctrsincrs ix ctrs

  ctrincr : Fin (S n) -> Vect k (Ty n) -> Vect k (Ty (S n))
  ctrincr ix [] = []
  ctrincr ix (t :: ts) = tyincr ix t :: ctrincr ix ts

mutual
  export
  tsubst : Fin (S n) -> Ty n -> Ty (S n) -> Ty n
  tsubst ix t' (TyVar x) with (decEq x ix)
    tsubst ix t' (TyVar ix) | Yes Refl = t'
    tsubst ix t' (TyVar x) | No neq = TyVar (fdecr x neq)
  tsubst ix t' (ArrowTy t1 t2) = ArrowTy (tsubst ix t' t1) (tsubst ix t' t2)
  tsubst ix t' IntTy = IntTy
  tsubst ix t' (DataTy ctrs) = DataTy (ctrssubst ix t' ctrs)
  tsubst ix t' (ForallTy t) = ForallTy (tsubst (FS ix) (tyincr 0 t') t)

  ctrssubst : Fin (S n) -> Ty n -> Vect m (k ** Vect k (Ty (S n))) -> Vect m (k ** Vect k (Ty n))
  ctrssubst ix t' [] = []
  ctrssubst ix t' ((k ** ctr) :: ctrs) = (k ** ctrsubst ix t' ctr) :: ctrssubst ix t' ctrs

  ctrsubst : Fin (S n) -> Ty n -> Vect k (Ty (S n)) -> Vect k (Ty n)
  ctrsubst ix t' [] = []
  ctrsubst ix t' (t :: ts) = tsubst ix t' t :: ctrsubst ix t' ts
