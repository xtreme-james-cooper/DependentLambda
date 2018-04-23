module VectHelper

import Data.Fin

%default total

public export
fincr : Fin (S n) -> Fin n -> Fin (S n)
fincr FZ x = FS x
fincr (FS ix) FZ = FZ
fincr (FS ix) (FS x) = FS (fincr ix x)

public export
fdecr : (x : Fin (S n)) -> {y : Fin (S n)} -> Not (x = y) -> Fin n
fdecr {n = n} FZ {y = FZ} neq = void (neq Refl)
fdecr {n = S n} FZ {y = FS y} neq = FZ
fdecr {n = n} (FS x) {y = FZ} neq = x
fdecr {n = S n} (FS x) {y = FS y} neq = FS (fdecr x {y = y} (\(Refl) => neq Refl))

public export
extendFin : (m : Nat) -> Fin (S n) -> Fin (S (m + n))
extendFin Z x = x
extendFin (S m) x = FS (extendFin m x)

public export
data FinLessThan : Fin n -> Fin n -> Type where
  ZLtS : FinLessThan FZ (FS x)
  SLtS : FinLessThan x y -> FinLessThan (FS x) (FS y)

export
fdecrEq : (x, y : Fin (S n)) -> {neq, neq' : Not (x = y)} -> fdecr x neq = fdecr x neq'
fdecrEq {n = n} FZ FZ {neq = neq} = void (neq Refl)
fdecrEq {n = S n} FZ (FS y) = Refl
fdecrEq {n = n} (FS x) FZ = Refl
fdecrEq {n = S n} (FS x) (FS y) = cong {f = FS} (fdecrEq x y)
