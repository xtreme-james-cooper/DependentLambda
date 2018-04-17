module VectHelper

import Data.Vect

%default total

export
indexInsertAt : (x : Fin (S n)) -> (a : t) -> (env : Vect n t) -> index x (insertAt x a env) = a
indexInsertAt FZ a env = Refl
indexInsertAt (FS x) a [] impossible
indexInsertAt (FS x) a (y :: env) = indexInsertAt x a env

export
fincr : Fin (S n) -> Fin n -> Fin (S n)
fincr FZ x = FS x
fincr (FS ix) FZ = FZ
fincr (FS ix) (FS x) = FS (fincr ix x)

export
fdecr : (x : Fin (S n)) -> {y : Fin (S n)} -> Not (x = y) -> Fin n
fdecr {n = n} FZ {y = FZ} neq = void (neq Refl)
fdecr {n = S n} FZ {y = FS y} neq = FZ
fdecr {n = n} (FS x) {y = FZ} neq = x
fdecr {n = S n} (FS x) {y = FS y} neq = FS (fdecr x {y = y} (\(Refl) => neq Refl))

export
extendFin : (m : Nat) -> Fin (S n) -> Fin (S (m + n))
extendFin Z x = x
extendFin (S m) x = FS (extendFin m x)

export
appendInsert : (as : Vect n t) -> (bs : Vect m t) -> (x : Fin (S m)) -> (a : t) ->
    as ++ insertAt x a bs = insertAt (extendFin n x) a (as ++ bs)
appendInsert [] bs x c = Refl
appendInsert (a :: as) bs x c = rewrite appendInsert as bs x c in Refl
