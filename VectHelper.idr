module VectHelper

import Data.Vect

%default total

public export
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
fdecrEq : (x, y : Fin (S n)) -> {neq, neq' : Not (x = y)} -> fdecr x neq = fdecr x neq'
fdecrEq {n = n} FZ FZ {neq = neq} = void (neq Refl)
fdecrEq {n = S n} FZ (FS y) = Refl
fdecrEq {n = n} (FS x) FZ = Refl
fdecrEq {n = S n} (FS x) (FS y) = cong {f = FS} (fdecrEq x y)

export
indexInsertAt : (x : Fin (S n)) -> (a : t) -> (env : Vect n t) -> index x (insertAt x a env) = a
indexInsertAt FZ a env = Refl
indexInsertAt (FS x) a [] impossible
indexInsertAt (FS x) a (y :: env) = indexInsertAt x a env

export
appendInsert : (as : Vect n t) -> (bs : Vect m t) -> (x : Fin (S m)) -> (a : t) ->
    as ++ insertAt x a bs = insertAt (extendFin n x) a (as ++ bs)
appendInsert [] bs x c = Refl
appendInsert (a :: as) bs x c = rewrite appendInsert as bs x c in Refl

export
insertAtMap : (f : a1 -> b1) -> (x : Fin (S n)) -> (a : a1) -> (as : Vect n a1) ->
    map f (insertAt x a as) = insertAt x (f a) (map f as)
insertAtMap f FZ a as = Refl
insertAtMap f (FS x) a [] impossible
insertAtMap f (FS x) a (a' :: as) = rewrite insertAtMap f x a as in Refl

export
mapAppend : (f : a -> b) -> (as : Vect n a) -> (bs : Vect m a) ->
    map f as ++ map f bs = map f (as ++ bs)
mapAppend f [] bs = Refl
mapAppend f (a :: as) bs = rewrite mapAppend f as bs in Refl
