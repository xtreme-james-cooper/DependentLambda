module Index

import Data.Vect

%default total

export
indexInsertAt : (x : Fin (S n)) -> (a : t) -> (env : Vect n t) -> index x (insertAt x a env) = a
indexInsertAt FZ a env = Refl
indexInsertAt (FS x) a [] impossible
indexInsertAt (FS x) a (y :: env) = indexInsertAt x a env

public export
extendFin : (m : Nat) -> Fin (S n) -> Fin (S (m + n))
extendFin Z x = x
extendFin (S m) x = FS (extendFin m x)

export
appendInsert : (as : Vect n t) -> (bs : Vect m t) -> (x : Fin (S m)) -> (a : t) ->
    as ++ insertAt x a bs = insertAt (extendFin n x) a (as ++ bs)
appendInsert [] bs x c = Refl
appendInsert (a :: as) bs x c = rewrite appendInsert as bs x c in Refl
