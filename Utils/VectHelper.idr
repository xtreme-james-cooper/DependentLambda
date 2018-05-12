module Utils.VectHelper

import public Data.Vect
import public Utils.FinHelper

%default total

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
