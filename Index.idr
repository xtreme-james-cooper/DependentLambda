module Index

import Data.Vect

%default total

public export
data Index : Vect n a -> a -> Type where
  IxZ : (a : t) -> (as : Vect n t) -> Index (a :: as) a
  IxS : (n : Nat) -> (as : Vect n t) -> (a : t) -> (b : t) -> Index as a -> Index (b :: as) a

export
indexInsert : (b : t) -> (x : Fin (S n)) -> Index env a -> Index (insertAt x b env) a
indexInsert b FZ ix = IxS _ _ _ _ ix
indexInsert b (FS x) (IxZ a as) = IxZ a (insertAt x b as)
indexInsert b (FS x) (IxS n as a c ix) = IxS (S n) (insertAt x b as) a c (indexInsert b x ix)

export
finFromIndex : {env : Vect n a} -> Index env t -> Fin n
finFromIndex (IxZ a as) = FZ
finFromIndex (IxS n as a c ix) = FS (finFromIndex ix)

export
compareFinToIndex : (x : Fin n) -> (ix : Index env a) -> Dec (finFromIndex ix = x)
compareFinToIndex FZ (IxZ a as) = Yes Refl
compareFinToIndex FZ (IxS n as a c ix) = No (\Refl impossible)
compareFinToIndex (FS x) (IxZ a as) = No (\Refl impossible)
compareFinToIndex (FS x) (IxS n as a c ix) = case compareFinToIndex x ix of
    Yes Refl => Yes Refl
    No npf => No (\Refl => npf Refl)

export
indexOfIndex : (x : Fin n) -> (ix : Index env a) -> finFromIndex ix = x -> index x env = a
indexOfIndex FZ (IxZ a as) eq = Refl
indexOfIndex FZ (IxS k as a b x) Refl impossible
indexOfIndex (FS x) (IxZ a as) Refl impossible
indexOfIndex (FS x) (IxS k as a b ix) eq = indexOfIndex x ix (fsDown eq)
    where fsDown : FS i = FS j -> i = j
          fsDown Refl = Refl

export
indexSubr : (b : t) -> (x : Fin (S n)) -> (ix : Index (insertAt x b env) a) ->
  Not (finFromIndex ix = x) -> Index env a
indexSubr b FZ (IxZ b as) neq = absurd (neq Refl)
indexSubr b FZ (IxS n as a b ix) neq = ix
indexSubr b (FS x) ix neq {env = []} impossible
indexSubr b (FS x) (IxZ y (insertAt x b env)) neq {env = (y :: env)} = IxZ y env
indexSubr b (FS x) (IxS (S n) (insertAt x b env) a y ix) neq {env = (y :: env)} =
    IxS n env a y (indexSubr b x ix (npf neq))
        where npf : (neq : Not (FS i = FS j)) -> Not (i = j)
              npf neq Refl = neq Refl

export
indexInsertAt : (x : Fin (S n)) -> (a : t) -> (env : Vect n t) -> index x (insertAt x a env) = a
indexInsertAt FZ a env = Refl
indexInsertAt (FS x) a [] impossible
indexInsertAt (FS x) a (y :: env) = indexInsertAt x a env
