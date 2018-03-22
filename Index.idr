module Index

import Data.Vect

%default total

public export
data Index : Vect n t -> t -> Type where
  IxZ : (a : t) -> (as : Vect n t) -> Index (a :: as) a
  IxS : (b : t) -> Index as a -> Index (b :: as) a

export
indexInsert : (b : t) -> (x : Fin (S n)) -> Index env a -> Index (insertAt x b env) a
indexInsert b FZ ix = IxS b ix
indexInsert b (FS x) (IxZ a as) = IxZ a (insertAt x b as)
indexInsert b (FS x) (IxS c ix) = IxS c (indexInsert b x ix)

export
indexLeftExtend : (env' : Vect n t) -> Index env a -> Index (env' ++ env) a
indexLeftExtend [] ix = ix
indexLeftExtend (x :: xs) ix = IxS x (indexLeftExtend xs ix)

export
indexRightExtend : (env' : Vect n t) -> Index env a -> Index (env ++ env') a
indexRightExtend env' (IxZ a env) = IxZ a (env ++ env')
indexRightExtend env' (IxS b ix) = IxS b (indexRightExtend env' ix)

export
finFromIndex : {env : Vect n a} -> Index env t -> Fin n
finFromIndex (IxZ a as) = FZ
finFromIndex (IxS c ix) = FS (finFromIndex ix)

export
indexSplit : (as : Vect n t) -> (ix : Index (as ++ bs) a) ->
    Either (ix' : Index as a ** ix = indexRightExtend bs ix')
           (ix' : Index bs a ** ix = indexLeftExtend as ix')
indexSplit [] ix = Right (ix ** Refl)
indexSplit (a :: as) (IxZ a (as ++ bs)) = Left (IxZ a as ** Refl)
indexSplit (a' :: as) (IxS a' ix) with (indexSplit as ix)
  indexSplit (a' :: as) (IxS a' (indexRightExtend bs ix')) | Left (ix' ** Refl) =
      Left (IxS a' ix' ** ?other)
  indexSplit (a' :: as) (IxS a' (indexLeftExtend as ix')) | Right (ix' ** Refl) =
      Right (ix' ** Refl)

export
compareFinToIndex : (x : Fin n) -> (ix : Index env a) -> Dec (finFromIndex ix = x)
compareFinToIndex FZ (IxZ a as) = Yes Refl
compareFinToIndex FZ (IxS c ix) = No (\Refl impossible)
compareFinToIndex (FS x) (IxZ a as) = No (\Refl impossible)
compareFinToIndex (FS x) (IxS c ix) = case compareFinToIndex x ix of
    Yes Refl => Yes Refl
    No npf => No (\Refl => npf Refl)

export
indexOfIndex : (x : Fin n) -> (ix : Index env a) -> finFromIndex ix = x -> index x env = a
indexOfIndex FZ (IxZ a as) eq = Refl
indexOfIndex FZ (IxS b x) Refl impossible
indexOfIndex (FS x) (IxZ a as) Refl impossible
indexOfIndex (FS x) (IxS b ix) eq = indexOfIndex x ix (fsDown eq)
    where fsDown : FS i = FS j -> i = j
          fsDown Refl = Refl

export
indexSubr : (b : t) -> (x : Fin (S n)) -> (ix : Index (insertAt x b env) a) ->
  Not (finFromIndex ix = x) -> Index env a
indexSubr b FZ (IxZ b as) neq = absurd (neq Refl)
indexSubr b FZ (IxS b ix) neq = ix
indexSubr b (FS x) ix neq {env = []} impossible
indexSubr b (FS x) (IxZ y (insertAt x b env)) neq {env = (y :: env)} = IxZ y env
indexSubr b (FS x) (IxS y ix) neq {env = (y :: env)} =
    IxS y (indexSubr b x ix (npf neq))
        where npf : (neq : Not (FS i = FS j)) -> Not (i = j)
              npf neq Refl = neq Refl
