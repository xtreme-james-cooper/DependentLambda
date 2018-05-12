module Utils.Index

import public Utils.VectHelper

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

public export
finFromIndex : {env : Vect n a} -> Index env t -> Fin n
finFromIndex (IxZ a as) = FZ
finFromIndex (IxS c ix) = FS (finFromIndex ix)

export
sameIndex : {as : Vect n a'} -> {bs : Vect n b'} -> (ix1 : Index as a) -> (ix2 : Index bs b) -> Type
sameIndex ix1 ix2 = finFromIndex ix1 = finFromIndex ix2

export
compareIndex : (ix1 : Index as a) -> (ix2 : Index bs b) -> Dec (sameIndex ix1 ix2)
compareIndex (IxZ a as) (IxZ b bs) = Yes Refl
compareIndex (IxZ a as) (IxS b ix2) = No (\Refl impossible)
compareIndex (IxS a ix1) (IxZ b bs) = No (\Refl impossible)
compareIndex (IxS a ix1) (IxS b ix2) = case compareIndex ix1 ix2 of
    Yes pf => Yes (rewrite pf in Refl)
    No npf => No (\pf => npf (rewrite FSinjective pf in Refl))

export
compareFinToIndex : (x : Fin n) -> (ix : Index env a) -> Dec (finFromIndex ix = x)
compareFinToIndex FZ (IxZ a as) = Yes Refl
compareFinToIndex FZ (IxS c ix) = No (\Refl impossible)
compareFinToIndex (FS x) (IxZ a as) = No (\Refl impossible)
compareFinToIndex (FS x) (IxS c ix) = case compareFinToIndex x ix of
    Yes Refl => Yes Refl
    No npf => No (\Refl => npf Refl)

export
indexSplit : (as : Vect n t) -> (ix : Index (as ++ bs) a) ->
    Either (ix' : Index as a ** ix = indexRightExtend bs ix')
           (ix' : Index bs a ** ix = indexLeftExtend as ix')
indexSplit [] ix = Right (ix ** Refl)
indexSplit (a :: as) (IxZ a (as ++ bs)) = Left (IxZ a as ** Refl)
indexSplit (a' :: as) (IxS a' ix) with (indexSplit as ix)
  indexSplit (a' :: as) (IxS a' (indexRightExtend bs ix')) | Left (ix' ** Refl) =
      Left (IxS a' ix' ** Refl)
  indexSplit (a' :: as) (IxS a' (indexLeftExtend as ix')) | Right (ix' ** Refl) =
      Right (ix' ** Refl)

export
indexOfIndex : (x : Fin n) -> (ix : Index env a) -> finFromIndex ix = x -> index x env = a
indexOfIndex FZ (IxZ a as) eq = Refl
indexOfIndex FZ (IxS b x) Refl impossible
indexOfIndex (FS x) (IxZ a as) Refl impossible
indexOfIndex (FS x) (IxS b ix) eq = indexOfIndex x ix (FSinjective eq)

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

export
indexSubst : (x : Fin (S n)) -> Index env t' -> Index (insertAt x t' env) t -> Index env t
indexSubst x ix' ix {t' = t'} {env = env} with (compareFinToIndex x ix)
  indexSubst x ix' ix {t' = t'} {env = env} | Yes eq with (indexOfIndex x ix eq)
   indexSubst x ix' ix {t' = t'} {env = env} | Yes eq | Refl =
       rewrite indexInsertAt x t' env in ix'
  indexSubst x ix' ix {t' = t'} {env = env} | No neq = indexSubr _ x ix neq

export
indexMap : (f : a -> b) -> Index env t -> Index (map f env) (f t)
indexMap f (IxZ a as) = IxZ (f a) (map f as)
indexMap f (IxS b ix) = IxS (f b) (indexMap f ix)
