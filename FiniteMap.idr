module FiniteMap

import Data.Vect
import Index

%default total

export
FinMap : Type -> Type -> Type
FinMap k v = (n ** Vect n (k, v))

export
emptyMap : FinMap k v
emptyMap = (0 ** [])

public export
extend : FinMap k v -> k -> v -> FinMap k v
extend (n ** mp) k v = (S n ** (k, v) :: mp)

public export
multiExtend : FinMap k v -> Vect n k -> Vect n v -> FinMap k v
multiExtend mp [] [] = mp
multiExtend mp (k :: ks) (v :: vs) = extend (multiExtend mp ks vs) k v

public export
lookup' : DecEq k => Vect n (k, v) -> k -> Maybe v
lookup' [] k = Nothing
lookup' ((k', v) :: mp) k with (decEq k k')
  lookup' ((k', v) :: mp) k | Yes eq = Just v
  lookup' ((k', v) :: mp) k | No new = lookup' mp k

public export
lookup : DecEq k => FinMap k v -> k -> Maybe v
lookup (n ** mp) k = lookup' mp k

mapHelper : (v -> u) -> (k, v) -> (k, u)
mapHelper f (k, v) = (k, f v)

export
fmap : (v -> u) -> FinMap k v -> FinMap k u
fmap f (n ** mp) = (n ** map (mapHelper f) mp)

mapExtend : (f : v -> u) -> (mp : FinMap k v) -> (kk : k) -> (vv : v) ->
    fmap f (extend mp kk vv) = extend (fmap f mp) kk (f vv)
mapExtend f (x ** pf) kk vv = Refl

mapMultiExtend : (f : v -> u) -> (mp : FinMap k v) -> (ks : Vect n k) -> (vs : Vect n v) ->
    fmap f (multiExtend mp ks vs) = multiExtend (fmap f mp) ks (map f vs)
mapMultiExtend f mp [] [] = Refl
mapMultiExtend f mp (k :: ks) (v :: vs) =
    rewrite mapExtend f (multiExtend mp ks vs) k v
    in rewrite mapMultiExtend f mp ks vs
    in Refl

export
mapMultiExtendEmpty : (f : v -> u) -> (ks : Vect n k) -> (vs : Vect n v) ->
    fmap f (multiExtend FiniteMap.emptyMap ks vs) = multiExtend FiniteMap.emptyMap ks (map f vs)
mapMultiExtendEmpty f ks vs = rewrite mapMultiExtend f emptyMap ks vs in Refl

lookupExtendEq : DecEq kk => (mp : FinMap kk vv) -> (k : kk) -> (v : vv) ->
    lookup (extend mp k v) k = Just t -> t = v
lookupExtendEq (n ** mp) k v eq with (decEq k k)
  lookupExtendEq (n ** mp) k v Refl | Yes Refl = Refl
  lookupExtendEq (n ** mp) k v eq | No neq = void (neq Refl)

lookupExtendNeq : DecEq kk => (mp : FinMap kk vv) -> (k : kk) -> (v : vv) ->
    (k' : kk) -> Not (k = k') -> lookup (extend mp k v) k' = Just t ->
        lookup mp k' = Just t
lookupExtendNeq (n ** mp) k v k' neq eq with (decEq k' k)
  lookupExtendNeq (n ** mp) k v k neq eq | Yes Refl = void (neq Refl)
  lookupExtendNeq (n ** mp) k v k' neq eq | No neq' = eq

multiExtendAppend : (mp : FinMap k v) -> (ks : Vect n k) -> (vs : Vect n v) ->
    (ks' : Vect m k) -> (vs' : Vect m v) ->
        multiExtend (multiExtend mp ks vs) ks' vs' = multiExtend mp (ks' ++ ks) (vs' ++ vs)
multiExtendAppend mp ks vs [] [] = Refl
multiExtendAppend mp ks vs (k :: ks') (v :: vs') =
    rewrite multiExtendAppend mp ks vs ks' vs' in Refl

export
multiExtendAppendEmpty : (ks : Vect n k) -> (vs : Vect n v) ->
    (ks' : Vect m k) -> (vs' : Vect m v) ->
        multiExtend (multiExtend FiniteMap.emptyMap ks vs) ks' vs' =
            multiExtend FiniteMap.emptyMap (ks' ++ ks) (vs' ++ vs)
multiExtendAppendEmpty ks vs ks' vs' =
    rewrite multiExtendAppend emptyMap ks vs ks' vs' in Refl

export
getIndex : DecEq k => (ks : Vect n k) -> (vs : Vect n v) -> (x : k) ->
    lookup (multiExtend FiniteMap.emptyMap ks vs) x = Just t -> Index vs t
getIndex [] [] x Refl impossible
getIndex (k :: ks) (v :: vs) x eq with (decEq k x)
  getIndex (k :: ks) (v :: vs) k eq | Yes Refl =
      rewrite lookupExtendEq (multiExtend emptyMap ks vs) k v eq in IxZ _ _
  getIndex (k :: ks) (v :: vs) x eq | No neq =
      IxS v (getIndex ks vs x (lookupExtendNeq (multiExtend emptyMap ks vs) k v x neq eq))
