module Utils.Heap

import public Utils.BasicsHelper

%default total

public export
HeapEnv : Nat -> Type -> Type
HeapEnv n t = (m : Nat) -> LT m n -> t

export
extendHEnv : HeapEnv n t -> t -> HeapEnv (S n) t
extendHEnv {n = n} henv tt m lt = case decEq m n of
    Yes eq => tt
    No neq => henv m (lteNeq lt neq)

export
Heap : HeapEnv k t -> (t -> Type) -> Type
Heap {k = k} henv f = (n : Nat) -> (lt : LT n k) -> f (henv n lt)

export
hLookup : Heap henv f -> (n : Nat) -> (lt : LT n k) -> f (henv n lt)
hLookup h n = h n

export
hUpdate : {henv : HeapEnv k t} -> Heap henv f -> (n : Nat) -> (lt : LT n k) ->
    f (henv n lt) -> Heap henv f
hUpdate {k = k} h n lt a y lt' = case decEq y n of
    Yes Refl => rewrite allLtesTheSame lt' lt in a
    No neq => h y lt'

hAlloc' : {henv : HeapEnv k t} -> Heap henv f -> (v : t) -> f v -> (n : Nat) ->
    (lt : LT n (S k)) -> f (extendHEnv henv v n lt)
hAlloc' {k = k} h tt v n lt with (decEq n k)
  hAlloc' {k = k} h tt v n lt | Yes eq = v
  hAlloc' {k = k} h tt v n lt | No neq = h n (lteNeq lt neq)

export
hAlloc : {henv : HeapEnv k t} -> Heap henv f -> (v : t) -> f v -> Heap (extendHEnv henv v) f
hAlloc {k = k} h tt v = hAlloc' h tt v
