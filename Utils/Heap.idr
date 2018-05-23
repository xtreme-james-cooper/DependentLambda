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
Heap : (k : Nat) -> HeapEnv k t -> (t -> Type) -> Type
Heap k henv f = (n : Nat) -> (lt : LT n k) -> f (henv n lt)

export
hLookup : Heap k henv f -> (n : Nat) -> (lt : LT n k) -> f (henv n lt)
hLookup h n = h n

export
hUpdate : Heap k henv f -> (n : Nat) -> (lt : LT n k) -> f (henv n lt) -> Heap k henv f
hUpdate {k = k} h n lt a y lt' = case decEq y n of
    Yes Refl => rewrite allLtesTheSame lt' lt in a
    No neq => h y lt'

hAlloc' : Heap k henv f -> (v : t) -> f v -> (n : Nat) -> (lt : LT n (S k)) ->
    f (extendHEnv henv v n lt)
hAlloc' {k = k} h tt v n lt with (decEq n k)
  hAlloc' {k = k} h tt v n lt | Yes eq = v
  hAlloc' {k = k} h tt v n lt | No neq = h n (lteNeq lt neq)

export
hAlloc : Heap k henv f -> (v : t) -> f v -> Heap (S k) (extendHEnv henv v) f
hAlloc {k = k} h tt v = hAlloc' h tt v
