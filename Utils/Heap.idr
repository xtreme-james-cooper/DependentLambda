module Utils.Heap

import public Data.Vect
import public Utils.BasicsHelper

%default total

export
Heap : (k : Nat) -> Vect k t -> (t -> Type) -> Type
Heap k henv f = (n : Fin k) -> f (index n henv)

export
hEmpty : Heap Z [] f
hEmpty n impossible

export
hLookup : Heap k henv f -> (n : Fin k) -> f (index n henv)
hLookup h n = h n

export
hUpdate : Heap k henv f -> (n : Fin k) -> f (index n henv) -> Heap k henv f
hUpdate h n a m = case decEq m n of
    Yes Refl => a
    No neq => h m

export
hAlloc : Heap k henv f -> (v : f t) -> Heap (S k) (t :: henv) f
hAlloc h v FZ = v
hAlloc h v (FS n) = h n

export
hMap : (mp : {n : Fin k} -> f (index n henv) -> f' (index n henv)) ->
    Heap k henv f -> Heap k henv f'
hMap mp h n = mp (h n)
