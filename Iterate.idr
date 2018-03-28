module Iterate

%default total

public export
data Iterate : (a -> a -> Type) -> a -> a -> Type where
  IterRefl : Iterate f a a
  IterStep : f a b -> Iterate f b c -> Iterate f a c

export
iterOne : f a b -> Iterate f a b
iterOne fab = IterStep fab IterRefl

export
iterConcat : Iterate f a b -> Iterate f b c -> Iterate f a c
iterConcat IterRefl it2 = it2
iterConcat (IterStep fab it1) it2 = IterStep fab (iterConcat it1 it2)

export
iterEndStep : Iterate f a b -> f b c -> Iterate f a c
iterEndStep it fbc = iterConcat it (iterOne fbc)
