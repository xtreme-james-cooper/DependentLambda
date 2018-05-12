module Utils.Iterate

%default total

public export
data Iterate : (a -> a -> Type) -> a -> a -> Type where
  Nil : Iterate f a a
  (::) : f a b -> Iterate f b c -> Iterate f a c

export
iterOne : f a b -> Iterate f a b
iterOne fab = [fab]

export
iterConcat : Iterate f a b -> Iterate f b c -> Iterate f a c
iterConcat [] it2 = it2
iterConcat (fab :: it1) it2 = fab :: iterConcat it1 it2

export
iterEndStep : Iterate f a b -> f b c -> Iterate f a c
iterEndStep it fbc = iterConcat it (iterOne fbc)
