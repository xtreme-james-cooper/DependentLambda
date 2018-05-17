module Utils.BooleanHelper

import public Data.Vect
import public Utils.FinHelper

%default total

public export
or : Bool -> Bool -> Bool
or True x = True
or False x = x

export
orLeftT : Data.Vect.index x as = True -> index x (zipWith BooleanHelper.or as bs) = True
orLeftT {x = FZ} {as = True :: as} {bs = b :: bs} eq = Refl
orLeftT {x = FZ} {as = False :: as} {bs = b :: bs} Refl impossible
orLeftT {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orLeftT {x = x} {as = as} {bs = bs} eq

export
orRightT : Data.Vect.index x bs = True -> index x (zipWith BooleanHelper.or as bs) = True
orRightT {x = FZ} {as = True :: as} {bs = b :: bs} eq = Refl
orRightT {x = FZ} {as = False :: as} {bs = True :: bs} eq = Refl
orRightT {x = FZ} {as = False :: as} {bs = False :: bs} Refl impossible
orRightT {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orRightT {x = x} {as = as} {bs = bs} eq

export
orTailT : Data.Vect.index (FS x) as = True -> index x (tail as) = True
orTailT {as = a :: as} eq = eq

export
orLeftF : Data.Vect.index x (zipWith BooleanHelper.or as bs) = False -> index x as = False
orLeftF {x = FZ} {as = True :: as} {bs = b :: bs} Refl impossible
orLeftF {x = FZ} {as = False :: as} {bs = b :: bs} eq = Refl
orLeftF {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orLeftF {x = x} {as = as} {bs = bs} eq

export
orRightF : Data.Vect.index x (zipWith BooleanHelper.or as bs) = False -> index x bs = False
orRightF {x = FZ} {as = True :: as} {bs = b :: bs} Refl impossible
orRightF {x = FZ} {as = False :: as} {bs = True :: bs} Refl impossible
orRightF {x = FZ} {as = False :: as} {bs = False :: bs} eq = Refl
orRightF {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orRightF {x = x} {as = as} {bs = bs} eq

export
orTailF : Data.Vect.index x (tail as) = False -> index (FS x) as = False
orTailF {as = a :: as} eq = eq

export
orDropF : Data.Vect.index x (drop p as) = False -> Data.Vect.index (extendFin' p x) as = False
orDropF {x = x} {as = a :: as} {p = Z} eq = eq
orDropF {x = x} {as = a :: as} {p = S p} eq =
    orDropF {x = x} {as = as} {p = p} eq

export
eqFlip : Not (a = False) -> a = True
eqFlip {a = False} neq = void (neq Refl)
eqFlip {a = True} neq = Refl

export
eqFlip' : a = False -> Not (a = True)
eqFlip' Refl Refl impossible
