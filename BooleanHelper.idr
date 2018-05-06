module BooleanHelper

import Data.Vect
import FinHelper

public export
or : Bool -> Bool -> Bool
or True x = True
or False x = x

export
orLeft : Data.Vect.index x (zipWith BooleanHelper.or as bs) = False -> index x as = False
orLeft {x = FZ} {as = True :: as} {bs = b :: bs} Refl impossible
orLeft {x = FZ} {as = False :: as} {bs = b :: bs} eq = Refl
orLeft {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orLeft {x = x} {as = as} {bs = bs} eq

export
orRight : Data.Vect.index x (zipWith BooleanHelper.or as bs) = False -> index x bs = False
orRight {x = FZ} {as = True :: as} {bs = b :: bs} Refl impossible
orRight {x = FZ} {as = False :: as} {bs = True :: bs} Refl impossible
orRight {x = FZ} {as = False :: as} {bs = False :: bs} eq = Refl
orRight {x = FS x} {as = a :: as} {bs = b :: bs} eq =
    orRight {x = x} {as = as} {bs = bs} eq

export
orTail : Data.Vect.index x (tail as) = False -> index (FS x) as = False
orTail {as = a :: as} eq = eq

export
orDrop : Data.Vect.index x (drop p as) = False -> Data.Vect.index (extendFin' p x) as = False
orDrop {x = x} {as = a :: as} {p = Z} eq = eq
orDrop {x = x} {as = a :: as} {p = S p} eq =
    orDrop {x = x} {as = as} {p = p} eq
