module Utils.BasicsHelper

%default total

export
allEqsTheSame : (a : x = y) -> (b : x = y) -> a = b
allEqsTheSame Refl Refl = Refl

export
allLtesTheSame : (a : LTE x y) -> (b : LTE x y) -> a = b
allLtesTheSame LTEZero LTEZero = Refl
allLtesTheSame (LTESucc a) (LTESucc b) = rewrite allLtesTheSame a b in Refl

export
neqDown : Not (S m = S n) -> Not (m = n)
neqDown neq Refl = neq Refl

export
lteNeq : LTE (S m) (S n) -> Not (m = n) -> LTE (S m) n
lteNeq {m = m} {n = n} LTEZero neq impossible
lteNeq {m = Z} {n = Z} (LTESucc LTEZero) neq = void (neq Refl)
lteNeq {m = Z} {n = S n} (LTESucc LTEZero) neq = LTESucc LTEZero
lteNeq {m = S m} {n = S n} (LTESucc (LTESucc lte)) neq =
    LTESucc (lteNeq (LTESucc lte) (neqDown neq))
