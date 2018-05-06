module FinHelper

import Data.Fin

%default total

public export
fincr : Fin (S n) -> Fin n -> Fin (S n)
fincr FZ x = FS x
fincr (FS ix) FZ = FZ
fincr (FS ix) (FS x) = FS (fincr ix x)

public export
fneqDown : Not (FS x = FS y) -> Not (x = y)
fneqDown neq Refl = neq Refl

public export
fdecr : (x : Fin (S n)) -> {y : Fin (S n)} -> Not (x = y) -> Fin n
fdecr {n = n} FZ {y = FZ} neq = void (neq Refl)
fdecr {n = S n} FZ {y = FS y} neq = FZ
fdecr {n = n} (FS x) {y = FZ} neq = x
fdecr {n = S n} (FS x) {y = FS y} neq = FS (fdecr x {y = y} (fneqDown neq))

public export
extendFin : (m : Nat) -> Fin (S n) -> Fin (S (m + n))
extendFin Z x = x
extendFin (S m) x = FS (extendFin m x)

public export
extendFin' : (m : Nat) -> Fin (S n) -> Fin (m + S n)
extendFin' Z x = x
extendFin' (S m) x = FS (extendFin' m x)

public export
data FinLessEqThan : Fin n -> Fin n -> Type where
  ZLeX : FinLessEqThan FZ x
  SLeS : FinLessEqThan x y -> FinLessEqThan (FS x) (FS y)

export
fincrNeverEq : (x : Fin (S n)) -> (y : Fin n) -> Not (fincr x y = x)
fincrNeverEq FZ y Refl impossible
fincrNeverEq (FS x) FZ Refl impossible
fincrNeverEq (FS x) (FS y) eq = fincrNeverEq x y (FSInjective _ _ eq)

export
fdecrEq : (x : Fin (S n)) -> {y : Fin (S n)} -> (neq, neq' : Not (x = y)) ->
    fdecr x neq = fdecr x neq'
fdecrEq {n = n} FZ {y = FZ} neq neq' = void (neq Refl)
fdecrEq {n = S n} FZ {y = FS y} neq neq' = Refl
fdecrEq {n = n} (FS x) {y = FZ} neq neq' = Refl
fdecrEq {n = S n} (FS x) {y = FS y} neq neq' =
    rewrite fdecrEq x (fneqDown neq) (fneqDown neq') in Refl

export
fincrFincr : (x, y : Fin (S n)) -> (z : Fin n) -> FinLessEqThan y x ->
    fincr (FS x) (fincr y z) = fincr (weaken y) (fincr x z)
fincrFincr FZ FZ z le = Refl
fincrFincr FZ (FS x) z le impossible
fincrFincr (FS x) FZ z le = Refl
fincrFincr (FS x) (FS y) FZ le = Refl
fincrFincr (FS x) (FS y) (FS z) (SLeS le) = rewrite fincrFincr x y z le in Refl

export
fincrFdecrLe : (x, y, z : Fin (S n)) -> (neq : Not (z = x)) ->
    (neq' : Not (fincr (weaken y) z = FS x)) -> y `FinLessEqThan` x ->
        fdecr (fincr (weaken y) z) neq' = fincr y (fdecr z neq)
fincrFdecrLe {n = n} x FZ z neq neq' le = rewrite fdecrEq z (fneqDown neq') neq in Refl
fincrFdecrLe {n = n} FZ (FS y) FZ neq neq' le = void (neq Refl)
fincrFdecrLe {n = S n} (FS x) (FS y) FZ neq neq' le = Refl
fincrFdecrLe {n = n} FZ (FS y) (FS z) neq neq' le impossible
fincrFdecrLe {n = S n} (FS x) (FS y) (FS z) neq neq' (SLeS le) =
    rewrite fincrFdecrLe x y z (fneqDown neq) (fneqDown neq') le in Refl

export
fincrFdecr : (x : Fin (S n)) -> (y : Fin n) -> (neq : Not (fincr x y = x)) ->
    fdecr (fincr x y) neq = y
fincrFdecr FZ y neq = Refl
fincrFdecr (FS x) FZ neq = Refl
fincrFdecr (FS x) (FS y) neq = rewrite fincrFdecr x y (fneqDown neq) in Refl

export
fincrLessThan : (x, y : Fin (S n)) -> y `FinLessEqThan` x -> fincr (weaken y) x = FS x
fincrLessThan {n = n} x FZ ZLeX = Refl
fincrLessThan {n = S n} (FS x) (FS y) (SLeS le) =
    rewrite fincrLessThan x y le in Refl

export
fincrLessThanDown : (x, y, z : Fin (S n)) -> fincr (weaken y) x = FS z ->
    y `FinLessEqThan` z -> x = z
fincrLessThanDown x FZ x Refl le = Refl
fincrLessThanDown FZ (FS y) z Refl le impossible
fincrLessThanDown (FS x) (FS y) FZ eq le impossible
fincrLessThanDown {n = S n} (FS x) (FS y) (FS z) eq (SLeS le) =
    rewrite fincrLessThanDown x y z (FSInjective _ _ eq) le in Refl

export
lessThanFS : y `FinLessEqThan` x -> Not (FS x = weaken y)
lessThanFS ZLeX Refl impossible
lessThanFS (SLeS le) eq = lessThanFS le (FSInjective _ _ eq)

export
fdecrLessThan : y `FinLessEqThan` x -> (neq : Not (FS x = weaken y)) ->
    fdecr (FS x) neq = x
fdecrLessThan ZLeX neq = Refl
fdecrLessThan (SLeS le) neq = rewrite fdecrLessThan le (fneqDown neq) in Refl

export
fdecrLessThan2 : y `FinLessEqThan` x -> (neq : Not (weaken y = FS x)) ->
    fdecr (weaken y) neq = y
fdecrLessThan2 ZLeX neq = Refl
fdecrLessThan2 (SLeS le) neq = rewrite fdecrLessThan2 le (fneqDown neq) in Refl

export
fdecrSwap : (neq : Not (z = FS x)) -> (neq' : Not (fdecr z neq = y)) ->
    (neq'' : Not (z = weaken y)) -> (neq''' : Not (fdecr z neq'' = x)) ->
        y `FinLessEqThan` x ->
            fdecr (fdecr z neq) neq' = fdecr (fdecr z neq'') neq'''
fdecrSwap {x = x} {y = FZ} {z = FZ} neq neq' neq'' neq''' le = void (neq' Refl)
fdecrSwap {x = FZ} {y = FS y} {z = FZ} neq neq' neq'' neq''' le = void (neq''' Refl)
fdecrSwap {x = FS {k = S n} x} {y = FS y} {z = FZ} neq neq' neq'' neq''' le = Refl
fdecrSwap {x = x} {y = FZ} {z = FS z} neq neq' neq'' neq''' le =
    fdecrEq z (fneqDown neq) neq'''
fdecrSwap {x = FZ} {y = FS y} {z = FS z} neq neq' neq'' neq''' le impossible
fdecrSwap {x = FS {k = S n} x} {y = FS y} {z = FS z} neq neq' neq'' neq''' (SLeS le) =
    rewrite fdecrSwap (fneqDown neq) (fneqDown neq') (fneqDown neq'') (fneqDown neq''') le
    in Refl

export
tsubstLemma : (neq : Not (z = FS x)) -> Not (z = weaken y) -> y `FinLessEqThan` x ->
  Not (fdecr z neq = y)
tsubstLemma {z = FZ} neq neq' ZLeX eq = neq' Refl
tsubstLemma {z = FS z} neq neq' ZLeX Refl impossible
tsubstLemma {z = FZ} neq neq' (SLeS le) Refl impossible
tsubstLemma {z = FS z} neq neq' (SLeS le) eq =
    tsubstLemma (fneqDown neq) (fneqDown neq') le (FSInjective _ _ eq)

export
tsubstLemma2 : (neq : Not (x = weaken y)) -> (neq' : Not (x = FS (fdecr x neq))) ->
    Not (y `FinLessEqThan` fdecr x neq)
tsubstLemma2 {x = FZ} {y = FZ} neq neq' le = void (neq Refl)
tsubstLemma2 {x = FZ} {y = FS y} neq neq' le impossible
tsubstLemma2 {x = FS x} {y = FZ} neq neq' le = void (neq' Refl)
tsubstLemma2 {x = FS x} {y = FS y} neq neq' (SLeS le) =
    tsubstLemma2 (fneqDown neq) (fneqDown neq') le
