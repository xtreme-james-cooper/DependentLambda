module Examples

import Lambda.Evaluation.Determinism
import Stack.Evaluation.Determinism
import Named.Unname

%default total

-- fact = fix (\fact: Int -> Int. \x: Int. isZ x 1 (x * (fact (x - 1))))
fact : NExpr [] (ArrowTy IntTy IntTy)
fact = Fix (Abs "fact" (ArrowTy IntTy IntTy) (Abs "x" IntTy
    (IsZero (Var "x" Refl) (Num 1)
            (Prim (*) (Var "x" Refl)
                  (App (Var "fact" Refl)
                       (Prim (-) (Var "x" Refl) (Num 1)))))))

-- nat = fix (\nat. () + nat)
natTy : Ty 0
natTy = FixTy (DataTy [(0 ** []), (1 ** [TyVar FZ])])

natBin : Ty 0
natBin = ArrowTy natTy (ArrowTy natTy natTy)

-- plus = fix (\plus: Nat -> Nat -> Nat. \x: Nat. \y: Nat.
--          case (unfold x) of Z -> y | S n -> let i = plus n y in S i)
plus : NExpr [] Examples.natBin
plus = Fix (Abs "plus" natBin (Abs "x" natTy (Abs "y" natTy
    (Case (Unfold (Var "x" Refl) Refl)
          (Alt [] (Var "y" Refl)
          (Alt ["n"] (Let "i" (App (App (Var "plus" Refl) (Var "n" Refl)) (Var "y" Refl))
                              (Fold (Constr 1 (Cons "i" Nil Refl))))
          Fail))))))

-- mult = fix (\mult: Nat -> Nat -> Nat. \x: Nat. \y: Nat.
--          case (unfold x) of Z -> Z | S n -> plus y (mult n y))
mult : NExpr [("plus", Examples.natBin)] Examples.natBin
mult = Fix (Abs "mult" natBin (Abs "x" natTy (Abs "y" natTy
    (Case (Unfold (Var "x" Refl) Refl)
          (Alt [] (Fold (Constr 0 Nil))
          (Alt ["n"] (App (App (Var "plus" Refl) (Var "y" Refl))
                          (App (App (Var "mult" Refl) (Var "n" Refl)) (Var "y" Refl)))
          Fail))))))

-- fact = fix (\fact: Nat -> Nat. \x: Nat. case (unfold x) of Z -> 1 | S n -> mult x (fact n))
fact' : NExpr [("mult", Examples.natBin), ("plus", Examples.natBin)] (ArrowTy Examples.natTy Examples.natTy)
fact' = Fix (Abs "fact" (ArrowTy natTy natTy) (Abs "x" natTy
    (Case (Unfold (Var "x" Refl) Refl)
          (Alt [] (Let "z" (Fold (Constr 0 [])) (Fold (Constr 1 (Cons "z" Nil Refl))))
          (Alt ["n"] (App (App (Var "mult" Refl) (Var "x" Refl)) (App (Var "fact" Refl) (Var "n" Refl)))
          Fail)))))

three : NExpr [("mult", Examples.natBin), ("plus", Examples.natBin)] Examples.natTy
three = Let "z" (Fold (Constr 0 []))
        (Let "o" (Fold (Constr 1 (Cons "z" Nil Refl)))
        (Let "t" (Fold (Constr 1 (Cons "o" Nil Refl)))
        (Fold (Constr 1 (Cons "t" Nil Refl)))))

-- toInt = fix (\toInt: Nat -> Int. \x: Int. case (unfold x) of Z -> 0 | S n -> 1 + toInt n)
toInt : NExpr [] (ArrowTy Examples.natTy IntTy)
toInt = Fix (Abs "toInt" (ArrowTy natTy IntTy) (Abs "x" natTy
    (Case (Unfold (Var "x" Refl) Refl)
          (Alt [] (Num 0)
          (Alt ["n"] (Prim (+) (Num 1) (App (Var "toInt" Refl) (Var "n" Refl)))
          Fail)))))

fullFact : NExpr {tn = 0} [] IntTy
fullFact = App toInt (Let "plus" plus (Let "mult" mult (App fact' three)))
