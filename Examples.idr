module Examples

import Data.Vect
import Index
import Ty
import Lambda
import Evaluation

primMult : Int -> Int -> Int
primMult x y = x * y

primMinus : Int -> Int -> Int
primMinus x y = x - y

-- fact = fix (\fact. \x. isZ x 1 (x * (fact (x - 1))))
fact : Expr [] (ArrowTy IntTy IntTy)
fact = Fix (Abs (ArrowTy IntTy IntTy) (Abs IntTy (
    IsZero (Var (IxZ _ _)) (Num 1)
           (Prim primMult (Var (IxZ _ _))
                 (App (Var (IxS _ (IxZ _ _)))
                      (Prim primMinus (Var (IxZ _ _)) (Num 1)))))))
