module Examples

import Data.Vect
import Index
import Ty
import Lambda
import Evaluation
import Iterate

%default total

-- fact = fix (\fact: Int-> Int. \x: Int. isZ x 1 (x * (fact (x - 1))))
fact : Expr [] (ArrowTy IntTy IntTy)
fact = Fix (Abs (ArrowTy IntTy IntTy) (Abs IntTy (
    IsZero (Var (IxZ _ _)) (Num 1)
           (Prim (*) (Var (IxZ _ _))
                 (App (Var (IxS _ (IxZ _ _)))
                      (Prim (-) (Var (IxZ _ _)) (Num 1)))))))
