module Unname

import Data.Vect
import Index
import Ty
import Lambda
import NamedLambda
import FiniteMap

%default total

unnameXs' : (ns : Vect n Name) -> (ts : Vect n (Ty tn)) ->
    (xs : NVarArgs (multiExtend [] ns ts) t) -> VarArgs ts t
unnameXs' ns ts [] = []
unnameXs' ns ts (Cons x xs eq) = getIndex ns ts x eq :: unnameXs' ns ts xs

mutual
  unname' : (ns : Vect n Name) -> (ts : Vect n (Ty tn)) ->
      (e : NExpr (multiExtend [] ns ts) t) -> Expr ts t
  unname' ns ts (Var x eq) = Var (getIndex _ _ x eq)
  unname' ns ts (Num n) = Num n
  unname' ns ts (Prim f e1 e2) = Prim f (unname' ns ts e1) (unname' ns ts e2)
  unname' ns ts (IsZero e1 e2 e3) =
      IsZero (unname' ns ts e1) (unname' ns ts e2) (unname' ns ts e3)
  unname' ns ts (App e1 e2) = App (unname' ns ts e1) (unname' ns ts e2)
  unname' ns ts (Abs x t1 e) = Abs t1 (unname' (x :: ns) (t1 :: ts) e)
  unname' ns ts (Let x e1 e2) =
      Let (unname' ns ts e1) (unname' (x :: ns) (_ :: ts) e2)
  unname' ns ts (Fix e) = Fix (unname' ns ts e)
  unname' ns ts (Constr tag xs) = Constr tag (unnameXs' ns ts xs)
  unname' ns ts (Case e as) = Case (unname' ns ts e) (unnameAs' ns ts as)
  unname' ns ts (TyApp e t' eq) = TyApp (unname' ns ts e) t' eq
  unname' ns ts (TyAbs e) {t = ForallTy t} =
      let ep : NExpr (multiExtend [] ns (map (tyincr FZ) ts)) t =
          rewrite sym (mapMultiExtendEmpty (tyincr FZ) ns ts) in e
      in let small_ep = assert_smaller (TyAbs e) ep
      in TyAbs (unname' ns (map (tyincr FZ) ts) small_ep)
  unname' ns ts (Fold e) = Fold (unname' ns ts e)
  unname' ns ts (Unfold e eq) = Unfold (unname' ns ts e) eq

  unnameAs' : (ns : Vect n Name) -> (ts : Vect n (Ty tn)) ->
      (as : NAlts (multiExtend [] ns ts) ctrs t) -> Alts ts ctrs t
  unnameAs' ns ts Fail = Fail
  unnameAs' ns ts (Alt xs {ts = ts'} e as) =
      let ep : NExpr (multiExtend [] (xs ++ ns) (ts' ++ ts)) t =
          rewrite sym (multiExtendAppendEmpty ns ts xs ts') in e
      in let small_ep = assert_smaller (Alt xs {ts = ts'} e as) ep
      in Alt (unname' (xs ++ ns) (ts' ++ ts) small_ep) (unnameAs' ns ts as)

export
unname : NExpr [] t -> Expr [] t
unname e = unname' [] [] e
