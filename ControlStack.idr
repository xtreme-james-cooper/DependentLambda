module ControlStack

import Evaluation
import Data.Vect
import Lambda
import Index

%default total

data Control : Vect n Ty -> Ty -> Ty -> Type where
  SEmpty : Control [] tt tt
  SApp : Expr env t1 -> Control env t2 tt -> Control env (ArrowTy t1 t2) tt
  SLet1 : Expr env t1 -> Control env t2 tt -> Control (t1 :: env) t2 tt
  SLet2 : Expr (t1 :: env) t2 -> Control env t2 tt -> Control env t1 tt
  SFix : Control env t tt -> Control env (ArrowTy t t) tt
  SCase : Alts env ctrs t -> Control env t tt -> Control env (DataTy ctrs) tt

ControlState : Vect n Ty -> Ty -> Ty -> Type
ControlState env t tt = (Expr env t, Control env t tt)

ControlIsValue : ControlState env t tt -> Type
ControlIsValue {tt = tt} (e, c) = (IsValue e, c = SEmpty {tt = tt})

data ControlEval : ControlState env t tt -> ControlState env' t' tt -> Type where
  CEApp1 : ControlEval (App e1 e2, c) (e1, SApp e2 c)
  CEApp2 : ControlEval (Abs t1 e1, SApp e2 c) (Let e2 e1, c)
  CEAppLet : IsValue e12 -> ControlEval (Let e11 e12, SApp e2 c) (e12, SApp (incr FZ _ e2) (SLet1 e11 c))
  CELet1 : ControlEval (Let e1 e2, c) (e2, SLet1 e1 c)
  CELet2 : IsVarHeaded e2 (IxZ t env) -> ControlEval (e2, SLet1 e1 c) (e1, SLet2 e2 c)
  CELet3 : IsValue e1 -> ControlEval (e1, SLet2 e2 c) (subst FZ e1 e2, c)
  CELet4 : IsValue e2 -> ControlEval (e2, SLet1 e1 c) (Let e1 e2, c)
  CEFix1 : ControlEval (Fix e, c) (e, SFix c)
  CEFix2 : IsValue e -> ControlEval (e, SFix c) (App e (Fix e), c)
  CECase1 : ControlEval (Case e as, c) (e, SCase as c)
  CECase2 : ControlEval (Constr tag es, SCase as c) (altEval tag as es, c)
  CECaseLet : IsValue e2 -> ControlEval (Let e1 e2, SCase as c) (e2, SCase (incra FZ _ as) (SLet1 e1 c))

progress : (c : ControlState env t tt) -> Either (ControlIsValue c) (c' ** ControlEval c c')
progress (Var ix, c) = ?progres_1
progress (Num n, SEmpty) = Left (IntVal, Refl)
progress (Num n, SLet1 e1 c) = Right ((Let e1 (Num n), c) ** CELet4 ?arl)
progress (Num n, SLet2 e2 c) = Right ((subst FZ (Num n) e2, c) ** CELet3 ?barl)
progress (App e1 e2, c) = ?progres_3
progress (Abs t1 e, c) = ?progres_4
progress (Let e1 e2, c) = ?progres_5
progress (Fix e, c) = ?progres_6
progress (Constr tag es, c) = ?progres_7
progress (Case e as, c) = ?progres_8
