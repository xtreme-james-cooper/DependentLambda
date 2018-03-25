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

data ControlState : Ty -> Type where
  CtSt : Expr env t -> Control env t tt -> ControlState tt

ControlIsValue : ControlState t -> Type
ControlIsValue (CtSt e c) = (IsValue e, c = SEmpty {tt = t})

data ControlEval : ControlState t -> ControlState t -> Type where
  CEApp1 : ControlEval (CtSt (App e1 e2) c) (CtSt e1 (SApp e2 c))
  CEApp2 : ControlEval (CtSt (Abs t1 e1) (SApp e2 c)) (CtSt e1 (SLet1 e2 c))
--  CEAppLet : IsValue e12 ->
--      ControlEval (CtSt (Let e11 e12) (SApp e2 c)) (CtSt e12 (SApp (incr FZ _ e2) (SLet1 e11 c)))
  CELet1 : Not (IsValue e2) -> ControlEval (CtSt (Let e1 e2) c) (CtSt e2 (SLet1 e1 c))
--  CELet2 : IsVarHeaded e2 (IxZ t env) -> ControlEval (CtSt e2 (SLet1 e1 c)) (CtSt e1 (SLet2 e2 c))
  CELet3 : IsValue e1 -> ControlEval (CtSt e1 (SLet2 e2 c)) (CtSt (subst FZ e1 e2) c)
  CELet4 : IsValue e2 -> ControlEval (CtSt e2 (SLet1 e1 c)) (CtSt (Let e1 e2) c)
  CEFix1 : ControlEval (CtSt (Fix e) c) (CtSt e (SFix c))
--  CEFix2 : IsValue e -> ControlEval (CtSt e (SFix c)) (CtSt (App e (Fix e)) c)
  CECase1 : ControlEval (CtSt (Case e as) c) (CtSt e (SCase as c))
  CECase2 : ControlEval (CtSt (Constr tag es) (SCase as c)) (CtSt (altEval tag as es) c)
--  CECaseLet : IsValue e2 ->
--      ControlEval (CtSt (Let e1 e2) (SCase as c)) (CtSt e2 (SCase (incra FZ _ as) (SLet1 e1 c)))

progress : (c : ControlState t) -> Either (ControlIsValue c) (c' ** ControlEval c c')
progress (CtSt (Var ix) c) = ?progres_1
progress {t = IntTy} (CtSt (Num n) SEmpty) = Left (IntVal, Refl)
progress (CtSt (Num n) (SLet1 e1 c)) =
    Right (CtSt (Let e1 (Num n)) c ** CELet4 IntVal)
progress (CtSt (Num n) (SLet2 e2 c)) =
    Right (CtSt (subst FZ (Num n) e2) c ** CELet3 IntVal)
progress (CtSt (App e1 e2) c) = Right (CtSt e1 (SApp e2 c) ** CEApp1)
progress {t = ArrowTy t1 t2} (CtSt (Abs t1 e) SEmpty) = Left (ArrowVal, Refl)
progress (CtSt (Abs t1 e) (SApp e2 c)) = Right (CtSt e (SLet1 e2 c) **  CEApp2)
progress (CtSt (Abs t1 e) (SLet1 e1 c)) =
    Right (CtSt (Let e1 (Abs t1 e)) c ** CELet4 ArrowVal)
progress (CtSt (Abs t1 e) (SLet2 e2 c)) =
    Right (CtSt (subst FZ (Abs t1 e) e2) c ** CELet3 ArrowVal)
progress (CtSt (Abs t1 e) (SFix c)) = ?progres_45
progress (CtSt (Let e1 e2) c) = Right (CtSt e2 (SLet1 e1 c) ** CELet1 ?v)
progress (CtSt (Fix e) c) = Right (CtSt e (SFix c) ** CEFix1)
progress {t = DataTy ctrs} (CtSt (Constr tag es) SEmpty) = Left (DataVal, Refl)
progress (CtSt (Constr tag es) (SLet1 e1 c)) =
    Right (CtSt (Let e1 (Constr tag es)) c ** CELet4 DataVal)
progress (CtSt (Constr tag es) (SLet2 e2 c)) =
    Right (CtSt (subst FZ (Constr tag es) e2) c ** CELet3 DataVal)
progress (CtSt (Constr tag es) (SCase as c)) =
    Right (CtSt (altEval tag as es) c ** CECase2)
progress (CtSt (Case e as) c) = Right (CtSt e (SCase as c) ** CECase1)
