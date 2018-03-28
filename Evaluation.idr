module Evaluation

import Data.Vect
import Lambda
import LambdaOperations
import Index
import VectHelper
import Iterate

%default total

public export
data Eval : Expr env t -> Expr env t -> Type where
  EvApp1 : Eval e1 e1' -> Eval (App e1 e2) (App e1' e2)
  EvApp2 : Eval (App (Abs t1 e1) e2) (Let e2 e1)
  EvAppLet : IsValue e12 -> Eval (App (Let e11 e12) e2) (Let e11 (App e12 (incr FZ _ e2)))
  EvLet1 : Eval e2 e2' -> Eval (Let e1 e2) (Let e1 e2')
  EvLet2 : IsVarHeaded e2 (IxZ t env) -> Eval e1 e1' -> Eval (Let e1 e2) (Let e1' e2)
  EvLet3 : (vh : IsVarHeaded e2 (IxZ t env)) -> (v : IsValue e1) ->
      Eval (Let e1 e2) (fst (subst e1 e2 v vh))
  EvFix1 : Eval e e' -> Eval (Fix e) (Fix e')
  EvFix2 : Eval (Fix (Abs t1 e1)) (subst FZ (Fix (Abs t1 e1)) e1)
  EvFixLet : IsValue e2 -> Eval (Fix (Let e1 e2)) (Let e1 (Fix e2))
  EvCase1 : Eval e e' -> Eval (Case e as) (Case e' as)
  EvCase2 : Eval (Case (Constr tag es) as) (altEval tag as es)
  EvCaseLet : IsValue e2 -> Eval (Case (Let e1 e2) as) (Let e1 (Case e2 (incra FZ _ as)))

data Progress : Expr env t -> Type where
  Value : IsValue e -> Progress e
  Step : (e' : Expr env t) -> Eval e e' -> Progress e
  VarHeaded : (ix : Index env t') -> IsVarHeaded e ix -> Progress e

progress' : (e : Expr env t) -> Progress e
progress' (Var ix) = VarHeaded ix VarVar
progress' {t = IntTy} (Num n) = Value IntVal
progress' (App e1 e2) with (progress' e1)
  progress' (App (Abs t1 e1) e2) | Value ArrowVal = Step (Let e2 e1) EvApp2
  progress' (App (Let e11 e12) e2) | Value (LetVal v) =
      Step (Let e11 (App e12 (incr FZ _ e2))) (EvAppLet v)
  progress' (App e1 e2) | Step e1' ev = Step (App e1' e2) (EvApp1 ev)
  progress' (App e1 e2) | VarHeaded ix vh = VarHeaded ix (AppVar vh)
progress' (Abs t e) = Value ArrowVal
progress' (Let e1 e2) with (progress' e2)
  progress' (Let e1 e2) | Value v = Value (LetVal v)
  progress' (Let e1 e2) | Step e2' ev = Step (Let e1 e2') (EvLet1 ev)
  progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh with (progress' e1)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Value v =
        Step (sharingSubst FZ v e2) (EvLet3 vh v)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Step e1' ev =
        Step (Let e1' e2) (EvLet2 vh ev)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | VarHeaded ix vh' =
        VarHeaded ix (LetVarL vh vh')
  progress' (Let e1 e2) | VarHeaded (IxS t1 ix) vh = VarHeaded ix (LetVarR vh)
progress' (Fix e) with (progress' e)
  progress' (Fix (Abs t e)) | Value ArrowVal =
      Step (subst FZ (Fix (Abs t e)) e) EvFix2
  progress' (Fix (Let e1 e2)) | Value (LetVal v) =
      Step (Let e1 (Fix e2)) (EvFixLet v)
  progress' (Fix e) | Step e' ev = Step (Fix e') (EvFix1 ev)
  progress' (Fix e) | VarHeaded ix vh = VarHeaded ix (FixVar vh)
progress' {t = DataTy ctrs} (Constr tag es) = Value DataVal
progress' (Case e as) with (progress' e)
  progress' (Case (Constr tag es) as) | Value DataVal =
      Step (altEval tag as es) EvCase2
  progress' (Case (Let e1 e2) as) | Value (LetVal v) =
      Step (Let e1 (Case e2 (incra FZ _ as))) (EvCaseLet v)
  progress' (Case e as) | Step e' ev = Step (Case e' as) (EvCase1 ev)
  progress' (Case e as) | VarHeaded ix vh = VarHeaded ix (CaseVar vh)

export
progress : (e : Expr [] t) -> Either (IsValue e) (e' ** Eval e e')
progress e with (progress' e)
  progress e | Value v = Left v
  progress e | Step e' ev = Right (e' ** ev)
  progress e | VarHeaded ix vh impossible

export partial
evaluate : (e : Expr [] t) -> (e' : Expr [] t ** (Iterate Eval e e', IsValue e'))
evaluate e with (progress e)
  evaluate e | Left v = (e ** (IterRefl, v))
  evaluate e | Right (e' ** ev) with (evaluate e')
    evaluate e | Right (e' ** ev) | (e'' ** (evs, v)) = (e'' ** (IterStep ev evs, v))
