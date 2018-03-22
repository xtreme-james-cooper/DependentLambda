module Evaluation

import Data.Vect
import Lambda
import Index
import VectHelper

%default total

data IsValue : Expr env t -> Type where
  IntVal : IsValue (Num x)
  ArrowVal : IsValue (Abs t e)
  DataVal : IsValue (Constr tag es)
  LetVal : IsValue e2 -> IsValue (Let e1 e2)
  LetrecVal : IsValue e -> IsValue (Letrec ts es e)

data IsVarHeaded : Expr env t -> Index env t' -> Type where
  VarVar : IsVarHeaded (Var ix) ix
  AppVar : IsVarHeaded e1 ix -> IsVarHeaded (App e1 e2) ix
  LetVarL : IsVarHeaded e2 (IxZ t1 env) -> IsVarHeaded e1 ix -> IsVarHeaded (Let e1 e2) ix
  LetVarR : IsVarHeaded e2 (IxS b ix) -> IsVarHeaded (Let e1 e2) ix
  LetrecVarR : IsVarHeaded e (indexLeftExtend ts ix) -> IsVarHeaded (Letrec ts es e) ix
  CaseVar : IsVarHeaded e ix -> IsVarHeaded (Case e as) ix

data AltEval : Fin n -> Exprs env ts -> Alts env ctrs t -> Expr env t -> Type where
  AltEvFZ : AltEval FZ es (Alt e as) (multisubst es e)
  AltEvFS : AltEval x es as e -> AltEval (FS x) es (Alt e' as) e

mutual
  data Eval : Expr env t -> Expr env t -> Type where
    EvApp1 : Eval e1 e1' -> Eval (App e1 e2) (App e1' e2)
    EvApp2 : Eval (App (Abs t1 e1) e2) (Let e2 e1)
    EvAppLet : IsValue e12 -> Eval (App (Let e11 e12) e2) (Let e11 (App e12 (incr FZ _ e2)))
    EvLet1 : Eval e2 e2' -> Eval (Let e1 e2) (Let e1 e2')
    EvLet2 : IsVarHeaded e2 (IxZ t env) -> Eval e1 e1' -> Eval (Let e1 e2) (Let e1' e2)
    EvLet3 : IsValue e1 -> Eval (Let e1 e2) (subst FZ e1 e2)
    EvLetrec1 : Eval e e' -> Eval (Letrec ts es e) (Letrec ts es e')
    EvLetrec2 : IsVarHeaded e (indexRightExtend ts ix) -> Evals ix es es' ->
        Eval (Letrec ts es e) (Letrec ts es' e)
    EvCase1 : Eval e e' -> Eval (Case e as) (Case e' as)
    EvCase2 : AltEval tag es as e -> Eval (Case (Constr tag es) as) e
    EvCaseLet : IsValue e2 -> Eval (Case (Let e1 e2) as) (Let e1 (Case e2 (incra FZ _ as)))

  data Evals : Index ts t -> Exprs env ts -> Exprs env ts -> Type where
    EvIxZ : Eval e e' -> Evals (IxZ t env) (e :: es) (e' :: es)
    EvIxS : Evals ix es es' -> Evals (IxS tt ix) (e :: es) (e :: es')

data Progress : Expr env t -> Type where
  Value : IsValue e -> Progress e
  Step : (e' : Expr env t) -> Eval e e' -> Progress e
  VarHeaded : (ix : Index env t') -> IsVarHeaded e ix -> Progress e

progress'a : {ctrs : Vect n (p ** Vect p Ty)} -> (tag : Fin n) ->
    (es : Exprs env (snd (index tag ctrs))) -> (as : Alts env ctrs t) -> (e ** AltEval tag es as e)
progress'a FZ es (Alt e as) = (multisubst es e ** AltEvFZ)
progress'a (FS tag) es (Alt e as) = case progress'a tag es as of
    (e' ** aev) => (e' ** AltEvFS aev)

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
        Step (subst FZ e1 e2) (EvLet3 v)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Step e1' ev =
        Step (Let e1' e2) (EvLet2 vh ev)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | VarHeaded ix vh' =
        VarHeaded ix (LetVarL vh vh')
  progress' (Let e1 e2) | VarHeaded (IxS t1 ix) vh = VarHeaded ix (LetVarR vh)
progress' {env = env} (Letrec ts es e) with (progress' e)
  progress' {env = env} (Letrec ts es e) | Value v = Value (LetrecVal v)
  progress' {env = env} (Letrec ts es e) | Step e' ev = Step (Letrec ts es e') (EvLetrec1 ev)
  progress' {env = env} (Letrec ts es e) | VarHeaded ix vh with (indexSplit ts ix)
    progress' {env = env} (Letrec ts es e) | VarHeaded _ vh | Left (ix' ** Refl) = ?athing
        --Step (Letrec ts es' e) (EvLetrec2 vh evs)
    progress' (Letrec ts es e) | VarHeaded _ vh | Right (ix' ** Refl) =
        VarHeaded ix' (LetrecVarR vh)
progress' {t = DataTy ctrs} (Constr tag es) = Value DataVal
progress' (Case e as) with (progress' e)
  progress' (Case (Constr tag es) as) | Value DataVal with (progress'a tag es as)
    progress' (Case (Constr tag es) as) | Value DataVal | (e ** ev) = Step e (EvCase2 ev)
  progress' (Case (Let e1 e2) as) | Value (LetVal v) =
      Step (Let e1 (Case e2 (incra FZ _ as))) (EvCaseLet v)
  progress' (Case e as) | Step e' ev = Step (Case e' as) (EvCase1 ev)
  progress' (Case e as) | VarHeaded ix vh = VarHeaded ix (CaseVar vh)

progress : (e : Expr [] t) -> Either (IsValue e) (e' ** Eval e e')
progress e with (progress' e)
  progress e | Value v = Left v
  progress e | Step e' ev = Right (e' ** ev)
  progress e | VarHeaded ix vh impossible

partial
evaluate : Expr [] t -> (e' : Expr [] t ** IsValue e')
evaluate e with (progress e)
  evaluate e | Left v = (e ** v)
  evaluate e | Right (e' ** ev) = evaluate e'
