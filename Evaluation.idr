module Evaluation

import Data.Vect
import Lambda
import LambdaOperations
import Index
import VectHelper
import Iterate
import Ty

%default total

public export
data Eval : Expr env t -> Expr env t -> Type where
  EvPrim1 : Eval e1 e1' -> Eval (Prim f e1 e2) (Prim f e1' e2)
  EvPrim2 : Eval e2 e2' -> Eval (Prim f (Num n1) e2) (Prim f (Num n1) e2')
  EvPrim3 : Eval (Prim f (Num n1) (Num n2)) (Num (f n1 n2))
  EvPrimLetL : IsValue e12 b -> Not (b = PrimValTy) ->
      Eval (Prim f (Let e11 e12) e2) (Let e11 (Prim f e12 (incr FZ _ e2)))
  EvPrimLetR : IsValue e22 b -> Not (b = PrimValTy) ->
      Eval (Prim f (Num n1) (Let e21 e22)) (Let e21 (Prim f (incr FZ _ (Num n1)) e22))
  EvIsZero1 : Eval e1 e1' -> Eval (IsZero e1 e2 e3) (IsZero e1' e2 e3)
  EvIsZero2 : Eval (IsZero (Num 0) e2 e3) e2
  EvIsZero3 : Not (n = 0) -> Eval (IsZero (Num n) e2 e3) e3
  EvIsZeroLet : IsValue e12 b -> Not (b = PrimValTy) ->
      Eval (IsZero (Let e11 e12) e2 e3) (Let e11 (IsZero e12 (incr FZ _ e2) (incr FZ _ e3)))
  EvApp1 : Eval e1 e1' -> Eval (App e1 e2) (App e1' e2)
  EvApp2 : Eval (App (Abs t1 e1) e2) (Let e2 e1)
  EvAppLet : IsValue e12 b ->
      Eval (App (Let e11 e12) e2) (Let e11 (App e12 (incr FZ _ e2)))
  EvLet1 : Eval e2 e2' -> Eval (Let e1 e2) (Let e1 e2')
  EvLet2 : IsVarHeaded e2 (IxZ t env) -> Eval e1 e1' -> Eval (Let e1 e2) (Let e1' e2)
  EvLet3 : (vh : IsVarHeaded e2 (IxZ t env)) -> (v : IsValue e1 b) -> (nlt : Not (b = LetValTy)) ->
      Eval (Let e1 e2) (Let e1 (subst (incr FZ _ e1) e2 vh))
  EvLetLet : (vh : IsVarHeaded e2 (IxZ t env)) -> (v : IsValue e12 b) ->
      (npr : Not (b = PrimValTy)) ->
          Eval (Let (Let e11 e12) e2) (Let e11 (Let e12 (incr (FS FZ) _ e2)))
  EvLetGC : Eval (Let e1 (Num n)) (Num n)
  EvFix1 : Eval e e' -> Eval (Fix e) (Fix e')
  EvFix2 : Eval (Fix (Abs t1 e1)) (Let (Fix (Abs t1 e1)) e1)
  EvFixLet : IsValue e2 b -> Eval (Fix (Let e1 e2)) (Let e1 (Fix e2))
  EvCase1 : Eval e e' -> Eval (Case e as) (Case e' as)
  EvCase2 : Eval (Case (Constr tag es) as) (altEval tag as es)
  EvCaseLet : IsValue e2 b -> Eval (Case (Let e1 e2) as) (Let e1 (Case e2 (incra FZ _ as)))
  EvTyApp1 : Eval e e' -> Eval (TyApp e t eq) (TyApp e' t eq)
  EvTyApp2 : Eval (TyApp (TyAbs e) t eq) (tySubst t e)
  EvTyAppLet : IsValue e2 b -> Eval (TyApp (Let e1 e2) t eq) (Let e1 (TyApp e2 t eq))

data Progress : Expr env t -> Type where
  Value : IsValue e b -> Progress e
  Step : (e' : Expr env t) -> Eval e e' -> Progress e
  VarHeaded : (ix : Index env t') -> IsVarHeaded e ix -> Progress e

progress' : (e : Expr env t) -> Progress e
progress' (Var ix) = VarHeaded ix VarVar
progress' {t = IntTy} (Num n) = Value IntVal
progress' {t = IntTy} (Prim f e1 e2) with (progress' e1)
  progress' {t = IntTy} (Prim f (Num n1) e2) | Value IntVal with (progress' e2)
    progress' {t = IntTy} (Prim f (Num n1) (Num n2)) | Value IntVal | Value IntVal =
        Step (Num (f n1 n2)) EvPrim3
    progress' {t = IntTy} (Prim f (Num n1) (Let e21 e22)) | Value IntVal | Value (LetVal v2 npr) =
        Step (Let e21 (Prim f (incr FZ _ (Num n1)) e22)) (EvPrimLetR v2 npr)
    progress' {t = IntTy} (Prim f (Num n1) e2) | Value IntVal | Step e2' ev =
        Step (Prim f (Num n1) e2') (EvPrim2 ev)
    progress' {t = IntTy} (Prim f (Num n1) e2) | Value IntVal | VarHeaded ix vh =
        VarHeaded ix (PrimVarR vh)
  progress' {t = IntTy} (Prim f (Let e11 e12) e2) | Value (LetVal v npr) =
      Step (Let e11 (Prim f e12 (incr FZ _ e2))) (EvPrimLetL v npr)
  progress' {t = IntTy} (Prim f e1 e2) | Step e1' ev =
      Step (Prim f e1' e2) (EvPrim1 ev)
  progress' {t = IntTy} (Prim f e1 e2) | VarHeaded ix vh =
      VarHeaded ix (PrimVarL vh)
progress' (IsZero e1 e2 e3) with (progress' e1)
  progress' (IsZero (Num n) e2 e3) | Value IntVal with (decEq n 0)
    progress' (IsZero (Num n) e2 e3) | Value IntVal | Yes eq =
        Step e2 (rewrite eq in EvIsZero2)
    progress' (IsZero (Num n) e2 e3) | Value IntVal | No neq = Step e3 (EvIsZero3 neq)
  progress' (IsZero (Let e11 e12) e2 e3) | Value (LetVal v npr) =
      Step (Let e11 (IsZero e12 (incr FZ _ e2) (incr FZ _ e3))) (EvIsZeroLet v npr)
  progress' (IsZero e1 e2 e3) | Step e1' ev = Step (IsZero e1' e2 e3) (EvIsZero1 ev)
  progress' (IsZero e1 e2 e3) | VarHeaded ix vh = VarHeaded ix (IsZeroVar vh)
progress' (App e1 e2) with (progress' e1)
  progress' (App (Abs t1 e1) e2) | Value ArrowVal = Step (Let e2 e1) EvApp2
  progress' (App (Let e11 e12) e2) | Value (LetVal v npr) =
      Step (Let e11 (App e12 (incr FZ _ e2))) (EvAppLet v)
  progress' (App e1 e2) | Step e1' ev = Step (App e1' e2) (EvApp1 ev)
  progress' (App e1 e2) | VarHeaded ix vh = VarHeaded ix (AppVar vh)
progress' (Abs t e) = Value ArrowVal
progress' (Let e1 e2) with (progress' e2)
  progress' (Let e1 (Num n)) | Value {b = PrimValTy} IntVal = Step (Num n) EvLetGC
  progress' (Let e1 e2) | Value {b = StructValTy} v = Value (LetVal v (\(Refl) impossible))
  progress' (Let e1 e2) | Value {b = LetValTy} v = Value (LetVal v (\(Refl) impossible))
  progress' (Let e1 e2) | Step e2' ev = Step (Let e1 e2') (EvLet1 ev)
  progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh with (progress' e1)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Value {b = PrimValTy} v =
        Step (Let e1 (subst (incr FZ _ e1) e2 vh)) (EvLet3 vh v (\(Refl) impossible))
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Value {b = StructValTy} v =
        Step (Let e1 (subst (incr FZ _ e1) e2 vh)) (EvLet3 vh v (\(Refl) impossible))
    progress' (Let (Let e11 e12) e2) | VarHeaded (IxZ t1 env) vh | Value {b = LetValTy} (LetVal v npr) =
        Step (Let e11 (Let e12 (incr (FS FZ) _ e2))) (EvLetLet vh v npr)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Step e1' ev =
        Step (Let e1' e2) (EvLet2 vh ev)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | VarHeaded ix vh' =
        VarHeaded ix (LetVarL vh vh')
  progress' (Let e1 e2) | VarHeaded (IxS t1 ix) vh = VarHeaded ix (LetVarR vh)
progress' (Fix e) with (progress' e)
  progress' (Fix (Abs t e)) | Value ArrowVal =
      Step (Let (Fix (Abs t e)) e) EvFix2
  progress' (Fix (Let e1 e2)) | Value (LetVal v npr) =
      Step (Let e1 (Fix e2)) (EvFixLet v)
  progress' (Fix e) | Step e' ev = Step (Fix e') (EvFix1 ev)
  progress' (Fix e) | VarHeaded ix vh = VarHeaded ix (FixVar vh)
progress' {t = DataTy ctrs} (Constr tag es) = Value DataVal
progress' (Case e as) with (progress' e)
  progress' (Case (Constr tag es) as) | Value DataVal =
      Step (altEval tag as es) EvCase2
  progress' (Case (Let e1 e2) as) | Value (LetVal v npr) =
      Step (Let e1 (Case e2 (incra FZ _ as))) (EvCaseLet v)
  progress' (Case e as) | Step e' ev = Step (Case e' as) (EvCase1 ev)
  progress' (Case e as) | VarHeaded ix vh = VarHeaded ix (CaseVar vh)
progress' (TyApp e t eq) with (progress' e)
  progress' (TyApp (Let e1 e2) t eq) | Value (LetVal v npr) =
      Step (Let e1 (TyApp e2 t eq)) (EvTyAppLet v)
  progress' (TyApp (TyAbs e) t Refl) | Value ForallVal =
      Step (tySubst t e) EvTyApp2
  progress' (TyApp e t eq) | Step e' ev = Step (TyApp e' t eq) (EvTyApp1 ev)
  progress' (TyApp e t eq) | VarHeaded ix vh = VarHeaded ix (TyAppVar vh)
progress' {t = ForallTy t} (TyAbs e) = Value ForallVal


export
progress : (e : Expr [] t) -> Either (b ** IsValue e b) (e' ** Eval e e')
progress e with (progress' e)
  progress e | Value {b = b} v = Left (b ** v)
  progress e | Step e' ev = Right (e' ** ev)
  progress e | VarHeaded ix vh impossible

export partial
evaluate : {t : Ty 0} -> (e : Expr [] t) -> (b ** e' ** (Iterate Eval e e', IsValue e' b))
evaluate e with (progress e)
  evaluate e | Left (b ** v) = (b ** e ** ([], v))
  evaluate e | Right (e' ** ev) with (evaluate e')
    evaluate e | Right (e' ** ev) | (b ** e'' ** (evs, v)) =
        (b ** e'' ** (ev :: evs, v))
