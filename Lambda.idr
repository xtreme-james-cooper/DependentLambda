module Lambda

import Data.Vect
import Index

%default total

data Ty : Type where
  ArrowTy : Ty -> Ty -> Ty
  IntTy : Ty

data Expr : Vect n Ty -> Ty -> Type where
  Var : Index env t -> Expr env t
  Num : Int -> Expr env IntTy
  App : Expr env (ArrowTy t1 t2) -> Expr env t1 -> Expr env t2
  Abs : (t1 : Ty) -> Expr (t1 :: env) t2 -> Expr env (ArrowTy t1 t2)
  Let : Expr env t1 -> Expr (t1 :: env) t2 -> Expr env t2

{- evaluation -}

incr : (x : Fin (S n)) -> (tt : Ty) -> Expr env t -> Expr (insertAt x tt env) t
incr x tt (Var ix) = Var (indexInsert tt x ix)
incr x tt (Num n) = Num n
incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)
incr x tt (Let e1 e2) = Let (incr x tt e1) (incr (FS x) tt e2)

subst : (x : Fin (S n)) -> Expr env t' -> Expr (insertAt x t' env) t -> Expr env t
subst x e' (Var ix) {t' = t'} {env = env} with (compareFinToIndex x ix)
  subst x e' (Var ix) {t' = t'} {env = env} | Yes eq with (indexOfIndex x ix eq)
    subst x e' (Var ix) {t' = t'} {env = env} | Yes eq | Refl =
        rewrite indexInsertAt x t' env in e'
  subst x e' (Var ix) {t' = t'} {env = env} | No npf = Var (indexSubr _ x ix npf)
subst x e' (Num n) = Num n
subst x e' (App e1 e2) = App (subst x e' e1) (subst x e' e2)
subst x e' (Abs t1 e) = Abs t1 (subst (FS x) (incr FZ t1 e') e)
subst x e' (Let e1 e2) = Let (subst x e' e1) (subst (FS x) (incr FZ _ e') e2)

data IsValue : Expr env t -> Type where
  IntVal : IsValue (Num x)
  ArrowVal : IsValue (Abs t e)
  LetVal : IsValue e2 -> IsValue (Let e1 e2)

data IsVarHeaded : Expr env t -> Index env t' -> Type where
  VarVar : IsVarHeaded (Var ix) ix
  AppVar : IsVarHeaded e1 ix -> IsVarHeaded (App e1 e2) ix
  LetVarL : IsVarHeaded e2 (IxZ t1 env) -> IsVarHeaded e1 ix -> IsVarHeaded (Let e1 e2) ix
  LetVarR : IsVarHeaded e2 (IxS n as a b ix) -> IsVarHeaded (Let e1 e2) ix

data Eval : Expr env t -> Expr env t -> Type where
  EvApp1 : Eval e1 e1' -> Eval (App e1 e2) (App e1' e2)
  EvApp2 : Eval (App (Abs t1 e1) e2) (Let e2 e1)
  EvAppLet : IsValue e12 -> Eval (App (Let e11 e12) e2) (Let e11 (App e12 (incr FZ _ e2)))
  EvLet1 : Eval e2 e2' -> Eval (Let e1 e2) (Let e1 e2')
  EvLet2 : IsVarHeaded e2 (IxZ t env) -> Eval e1 e1' -> Eval (Let e1 e2) (Let e1' e2)
  EvLet3 : IsValue e1 -> Eval (Let e1 e2) (subst FZ e1 e2)

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
        Step (subst FZ e1 e2) (EvLet3 v)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | Step e1' ev =
        Step (Let e1' e2) (EvLet2 vh ev)
    progress' (Let e1 e2) | VarHeaded (IxZ t1 env) vh | VarHeaded ix vh' =
        VarHeaded ix (LetVarL vh vh')
  progress' (Let e1 e2) | VarHeaded (IxS n env t' t1 ix) vh =
      VarHeaded ix (LetVarR vh)

progress : (e : Expr [] t) -> Either (IsValue e) (e' ** Eval e e')
progress e with (progress' e)
  progress e | Value v = Left v
  progress e | Step e' ev = Right (e' ** ev)
  progress e | VarHeaded ix vh impossible
