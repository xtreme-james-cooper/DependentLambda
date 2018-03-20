module Lambda

import Data.Vect
import Index

%default total

data Ty : Type where
  Arrow : Ty -> Ty -> Ty
  Base : Ty

data Expr : Vect n Ty -> Ty -> Type where
  Var : Index env t -> Expr env t
  Con : Expr env Base
  App : Expr env (Arrow t1 t2) -> Expr env t1 -> Expr env t2
  Abs : (t1 : Ty) -> Expr (t1 :: env) t2 -> Expr env (Arrow t1 t2)

{- evaluation -}

data IsValue : Expr env t -> Type where
  BaseVal : IsValue Con
  ArrowVal : IsValue (Abs t e)

incr : (x : Fin (S n)) -> (tt : Ty) -> Expr env t -> Expr (insertAt x tt env) t
incr x tt (Var ix) = Var (indexInsert tt x ix)
incr x tt Con = Con
incr x tt (App e1 e2) = App (incr x tt e1) (incr x tt e2)
incr x tt (Abs t1 e) = Abs t1 (incr (FS x) tt e)

subst : (x : Fin (S n)) -> Expr env t' -> Expr (insertAt x t' env) t -> Expr env t
subst x e' (Var ix) {t' = t'} {env = env} with (compareFinToIndex x ix)
  subst x e' (Var ix) {t' = t'} {env = env} | Yes eq with (indexOfIndex x ix eq)
    subst x e' (Var ix) {t' = t'} {env = env} | Yes eq | Refl =
        rewrite indexInsertAt x t' env in e'
  subst x e' (Var ix) {t' = t'} {env = env} | No npf = Var (indexSubr _ x ix npf)
subst x e' Con = Con
subst x e' (App e1 e2) = App (subst x e' e1) (subst x e' e2)
subst x e' (Abs t1 e) = Abs t1 (subst (FS x) (incr FZ t1 e') e)

data Eval : Expr [] t -> Expr [] t -> Type where
  EvApp1 : Eval e1 e1' -> Eval (App e1 e2) (App e1' e2)
  EvApp2 : IsValue e1 -> Eval e2 e2' -> Eval (App e1 e2) (App e1 e2')
  EvApp3 : IsValue e2 -> Eval (App (Abs t1 e1) e2) (subst 0 e2 e1)

progress : (e : Expr [] t) -> Either (IsValue e) (e' ** Eval e e')
progress (Var _) impossible
progress Con = Left BaseVal
progress (App e1 e2) with (progress e1)
  progress (App (Abs t1 e1') e2) | Left ArrowVal with (progress e2)
    progress (App (Abs t1 e1') e2) | Left ArrowVal | Left v2 =
        Right (subst 0 e2 e1' ** EvApp3 v2)
    progress (App (Abs t1 e1') e2) | Left ArrowVal | Right (e2' ** ev2) =
        Right (App (Abs t1 e1') e2' ** EvApp2 ArrowVal ev2)
  progress (App e1 e2) | Right (e1' ** ev1) = Right (App e1' e2 ** EvApp1 ev1)
progress (Abs t e) = Left ArrowVal
