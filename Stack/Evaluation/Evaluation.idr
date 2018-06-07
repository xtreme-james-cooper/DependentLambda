module Stack.Evaluation.Evaluation

import public Stack.Stack
import public Utils.Iterate

%default total

public export
data Eval : StackState t -> StackState t -> Type where
  EvVar : Eval (SEval h (Var ix) s) (SEval h (hLookup h (finFromIndex ix))
      (SUpdate (finFromIndex ix) (indexOfIndex (finFromIndex ix) ix Refl) :: s))
  EvNum : Eval (SEval h (Num n) s) (SReturn h (Num n) IntVal s)
  EvPrim : Eval (SEval h (Prim f e1 e2) s) (SEval h e1 (SPrim1 f e2 :: s))
  EvIsZero : Eval (SEval h (IsZero e1 e2 e3) s) (SEval h e1 (SIsZero e2 e3 :: s))
  EvApp : Eval (SEval h (App e1 e2) s) (SEval h e1 (SApp e2 :: s))
  EvAbs : Eval (SEval h (Abs t1 e) s) (SReturn h (Abs t1 e) ArrowVal s)
  EvLet : Eval (SEval h (Let e1 e2) s)
      (SEval (hMap (incr FZ _) (hAlloc h e1)) e2 (sIncr _ s))
  EvFix : Eval (SEval h (Fix e) s) (SEval h e (SFix :: s))
  EvConstr : Eval (SEval h (Constr tag xs) s) (SReturn h (Constr tag xs) DataVal s)
  EvCase : Eval (SEval h (Case e as) s) (SEval h e (SCase as :: s))
  EvTyApp : Eval (SEval h (TyApp e t' eq) s) (SEval h e (STyApp t' eq :: s))
  EvTyAbs : Eval (SEval h (TyAbs e) s) (SReturn h (TyAbs e) ForallVal s)
  EvFold : Eval (SEval h (Fold e) s) (SReturn h (Fold e) FixVal s)
  EvUnfold : Eval (SEval h (Unfold e eq) s) (SEval h e (SUnfold eq :: s))

  RetUpdate : Eval (SReturn h e v (SUpdate n eq :: s))
      (SReturn (hUpdate h n e) e v s)
  RetPrim1 : Eval (SReturn h (Num n1) IntVal (SPrim1 f e2 :: s))
      (SEval h e2 (SPrim2 f n1 :: s))
  RetPrim2 : Eval (SReturn h (Num n2) IntVal (SPrim2 f n1 :: s))
      (SReturn h (Num (f n1 n2)) IntVal s)
  RetIsZeroZ : Eval (SReturn h (Num 0) IntVal (SIsZero e2 e3 :: s))
      (SEval h e2 s)
  RetIsZeroS : Not (n = 0) ->
      Eval (SReturn h (Num n) IntVal (SIsZero e2 e3 :: s)) (SEval h e3 s)
  RetApp : Eval (SReturn h (Abs t e1) ArrowVal (SApp e2 :: s))
      (SEval h (Let e2 e1) s)
  RetFix : Eval (SReturn h (Abs t e) ArrowVal (SFix :: s))
      (SEval h (Let (Fix (Abs t e)) e) s)
  RetCase : Eval (SReturn h (Constr tag xs) DataVal (SCase as :: s))
      (SEval h (altEval tag as xs) s)
  RetTyApp : Eval (SReturn h (TyAbs e) ForallVal (STyApp t eq :: s))
      (SEval h (tySubst t e) s)
  RetUnfold : Eval (SReturn h (Fold e) FixVal (SUnfold eq :: s)) (SEval h e s)

export
data IsComplete : StackState t -> Type where
  Complete : IsComplete (SReturn h e v [])

export
progress : (s : StackState t) -> Either (IsComplete s) (s' : StackState t ** Eval s s')
progress (SEval h (Var ix) s) =
    Right (SEval h (hLookup h (finFromIndex ix))
        (SUpdate (finFromIndex ix) (indexOfIndex (finFromIndex ix) ix Refl) :: s)
            ** EvVar)
progress (SEval h (Num n) s) = Right (SReturn h (Num n) IntVal s ** EvNum)
progress (SEval h (Prim f e1 e2) s) =
    Right (SEval h e1 (SPrim1 f e2 :: s) ** EvPrim)
progress (SEval h (IsZero e1 e2 e3) s) =
    Right (SEval h e1 (SIsZero e2 e3 :: s) ** EvIsZero)
progress (SEval h (App e1 e2) s) = Right (SEval h e1 (SApp e2 :: s) ** EvApp)
progress (SEval h (Abs t1 e) s) =
    Right (SReturn h (Abs t1 e) ArrowVal s ** EvAbs)
progress (SEval h (Let e1 e2) s) =
    Right (SEval (hMap (incr FZ _) (hAlloc h e1)) e2 (sIncr _ s) ** EvLet)
progress (SEval h (Fix e) s) = Right (SEval h e (SFix :: s) ** EvFix)
progress (SEval h (Constr tag xs) s) =
    Right (SReturn h (Constr tag xs) DataVal s ** EvConstr)
progress (SEval h (Case e as) s) = Right (SEval h e (SCase as :: s) ** EvCase)
progress (SEval h (TyApp e t' eq) s) =
    Right (SEval h e (STyApp t' eq :: s) ** EvTyApp)
progress (SEval h (TyAbs e) s) =
    Right (SReturn h (TyAbs e) ForallVal s ** EvTyAbs)
progress (SEval h (Fold e) s) = Right (SReturn h (Fold e) FixVal s ** EvFold)
progress (SEval h (Unfold e eq) s) =
    Right (SEval h e (SUnfold eq :: s) ** EvUnfold)

progress (SReturn h e v []) = Left Complete

progress (SReturn h e v (SUpdate n Refl :: s)) =
    Right (SReturn (hUpdate h n e) e v s ** RetUpdate)
progress (SReturn h (Num n1) IntVal (SPrim1 f e2 :: s)) =
    Right (SEval h e2 (SPrim2 f n1 :: s) ** RetPrim1)
progress (SReturn h (Num n2) IntVal (SPrim2 f n1 :: s)) =
    Right (SReturn h (Num (f n1 n2)) IntVal s ** RetPrim2)
progress (SReturn h (Num n) IntVal (SIsZero e2 e3 :: s)) with (decEq n 0)
  progress (SReturn h (Num n) IntVal (SIsZero e2 e3 :: s)) | Yes eq =
      rewrite eq in Right (SEval h e2 s ** RetIsZeroZ)
  progress (SReturn h (Num n) IntVal (SIsZero e2 e3 :: s)) | No neq =
      Right (SEval h e3 s ** RetIsZeroS neq)
progress (SReturn h (Abs t e1) ArrowVal (SApp e2 :: s)) =
    Right (SEval h (Let e2 e1) s ** RetApp)
progress (SReturn h (Abs t e) ArrowVal (SFix :: s)) =
    Right (SEval h (Let (Fix (Abs t e)) e) s ** RetFix)
progress (SReturn h (Constr tag xs) DataVal (SCase as :: s)) =
    Right (SEval h (altEval tag as xs) s ** RetCase)
progress (SReturn h (TyAbs e) ForallVal (STyApp t' Refl :: s)) =
    Right (SEval h (tySubst t' e) s ** RetTyApp)
progress (SReturn h (Fold e) FixVal (SUnfold Refl :: s)) =
    Right (SEval h e s ** RetUnfold)

partial export
evaluate : (s : StackState t) -> (s' : StackState t ** (Iterate Eval s s', IsComplete s'))
evaluate s with (progress s)
  evaluate s | Left c = (s ** ([], c))
  evaluate s | Right (s' ** ev) with (evaluate s')
    evaluate s | Right (s' ** ev) | (s'' ** (evs, c)) = (s'' ** (ev :: evs, c))
