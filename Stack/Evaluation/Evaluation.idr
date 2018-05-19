module Stack.Evaluation.Evaluation

import public Stack.Stack
import public Lambda.LambdaOperations
import public Utils.Iterate

%default total

public export
data Eval : StackState t -> StackState t -> Type where
  EvVar : {henv : HeapEnv k HeapEntry} -> {h : SHeap henv} -> {e : Expr env t} ->
      {m : Vect q (p ** LT p k)} -> {lt : LT n k} ->
          index (finFromIndex ix) m = (n ** lt) -> hLookup h n lt = e ->
              Eval (SEval (Var ix) s m h) (SEval e (SUpdate n lt pff :: s) m h)
  EvNum : Eval (SEval (Num n) s m h) (SReturn (IntVal n) s m h)
  EvPrim : Eval (SEval (Prim f e1 e2) s m h) (SEval e1 (SPrim1 f e2 :: s) m h)
  EvIsZero : Eval (SEval (IsZero e1 e2 e3) s m h) (SEval e1 (SIsZero e2 e3 :: s) m h)
  EvApp : Eval (SEval (App e1 e2) s m h) (SEval e1 (SApp e2 :: s) m h)
  EvAbs : Eval (SEval (Abs t1 e) s m h) (SReturn (ArrowVal t1 e) s m h)
  -- EvLet
  EvFix : Eval (SEval (Fix e) s m h) (SEval e (SFix :: s) m h)
  EvConstr : Eval (SEval (Constr tag xs) s m h) (SReturn (DataVal tag xs) s m h)
  EvCase : Eval (SEval (Case e as) s m h) (SEval e (SCase as :: s) m h)
  EvTyApp : Eval (SEval (TyApp e t' eq) s m h) (SEval e (STyApp t' eq :: s) m h)
  EvTyAbs : Eval (SEval (TyAbs e) s m h) (SReturn (ForallVal e) s m h)
  EvFold : Eval (SEval (Fold e) s m h) (SReturn (FixVal e) s m h)
  EvUnfold : Eval (SEval (Unfold e eq) s m h) (SEval e (SUnfold eq :: s) m h)

  RetUpdate : Eval (SReturn v (SUpdate n lt eq :: s) m h)
      (SReturn v s m (hUpdate h n lt e))
  RetPrim1 : Eval (SReturn (IntVal n1) (SPrim1 f e2 :: s) m h)
      (SEval e2 (SPrim2 f n1 :: s) m h)
  RetPrim2 : Eval (SReturn (IntVal n2) (SPrim2 f n1 :: s) m h)
      (SReturn (IntVal (f n1 n2)) s m h)
  RetIsZeroZ : Eval (SReturn (IntVal 0) (SIsZero e2 e3 :: s) m h) (SEval e2 s m h)
  RetIsZeroS : Not (n = 0) ->
      Eval (SReturn (IntVal n) (SIsZero e2 e3 :: s) m h) (SEval e3 s m h)
  RetApp : Eval (SReturn (ArrowVal t e1) (SApp e2 :: s) m h) (SEval (Let e2 e1) s m h)
  -- RetLet : Eval (SReturn e v (SLet n eq :: s) (k :: m) h) (SReturn e v s m h)
  RetFix : Eval (SReturn (ArrowVal t e) (SFix :: s) m h)
      (SEval (Let (Fix (Abs t e)) e) s m h)
  RetCase : Eval (SReturn (DataVal tag xs) (SCase as :: s) m h)
      (SEval (altEval tag as es) s m h)
  RetTyApp : Eval (SReturn (ForallVal e) (STyApp t' eq :: s) m h)
      (SEval (tySubst t e) s m h)
  RetUnfold : Eval (SReturn (FixVal e) (SUnfold eq :: s) m h) (SEval e s m h)

export
data IsComplete : StackState t -> Type where
  Complete : IsComplete (SReturn v [] m h)

export
progress : (s : StackState t) -> Either (IsComplete s) (s' : StackState t ** Eval s s')
progress (SEval (Var ix) s m h) with (index (finFromIndex ix) m)
  progress (SEval (Var ix) s m h) | (n ** lt) with (hLookup h n lt)
    progress (SEval (Var ix) s m h) | (n ** lt) | e =
        Right ?arcl --(SEval e (SUpdate n lt ?pff :: s) m h ** ?argl_2)

    -- EvVar : {henv : HeapEnv k HeapEntry} -> {h : SHeap henv} -> {e : Expr env t} ->
    --     {m : Vect q (p ** LT p k)} -> {lt : LT n k} ->
    --         index (finFromIndex ix) m = (n ** lt) -> hLookup h n lt = e ->
    --             Eval (SEval (Var ix) s m h) (SEval e (SUpdate n lt pff :: s) m h)

progress (SEval (Num n) s m h) =
    Right (SReturn (IntVal n) s m h ** EvNum)
progress (SEval (Prim f e1 e2) s m h) =
    Right (SEval e1 (SPrim1 f e2 :: s) m h ** EvPrim)
progress (SEval (IsZero e1 e2 e3) s m h) =
    Right (SEval e1 (SIsZero e2 e3 :: s) m h ** EvIsZero)
progress (SEval (App e1 e2) s m h) =
    Right (SEval e1 (SApp e2 :: s) m h ** EvApp)
progress (SEval (Abs t1 e) s m h) =
    Right (SReturn (ArrowVal t1 e) s m h ** EvAbs)
progress (SEval (Let e1 e2) s m h) = ?argl_9
progress (SEval (Fix e) s m h) =
    Right (SEval e (SFix :: s) m h ** EvFix)
progress (SEval (Constr tag xs) s m h) =
    Right (SReturn (DataVal tag xs) s m h ** EvConstr)
progress (SEval (Case e as) s m h) =
    Right (SEval e (SCase as :: s) m h ** EvCase)
progress (SEval (TyApp e t' eq) s m h) =
    Right (SEval e (STyApp t' eq :: s) m h ** EvTyApp)
progress (SEval (TyAbs e) s m h) =
    Right (SReturn (ForallVal e) s m h ** EvTyAbs)
progress (SEval (Fold e) s m h) =
    Right (SReturn (FixVal e) s m h ** EvFold)
progress (SEval (Unfold e eq) s m h) =
    Right (SEval e (SUnfold eq :: s) m h ** EvUnfold)
progress (SReturn v [] m h) = Left Complete
progress (SReturn {henv = henv} v (SUpdate n lt eq :: s) m h) =
    Right (SReturn v s m (hUpdate {henv = henv} h n lt (rewrite eq in devalue v)) ** RetUpdate)
progress (SReturn (IntVal n1) (SPrim1 f e2 :: s) m h) =
    Right (SEval e2 (SPrim2 f n1 :: s) m h ** RetPrim1)
progress (SReturn (IntVal n2) (SPrim2 f n1 :: s) m h) =
    Right (SReturn (IntVal (f n1 n2)) s m h ** RetPrim2)
progress (SReturn (IntVal n) (SIsZero e2 e3 :: s) m h) with (decEq n 0)
  progress (SReturn (IntVal 0) (SIsZero e2 e3 :: s) m h) | Yes Refl =
      Right (SEval e2 s m h ** RetIsZeroZ)
  progress (SReturn (IntVal n) (SIsZero e2 e3 :: s) m h) | No neq =
      Right (SEval e3 s m h ** RetIsZeroS neq)
progress (SReturn (ArrowVal t e1) (SApp e2 :: s) m h) =
    Right (SEval (Let e2 e1) s m h ** RetApp)
progress (SReturn v (SLet n eq :: s) m h) = ?argl_8
progress (SReturn (ArrowVal t e) (SFix :: s) m h) =
    Right (SEval (Let (Fix (Abs t e)) e) s m h ** RetFix)
progress (SReturn (DataVal tag xs) (SCase as :: s) m h) =
    Right (SEval (altEval tag as xs) s m h ** RetCase)
progress (SReturn (ForallVal e) (STyApp t' Refl :: s) m h) =
    Right (SEval (tySubst t' e) s m h ** RetTyApp)
progress (SReturn (FixVal e) (SUnfold Refl :: s) m h) =
    Right (SEval e s m h ** RetUnfold)

partial export
evaluate : (s : StackState t) -> (s' : StackState t ** (Iterate Eval s s', IsComplete s'))
evaluate s with (progress s)
  evaluate s | Left c = (s ** ([], c))
  evaluate s | Right (s' ** ev) with (evaluate s')
    evaluate s | Right (s' ** ev) | (s'' ** (evs, c)) = (s'' ** (ev :: evs, c))
