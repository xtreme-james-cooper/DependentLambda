module Stack.Evaluation.Evaluation

import public Stack.Stack
import public Lambda.LambdaOperations
import public Utils.Iterate

%default total

public export
data Eval : StackState t -> StackState t -> Type where
  -- EvVarE : {henv : HeapEnv k HeapEntry} -> {h : SHeap henv} -> {e : Expr env t} ->
  --     {lt : LT n k} -> index (finFromIndex ix) m = (n ** lt) ->
  --         hLookup h n lt = (e ** Nothing) ->
  --             Eval (SEval (Var ix) s m h) (SEval e (SUpdate n :: s) m h)
  -- EvVarR : {henv : HeapEnv k HeapEntry} -> {h : SHeap henv} -> {e : Expr env t} ->
  --     {lt : LT n k} -> index (finFromIndex ix) m = (n ** lt) ->
  --         hLookup h n lt = (e ** Just v) ->
  --             Eval (SEval (Var ix) s m h) (SReturn e v s m h)
  EvNum : Eval (SEval (Num n) s m h) (SReturn (Num n) IntVal s m h)
  EvPrim : Eval (SEval (Prim f e1 e2) s m h) (SEval e1 (SPrim1 f e2 :: s) m h)
  EvIsZero : Eval (SEval (IsZero e1 e2 e3) s m h) (SEval e1 (SIsZero e2 e3 :: s) m h)
  EvApp : Eval (SEval (App e1 e2) s m h) (SEval e1 (SApp e2 :: s) m h)
  EvAbs : Eval (SEval (Abs t1 e) s m h) (SReturn (Abs t1 e) ArrowVal s m h)
  -- EvLet
  EvFix : Eval (SEval (Fix e) s m h) (SEval e (SFix :: s) m h)
  EvConstr : Eval (SEval (Constr tag xs) s m h) (SReturn (Constr tag xs) DataVal s m h)
  EvCase : Eval (SEval (Case e as) s m h) (SEval e (SCase as :: s) m h)
  EvTyApp : Eval (SEval (TyApp e t' eq) s m h) (SEval e (STyApp t' eq :: s) m h)
  EvTyAbs : Eval (SEval (TyAbs e) s m h) (SReturn (TyAbs e) ForallVal s m h)
  EvFold : Eval (SEval (Fold e) s m h) (SReturn (Fold e) FixVal s m h)
  EvUnfold : Eval (SEval (Unfold e eq) s m h) (SEval e (SUnfold eq :: s) m h)

  -- RetUpdate : Eval (SReturn e v (SUpdate n lt :: s) m h)
  --     (SReturn e v s m (hUpdate h n lt (e ** Just v)))
  RetPrim1 : Eval (SReturn e1 v1 (SPrim1 f e2 :: s) m h)
      (SEval e2 (SPrim2 f e1 v1 :: s) m h)
  RetPrim2 : Eval (SReturn (Num n2) IntVal (SPrim2 f (Num n1) IntVal :: s) m h)
      (SReturn (Num (f n1 n2)) IntVal s m h)
  RetIsZeroZ : Eval (SReturn (Num 0) IntVal (SIsZero e2 e3 :: s) m h) (SEval e2 s m h)
  RetIsZeroS : Not (n = 0) ->
      Eval (SReturn (Num n) IntVal (SIsZero e2 e3 :: s) m h) (SEval e3 s m h)
  RetApp : Eval (SReturn (Abs t e1) ArrowVal (SApp e2 :: s) m h) (SEval (Let e2 e1) s m h)
  -- RetLet : Eval (SReturn e v (SLet n eq :: s) (k :: m) h) (SReturn e v s m h)
  RetFix : Eval (SReturn (Abs t e) ArrowVal (SFix :: s) m h)
      (SEval (Let (Fix (Abs t e)) e) s m h)
  RetCase : Eval (SReturn (Constr tag xs) DataVal (SCase as :: s) m h)
      (SEval (altEval tag as es) s m h)
  RetTyApp : Eval (SReturn (TyAbs e) ForallVal (STyApp t' eq :: s) m h)
      (SEval (tySubst t e) s m h)
  RetUnfold : Eval (SReturn (Fold e) FixVal (SUnfold eq :: s) m h) (SEval e s m h)

export
data IsComplete : StackState t -> Type where
  Complete : IsComplete (SReturn e v [] m h)

export
progress : (s : StackState t) -> Either (IsComplete s) (s' : StackState t ** Eval s s')
progress (SEval (Var ix) s m h) = ?argl_2
progress (SEval (Num n) s m h) = Right (SReturn (Num n) IntVal s m h ** EvNum)
progress (SEval (Prim f e1 e2) s m h) = Right (SEval e1 (SPrim1 f e2 :: s) m h ** EvPrim)
progress (SEval (IsZero e1 e2 e3) s m h) = Right (SEval e1 (SIsZero e2 e3 :: s) m h ** EvIsZero)
progress (SEval (App e1 e2) s m h) = Right (SEval e1 (SApp e2 :: s) m h ** EvApp)
progress (SEval (Abs t1 e) s m h) = Right (SReturn (Abs t1 e) ArrowVal s m h ** EvAbs)
progress (SEval (Let e1 e2) s m h) = ?argl_9
progress (SEval (Fix e) s m h) = Right (SEval e (SFix :: s) m h ** EvFix)
progress (SEval (Constr tag xs) s m h) = Right (SReturn (Constr tag xs) DataVal s m h ** EvConstr)
progress (SEval (Case e as) s m h) = Right (SEval e (SCase as :: s) m h ** EvCase)
progress (SEval (TyApp e t' eq) s m h) = Right (SEval e (STyApp t' eq :: s) m h ** EvTyApp)
progress (SEval (TyAbs e) s m h) = Right (SReturn (TyAbs e) ForallVal s m h ** EvTyAbs)
progress (SEval (Fold e) s m h) = Right (SReturn (Fold e) FixVal s m h ** EvFold)
progress (SEval (Unfold e eq) s m h) = Right (SEval e (SUnfold eq :: s) m h ** EvUnfold)
progress (SReturn e v [] m h) = Left Complete
progress (SReturn e v (SUpdate n lt :: s) m h) = ?argl_1
progress (SReturn e v (SPrim1 f e2 :: s) m h) = Right (SEval e2 (SPrim2 f e v :: s) m h ** RetPrim1)
progress (SReturn (Num n2) IntVal (SPrim2 f (Num n1) IntVal :: s) m h) =
    Right (SReturn (Num (f n1 n2)) IntVal s m h ** RetPrim2)
progress (SReturn (Num n) IntVal (SIsZero e2 e3 :: s) m h) with (decEq n 0)
  progress (SReturn (Num 0) IntVal (SIsZero e2 e3 :: s) m h) | Yes Refl =
      Right (SEval e2 s m h ** RetIsZeroZ)
  progress (SReturn (Num n) IntVal (SIsZero e2 e3 :: s) m h) | No neq =
      Right (SEval e3 s m h ** RetIsZeroS neq)
progress (SReturn (Abs t e1) ArrowVal (SApp e2 :: s) m h) =
    Right (SEval (Let e2 e1) s m h ** RetApp)
progress (SReturn e v (SLet n eq :: s) m h) = ?argl_8
progress (SReturn e v (SFix :: s) m h) = ?argl_10
progress (SReturn e v (SCase as :: s) m h) = ?argl_11
progress (SReturn e v (STyApp t' eq :: s) m h) = ?argl_12
progress (SReturn e v (SUnfold eq :: s) m h) = ?argl_13

partial export
evaluate : (s : StackState t) -> (s' : StackState t ** (Iterate Eval s s', IsComplete s'))
evaluate s with (progress s)
  evaluate s | Left c = (s ** ([], c))
  evaluate s | Right (s' ** ev) with (evaluate s')
    evaluate s | Right (s' ** ev) | (s'' ** (evs, c)) = (s'' ** (ev :: evs, c))
