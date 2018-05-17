module Stack.Stack

import public Lambda.Lambda
import public Utils.Heap

%default total

public export
data IsSValue : Expr env t -> Type where
  IntVal : IsSValue (Num n)
  ArrowVal : IsSValue (Abs t e)
  DataVal : IsSValue (Constr tag es)
  ForallVal : IsSValue (TyAbs e)
  FixVal : IsSValue (Fold e)

public export
data HeapEntry : Type where
  HeapE : Vect n (Ty tn) -> Ty tn -> HeapEntry

public export
SHeap : HeapEnv n HeapEntry -> Type
SHeap h = Heap h (\(HeapE env t) => (e : Expr env t ** Maybe (IsSValue e)))

public export
data Frame : HeapEnv m HeapEntry -> Vect n (Ty tn) -> Ty tn -> Ty tn -> Type where
  SUpdate : (n : Nat) -> LT n m -> Frame h env t t
  SPrim1 : (Int -> Int -> Int) -> Expr env IntTy -> Frame h env IntTy IntTy
  SPrim2 : (Int -> Int -> Int) -> (e1 : Expr env IntTy) -> IsSValue e1 ->
      Frame h env IntTy IntTy
  SIsZero : Expr env t -> Expr env t -> Frame h env IntTy t
  SApp : Expr env t1 -> Frame h env (ArrowTy t1 t2) t2
  SLet : (n : Nat) -> {h : HeapEnv m HeapEntry} ->
      h n lt = HeapE env t1 -> Frame h (t1 :: env) t2 t2
  SFix : Frame h env (ArrowTy t t) t
  SCase : Alts env ctrs t -> Frame h env (DataTy ctrs) t
  STyApp : (t' : Ty tn) -> tt = tsubst FZ t' t -> Frame h env (ForallTy t) tt
  SUnfold : tt = tsubst FZ (FixTy t) t -> Frame h env (FixTy t) tt

public export
data Stack : HeapEnv m HeapEntry -> Vect n (Ty tn) -> Ty tn -> Ty tn -> Type where
  Nil : Stack h [] t t
  (::) : Frame h env t1 t2 -> Stack h env t2 t3 -> Stack h env t1 t3

public export
data StackState : Ty tn -> Type where
  SEval : {env : Vect n (Ty tn)} -> {h : HeapEnv m HeapEntry} -> Expr env t1 ->
      Stack h env t1 t2 -> Vect n (p ** LT p m) -> SHeap h -> StackState t2
  SReturn : {env : Vect n (Ty tn)} -> {h : HeapEnv m HeapEntry} -> (e : Expr env t1) ->
      IsSValue e -> Stack h env t1 t2 -> Vect n (p ** LT p m) -> SHeap h -> StackState t2
