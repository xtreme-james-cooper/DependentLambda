module Stack.Stack

import public Lambda.Lambda
import public Utils.Heap

%default total

public export
data SValue : Vect n (Ty tn) -> Ty tn -> Type where
  IntVal : Int -> SValue env IntTy
  ArrowVal : (t1 : Ty tn) -> Expr (t1 :: env) t2 -> SValue env (ArrowTy t1 t2)
  DataVal : {ctrs : Vect m (n ** Vect n (Ty tn))} -> (tag : Fin m) ->
      VarArgs env (snd (index tag ctrs)) -> SValue env (DataTy ctrs)
  ForallVal : Expr (map (tyincr FZ) env) t -> SValue env (ForallTy t)
  FixVal : Expr env (tsubst FZ (FixTy t) t) -> SValue env (FixTy t)

export
devalue : SValue env t -> Expr env t
devalue (IntVal n) = Num n
devalue (ArrowVal t1 e) = Abs t1 e
devalue (DataVal tag xs) = Constr tag xs
devalue (ForallVal e) = TyAbs e
devalue (FixVal e) = Fold e

public export
data HeapEntry : Type where
  HeapE : Vect n (Ty tn) -> Ty tn -> HeapEntry

public export
exprOfHeapType : HeapEntry -> Type
exprOfHeapType (HeapE env t) = Expr env t

public export
SHeap : HeapEnv n HeapEntry -> Type
SHeap h = Heap h exprOfHeapType

public export
data Frame : HeapEnv m HeapEntry -> Vect n (Ty tn) -> Ty tn -> Ty tn -> Type where
  SUpdate : {h : HeapEnv m HeapEntry} -> (n : Nat) -> (lt : LT n m) ->
      h n lt = HeapE env t -> Frame h env t t
  SPrim1 : (Int -> Int -> Int) -> Expr env IntTy -> Frame h env IntTy IntTy
  SPrim2 : (Int -> Int -> Int) -> Int -> Frame h env IntTy IntTy
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
  SEval : {env : Vect n (Ty tn)} -> {henv : HeapEnv m HeapEntry} -> Expr env t1 ->
      Stack henv env t1 t2 -> Vect n (p ** LT p m) -> SHeap henv -> StackState t2
  SReturn : {env : Vect n (Ty tn)} -> {henv : HeapEnv m HeapEntry} ->
      SValue env t1 -> Stack henv env t1 t2 -> Vect n (p ** LT p m) -> SHeap henv ->
          StackState t2
