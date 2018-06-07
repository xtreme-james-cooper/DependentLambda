module Stack.Stack

import public Lambda.LambdaOperations
import public Utils.Heap

%default total

public export
data Frame : (henv : Vect k (Ty tn)) -> (t' : Ty tn) -> (t : Ty tn) -> Type where
  SUpdate : (x : Fin k) -> index x henv = t -> Frame henv (index x henv) t
  SPrim1 : (Int -> Int -> Int) -> Expr henv IntTy -> Frame henv IntTy IntTy
  SPrim2 : (Int -> Int -> Int) -> Int -> Frame henv IntTy IntTy
  SIsZero : Expr henv t -> Expr henv t -> Frame henv IntTy t
  SApp : Expr henv t1 -> Frame henv (ArrowTy t1 t2) t2
  SFix : Frame henv (ArrowTy t t) t
  SCase : Alts henv ctrs t -> Frame henv (DataTy ctrs) t
  STyApp : (t' : Ty tn) -> tt = tsubst FZ t' t -> Frame henv (ForallTy t) tt
  SUnfold : tt = tsubst FZ (FixTy t) t -> Frame henv (FixTy t) tt

public export
data Stack : (henv : Vect k (Ty tn)) -> (t' : Ty tn) -> (t : Ty tn) -> Type where
  Nil : Stack henv t t
  (::) : Frame henv t1 t2 -> Stack henv t2 t3 -> Stack henv t1 t3

public export
data StackState : Ty tn -> Type where
  SEval : Heap k henv (Expr henv) -> Expr henv t1 -> Stack henv t1 t2 ->
      StackState t2
  SReturn : Heap k henv (Expr henv) -> (e : Expr henv t1) -> IsValue e ->
      Stack henv t1 t2 -> StackState t2

fIncr : (t3 : Ty tn) -> Frame henv t1 t2 -> Frame (t3 :: henv) t1 t2
fIncr t3 (SUpdate x eq) = SUpdate (FS x) eq
fIncr t3 (SPrim1 f e) = SPrim1 f (incr FZ t3 e)
fIncr t3 (SPrim2 f n) = SPrim2 f n
fIncr t3 (SIsZero e2 e3) = SIsZero (incr FZ t3 e2) (incr FZ t3 e3)
fIncr t3 (SApp e2) = SApp (incr FZ t3 e2)
fIncr t3 SFix = SFix
fIncr t3 (SCase as) = SCase (incra FZ t3 as)
fIncr t3 (STyApp t' eq) = STyApp t' eq
fIncr t3 (SUnfold eq) = SUnfold eq

export
sIncr : (t3 : Ty tn) -> Stack henv t1 t2 -> Stack (t3 :: henv) t1 t2
sIncr t3 [] = []
sIncr t3 (f :: fs) = fIncr t3 f :: sIncr t3 fs
