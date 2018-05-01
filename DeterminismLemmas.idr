module DeterminismLemmas

import Evaluation
import Lambda
import LambdaOperations
import Data.Vect
import Index
import Ty

%default total

export
valNotVarHeaded : IsValue e b -> Not (IsVarHeaded e ix)
valNotVarHeaded IntVal vh impossible
valNotVarHeaded ArrowVal vh impossible
valNotVarHeaded DataVal vh impossible
valNotVarHeaded ForallVal vh impossible
valNotVarHeaded FixVal vh impossible
valNotVarHeaded (LetVal v npr) (LetVarR vh2) = valNotVarHeaded v vh2
valNotVarHeaded (LetVal v npr) (LetVarL vh2 vh1) = valNotVarHeaded v vh2

mutual
  varHeadedSameIndex : {ix : Index as t'} -> {ix' : Index as t''} ->
      IsVarHeaded e ix -> IsVarHeaded e ix' -> ix = ix'
  varHeadedSameIndex VarVar VarVar = Refl
  varHeadedSameIndex (PrimVarL vh1) (PrimVarL vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (PrimVarL vh1) (PrimVarR vh2) = void (valNotVarHeaded IntVal vh1)
  varHeadedSameIndex (PrimVarR vh1) (PrimVarL vh2) = void (valNotVarHeaded IntVal vh2)
  varHeadedSameIndex (PrimVarR vh1) (PrimVarR vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (IsZeroVar vh1) (IsZeroVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (AppVar vh1) (AppVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (LetVarL vh12 vh11) (LetVarL vh22 vh21) = varHeadedSameIndex vh11 vh21
  varHeadedSameIndex (LetVarL vh12 vh11) (LetVarR vh22) = void (varHeadedDiff vh12 vh22)
  varHeadedSameIndex (LetVarR vh12) (LetVarR vh22) with (varHeadedSameIndex vh12 vh22)
    varHeadedSameIndex (LetVarR vh12) (LetVarR vh22) | Refl = Refl
  varHeadedSameIndex (LetVarR vh12) (LetVarL vh22 vh21) = void (varHeadedDiff vh22 vh12)
  varHeadedSameIndex (FixVar vh1) (FixVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (CaseVar vh1) (CaseVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (TyAppVar vh1) (TyAppVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (UnfoldVar vh1) (UnfoldVar vh2) = varHeadedSameIndex vh1 vh2

  varHeadedDiff : IsVarHeaded e (IxZ a as) -> Not (IsVarHeaded e (IxS a ix))
  varHeadedDiff vh1 vh2 with (varHeadedSameIndex vh1 vh2)
    varHeadedDiff vh1 vh2 | Refl impossible

export
varHeadedSame : (vh1 : IsVarHeaded e ix) -> (vh2 : IsVarHeaded e ix) -> vh1 = vh2
varHeadedSame VarVar VarVar = Refl
varHeadedSame (PrimVarL vh1) (PrimVarL vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (PrimVarL vh1) (PrimVarL vh1) | Refl = Refl
varHeadedSame (PrimVarL vh1) (PrimVarR vh2) = void (valNotVarHeaded IntVal vh1)
varHeadedSame (PrimVarR vh1) (PrimVarL vh2) = void (valNotVarHeaded IntVal vh2)
varHeadedSame (PrimVarR vh1) (PrimVarR vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (PrimVarR vh1) (PrimVarR vh1) | Refl = Refl
varHeadedSame (IsZeroVar vh1) (IsZeroVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (IsZeroVar vh1) (IsZeroVar vh1) | Refl = Refl
varHeadedSame (AppVar vh1) (AppVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (AppVar vh1) (AppVar vh1) | Refl = Refl
varHeadedSame (LetVarL vh12 vh11) (LetVarL vh22 vh21) with (varHeadedSame vh11 vh21, varHeadedSame vh12 vh22)
  varHeadedSame (LetVarL vh12 vh11) (LetVarL vh12 vh11) | (Refl, Refl) = Refl
varHeadedSame (LetVarL vh12 vh11) (LetVarR vh22) = void (varHeadedDiff vh12 vh22)
varHeadedSame (LetVarR vh12) (LetVarL vh22 vh21) = void (varHeadedDiff vh22 vh12)
varHeadedSame (LetVarR vh12) (LetVarR vh22) with (varHeadedSame vh12 vh22)
  varHeadedSame (LetVarR vh12) (LetVarR vh12) | Refl = Refl
varHeadedSame (FixVar vh1) (FixVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (FixVar vh1) (FixVar vh1) | Refl = Refl
varHeadedSame (CaseVar vh1) (CaseVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (CaseVar vh1) (CaseVar vh1) | Refl = Refl
varHeadedSame (TyAppVar vh1) (TyAppVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (TyAppVar vh1) (TyAppVar vh1) | Refl = Refl
varHeadedSame (UnfoldVar vh1) (UnfoldVar vh2) with (varHeadedSame vh1 vh2)
  varHeadedSame (UnfoldVar vh1) (UnfoldVar vh1) | Refl = Refl

mutual
  export
  varHeadedNoEval : IsVarHeaded e ix -> Not (Eval e e')
  varHeadedNoEval (PrimVarL vh) (EvPrim1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (PrimVarL vh) (EvPrim2 ev) = valNotVarHeaded IntVal vh
  varHeadedNoEval (PrimVarL vh) EvPrim3 impossible
  varHeadedNoEval (PrimVarL (LetVarL vh2 vh1)) (EvPrimLetL v1 npr) = valNotVarHeaded v1 vh2
  varHeadedNoEval (PrimVarL (LetVarR vh2)) (EvPrimLetL v1 npr) = valNotVarHeaded v1 vh2
  varHeadedNoEval (PrimVarL vh) (EvPrimLetR v2 npr) impossible
  varHeadedNoEval (PrimVarR vh) (EvPrim1 ev) = valNoEval IntVal ev
  varHeadedNoEval (PrimVarR vh) (EvPrim2 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (PrimVarR vh) EvPrim3 impossible
  varHeadedNoEval (PrimVarR vh) (EvPrimLetL v1 npr) impossible
  varHeadedNoEval (PrimVarR (LetVarL vh2 vh1)) (EvPrimLetR v2 npr) = valNotVarHeaded v2 vh2
  varHeadedNoEval (PrimVarR (LetVarR vh2)) (EvPrimLetR v2 npr) = valNotVarHeaded v2 vh2
  varHeadedNoEval (IsZeroVar vh) (EvIsZero1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (IsZeroVar vh) EvIsZero2 impossible
  varHeadedNoEval (IsZeroVar vh) (EvIsZero3 neq) impossible
  varHeadedNoEval (IsZeroVar (LetVarL vh2 vh1)) (EvIsZeroLet v npr) = valNotVarHeaded v vh2
  varHeadedNoEval (IsZeroVar (LetVarR vh2)) (EvIsZeroLet v npr) = valNotVarHeaded v vh2
  varHeadedNoEval (AppVar vh) (EvApp1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (AppVar vh) EvApp2 impossible
  varHeadedNoEval (AppVar (LetVarL vh2 vh1)) (EvAppLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (AppVar (LetVarR vh2)) (EvAppLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (LetVarL vh2 vh1) (EvLet1 ev) = varHeadedNoEval vh2 ev
  varHeadedNoEval (LetVarL vh2 vh1) (EvLet2 vh ev) = varHeadedNoEval vh1 ev
  varHeadedNoEval (LetVarL vh2 vh1) (EvLet3 vh v npr) = valNotVarHeaded v vh1
  varHeadedNoEval (LetVarL vh2 (LetVarL vh12 vh11)) (EvLetLet vh v npr) = valNotVarHeaded v vh12
  varHeadedNoEval (LetVarL vh2 (LetVarR vh12)) (EvLetLet vh v npr) = valNotVarHeaded v vh12
  varHeadedNoEval (LetVarR vh2) (EvLet1 ev) = varHeadedNoEval vh2 ev
  varHeadedNoEval (LetVarR vh2) (EvLet2 vh ev) = varHeadedDiff vh vh2
  varHeadedNoEval (LetVarR vh2) (EvLet3 vh v npr) = varHeadedDiff vh vh2
  varHeadedNoEval (LetVarR vh2) (EvLetLet vh v npr) = varHeadedDiff vh vh2
  varHeadedNoEval (FixVar vh) (EvFix1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (FixVar vh) EvFix2 impossible
  varHeadedNoEval (FixVar (LetVarL vh2 vh1)) (EvFixLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (FixVar (LetVarR vh2)) (EvFixLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (CaseVar vh) (EvCase1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (CaseVar vh) EvCase2 impossible
  varHeadedNoEval (CaseVar (LetVarL vh2 vh1)) (EvCaseLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (CaseVar (LetVarR vh2)) (EvCaseLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (TyAppVar vh) (EvTyApp1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (TyAppVar vh) EvTyApp2 impossible
  varHeadedNoEval (TyAppVar (LetVarL vh2 vh1)) (EvTyAppLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (TyAppVar (LetVarR vh2)) (EvTyAppLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (UnfoldVar vh) (EvUnfold1 ev) = varHeadedNoEval vh ev
  varHeadedNoEval (UnfoldVar vh) EvUnfold2 impossible
  varHeadedNoEval (UnfoldVar (LetVarL vh2 vh1)) (EvUnfoldLet v) = valNotVarHeaded v vh2
  varHeadedNoEval (UnfoldVar (LetVarR vh2)) (EvUnfoldLet v) = valNotVarHeaded v vh2

  export
  valNoEval : IsValue e b -> Not (Eval e e')
  valNoEval IntVal ev impossible
  valNoEval ArrowVal ev impossible
  valNoEval DataVal ev impossible
  valNoEval ForallVal ev impossible
  valNoEval FixVal ev impossible
  valNoEval (LetVal v1 npr) (EvLet1 ev) = valNoEval v1 ev
  valNoEval (LetVal v1 npr) (EvLet2 vh ev) = valNotVarHeaded v1 vh
  valNoEval (LetVal v1 npr) (EvLet3 vh v2 npr') = valNotVarHeaded v1 vh
  valNoEval (LetVal v1 npr) (EvLetLet vh v2 npr') = valNotVarHeaded v1 vh
  valNoEval (LetVal IntVal npr) EvLetGC = npr Refl

export
arrowNotPrim : {e : Expr env (ArrowTy t1 t2)} -> IsValue e b -> Not (b = PrimValTy)
arrowNotPrim {e = Abs t1 e} ArrowVal Refl impossible
arrowNotPrim {e = Let e1 e2} (LetVal v npr) Refl impossible

export
constrNotPrim : {e : Expr env (DataTy ctrs)} -> IsValue e b -> Not (b = PrimValTy)
constrNotPrim {e = Constr tag es} ConstrVal Refl impossible
constrNotPrim {e = Let e1 e2} (LetVal v npr) Refl impossible

export
forallNotPrim : {e : Expr env (ForallTy t)} -> IsValue e b -> Not (b = PrimValTy)
forallNotPrim {e = TyAbs e} ConstrVal Refl impossible
forallNotPrim {e = Let e1 e2} (LetVal v npr) Refl impossible

export
fixNotPrim : {e : Expr env (FixTy t)} -> IsValue e b -> Not (b = PrimValTy)
fixNotPrim {e = Fold e} FixVal Refl impossible
fixNotPrim {e = Let e1 e2} (LetVal v npr) Refl impossible
