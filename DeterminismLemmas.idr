module DeterminismLemmas

import Evaluation
import Lambda
import LambdaOperations
import Data.Vect
import Index
import Ty

%default total

export
valSame : (v1 : IsValue e) -> (v2 : IsValue e) -> v1 = v2
valSame IntVal IntVal = Refl
valSame ArrowVal ArrowVal = Refl
valSame DataVal DataVal = Refl
valSame (LetVal v1) (LetVal v2) with (valSame v1 v2)
  valSame (LetVal v1) (LetVal v1) | Refl = Refl
valSame ForallVal ForallVal = Refl

export
valNotVarHeaded : IsValue e -> Not (IsVarHeaded e ix)
valNotVarHeaded IntVal vh impossible
valNotVarHeaded ArrowVal vh impossible
valNotVarHeaded DataVal vh impossible
valNotVarHeaded (LetVal v) (LetVarR vh2) = valNotVarHeaded v vh2
valNotVarHeaded (LetVal v) (LetVarL vh2 vh1) = valNotVarHeaded v vh2
valNotVarHeaded ForallVal vh impossible

mutual
  varHeadedSameIndex : {ix : Index as t'} -> {ix' : Index as t''} ->
      IsVarHeaded e ix -> IsVarHeaded e ix' -> ix = ix'
  varHeadedSameIndex VarVar VarVar = Refl
  varHeadedSameIndex (AppVar vh1) (AppVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (LetVarL vh12 vh11) (LetVarL vh22 vh21) = varHeadedSameIndex vh11 vh21
  varHeadedSameIndex (LetVarL vh12 vh11) (LetVarR vh22) = void (varHeadedDiff vh12 vh22)
  varHeadedSameIndex (LetVarR vh12) (LetVarR vh22) with (varHeadedSameIndex vh12 vh22)
    varHeadedSameIndex (LetVarR vh12) (LetVarR vh22) | Refl = Refl
  varHeadedSameIndex (LetVarR vh12) (LetVarL vh22 vh21) = void (varHeadedDiff vh22 vh12)
  varHeadedSameIndex (FixVar vh1) (FixVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (CaseVar vh1) (CaseVar vh2) = varHeadedSameIndex vh1 vh2
  varHeadedSameIndex (TyAppVar vh1) (TyAppVar vh2) = varHeadedSameIndex vh1 vh2

  varHeadedDiff : IsVarHeaded e (IxZ a as) -> Not (IsVarHeaded e (IxS a ix))
  varHeadedDiff vh1 vh2 with (varHeadedSameIndex vh1 vh2)
    varHeadedDiff vh1 vh2 | Refl impossible

export
varHeadedSame : (vh1 : IsVarHeaded e ix) -> (vh2 : IsVarHeaded e ix) -> vh1 = vh2
varHeadedSame VarVar VarVar = Refl
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

export
varHeadedNoEval : IsVarHeaded e ix -> Not (Eval e e')
varHeadedNoEval (AppVar vh) (EvApp1 ev) = varHeadedNoEval vh ev
varHeadedNoEval (AppVar vh) EvApp2 impossible
varHeadedNoEval (AppVar (LetVarL vh2 vh1)) (EvAppLet v) = valNotVarHeaded v vh2
varHeadedNoEval (AppVar (LetVarR vh2)) (EvAppLet v) = valNotVarHeaded v vh2
varHeadedNoEval (LetVarL vh2 vh1) (EvLet1 ev) = varHeadedNoEval vh2 ev
varHeadedNoEval (LetVarR vh2) (EvLet1 ev) = varHeadedNoEval vh2 ev
varHeadedNoEval (LetVarL vh2 vh1) (EvLet2 vh ev) = varHeadedNoEval vh1 ev
varHeadedNoEval (LetVarR vh2) (EvLet2 vh ev) = varHeadedDiff vh vh2
varHeadedNoEval (LetVarL vh2 vh1) (EvLet3 vh v) = valNotVarHeaded v vh1
varHeadedNoEval (LetVarR vh2) (EvLet3 vh v) = varHeadedDiff vh vh2
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

export
valNoEval : IsValue e -> Not (Eval e e')
valNoEval IntVal ev impossible
valNoEval ArrowVal ev impossible
valNoEval DataVal ev impossible
valNoEval (LetVal v1) (EvLet1 ev) = valNoEval v1 ev
valNoEval (LetVal v1) (EvLet2 vh ev) = valNotVarHeaded v1 vh
valNoEval (LetVal v1) (EvLet3 vh v2) = valNotVarHeaded v1 vh
valNoEval ForallVal ev impossible
