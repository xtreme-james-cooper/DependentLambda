module Determinism

import Evaluation
import Lambda
import LambdaOperations
import Values
import Data.Vect
import Index
import Ty
import DeterminismLemmas

%default total

deterministicEval : Eval e e' -> Eval e e'' -> e' = e''
deterministicEval (EvPrim1 ev1) (EvPrim1 ev2) =
    rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvPrim1 ev1) (EvPrim2 ev22) = void (valNoEval IntVal ev1)
deterministicEval (EvPrim1 ev1) EvPrim3 = void (valNoEval IntVal ev1)
deterministicEval (EvPrim1 ev1) (EvPrimLetL v22 npr) = void (valNoEval (LetVal v22 npr) ev1)
deterministicEval (EvPrim1 ev1) (EvPrimLetR v22 npr) = void (valNoEval IntVal ev1)
deterministicEval (EvPrim2 ev12) (EvPrim1 ev2) = void (valNoEval IntVal ev2)
deterministicEval (EvPrim2 ev12) (EvPrim2 ev22) = rewrite deterministicEval ev12 ev22 in Refl
deterministicEval (EvPrim2 ev12) EvPrim3 = void (valNoEval IntVal ev12)
deterministicEval (EvPrim2 ev12) (EvPrimLetL v22 npr) impossible
deterministicEval (EvPrim2 ev12) (EvPrimLetR v22 npr) = void (valNoEval (LetVal v22 npr) ev12)
deterministicEval EvPrim3 (EvPrim1 ev2) = void (valNoEval IntVal ev2)
deterministicEval EvPrim3 (EvPrim2 ev22) = void (valNoEval IntVal ev22)
deterministicEval EvPrim3 EvPrim3 = Refl
deterministicEval (EvPrimLetL v12 npr) (EvPrim1 ev2) = void (valNoEval (LetVal v12 npr) ev2)
deterministicEval (EvPrimLetL v12 npr) (EvPrim2 ev22) impossible
deterministicEval (EvPrimLetL v12 npr) (EvPrimLetL v22 npr') = Refl
deterministicEval (EvPrimLetR v12 npr) (EvPrim1 ev2) = void (valNoEval IntVal ev2)
deterministicEval (EvPrimLetR v12 npr) (EvPrim2 ev22) = void (valNoEval (LetVal v12 npr) ev22)
deterministicEval (EvPrimLetR v12 npr) (EvPrimLetR v22 npr') = Refl
deterministicEval (EvIsZero1 ev1) (EvIsZero1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvIsZero1 ev1) EvIsZero2 = void (valNoEval IntVal ev1)
deterministicEval (EvIsZero1 ev1) (EvIsZero3 neq) = void (valNoEval IntVal ev1)
deterministicEval (EvIsZero1 ev1) (EvIsZeroLet v npr) = void (valNoEval (LetVal v npr) ev1)
deterministicEval EvIsZero2 (EvIsZero1 ev2) = void (valNoEval IntVal ev2)
deterministicEval EvIsZero2 EvIsZero2 = Refl
deterministicEval EvIsZero2 (EvIsZero3 neq) = void (neq Refl)
deterministicEval (EvIsZero3 neq) (EvIsZero1 ev2) = void (valNoEval IntVal ev2)
deterministicEval (EvIsZero3 neq) EvIsZero2 = void (neq Refl)
deterministicEval (EvIsZero3 neq) (EvIsZero3 neq2) = Refl
deterministicEval (EvIsZeroLet v npr) (EvIsZero1 ev2) = void (valNoEval (LetVal v npr) ev2)
deterministicEval (EvIsZeroLet v npr) (EvIsZeroLet v2 npr') = Refl
deterministicEval (EvApp1 ev1) (EvApp1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvApp1 ev1) EvApp2 = void (valNoEval ArrowVal ev1)
deterministicEval (EvApp1 ev1) (EvAppLet v2) = void (valNoEval (LetVal v2 (arrowNotPrim v2)) ev1)
deterministicEval EvApp2 (EvApp1 ev2) = void (valNoEval ArrowVal ev2)
deterministicEval EvApp2 EvApp2 = Refl
deterministicEval (EvAppLet v1) (EvApp1 ev2) = void (valNoEval (LetVal v1 (arrowNotPrim v1)) ev2)
deterministicEval (EvAppLet v1) (EvAppLet v2) = Refl
deterministicEval (EvLet1 ev1) (EvLet1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvLet1 ev1) (EvLet2 vh2 ev2) = void (varHeadedNoEval vh2 ev1)
deterministicEval (EvLet1 ev1) (EvLet3 vh2 v2 neq) = void (varHeadedNoEval vh2 ev1)
deterministicEval (EvLet1 ev1) (EvLetLet vh2 v2 npr) = void (varHeadedNoEval vh2 ev1)
deterministicEval (EvLet1 ev1) EvLetGC = void (valNoEval IntVal ev1)
deterministicEval (EvLet2 vh1 ev1) (EvLet1 ev2) = void (varHeadedNoEval vh1 ev2)
deterministicEval (EvLet2 vh1 ev1) (EvLet2 vh2 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvLet2 vh1 ev1) (EvLet3 vh2 v2 neq) = void (valNoEval v2 ev1)
deterministicEval (EvLet2 vh1 ev1) (EvLetLet vh2 v2 npr) = void (valNoEval (LetVal v2 npr) ev1)
deterministicEval (EvLet2 vh1 ev1) EvLetGC = void (valNotVarHeaded IntVal vh1)
deterministicEval (EvLet3 vh1 v1 neq) (EvLet1 ev2) = void (varHeadedNoEval vh1 ev2)
deterministicEval (EvLet3 vh1 v1 neq) (EvLet2 vh2 ev2) = void (valNoEval v1 ev2)
deterministicEval (EvLet3 vh1 v1 neq) (EvLet3 vh2 v2 neq') = rewrite varHeadedSame vh1 vh2 in Refl
deterministicEval (EvLet3 vh1 (LetVal v1 npr) neq) (EvLetLet vh2 v2 npr') = void (neq Refl)
deterministicEval (EvLet3 vh1 v1 neq) EvLetGC impossible
deterministicEval (EvLetLet vh11 v12 npr) (EvLet1 ev2) = void (varHeadedNoEval vh11 ev2)
deterministicEval (EvLetLet vh11 v12 npr) (EvLet2 vh21 ev21) = void (valNoEval (LetVal v12 npr) ev21)
deterministicEval (EvLetLet vh11 v12 npr) (EvLet3 vh22 (LetVal v22 npr') neq) = void (neq Refl)
deterministicEval (EvLetLet vh11 v12 npr) (EvLetLet vh22 v22 npr') = Refl
deterministicEval (EvLetLet vh11 v12 npr) EvLetGC impossible
deterministicEval EvLetGC (EvLet1 ev2) = void (valNoEval IntVal ev2)
deterministicEval EvLetGC (EvLet2 vh21 ev21) = void (valNotVarHeaded IntVal vh21)
deterministicEval EvLetGC (EvLet3 vh22 v22 neq) = void (valNotVarHeaded IntVal vh22)
deterministicEval EvLetGC (EvLetLet vh22 v22 npr) = void (valNotVarHeaded IntVal vh22)
deterministicEval EvLetGC EvLetGC = Refl
deterministicEval (EvFix1 ev1) (EvFix1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvFix1 ev1) EvFix2 = void (valNoEval ArrowVal ev1)
deterministicEval (EvFix1 ev1) (EvFixLet v2) = void (valNoEval (LetVal v2 (arrowNotPrim v2)) ev1)
deterministicEval EvFix2 (EvFix1 ev2) = void (valNoEval ArrowVal ev2)
deterministicEval EvFix2 EvFix2 = Refl
deterministicEval (EvFixLet v1) (EvFix1 ev2) = void (valNoEval (LetVal v1 (arrowNotPrim v1)) ev2)
deterministicEval (EvFixLet v1) (EvFixLet v2) = Refl
deterministicEval (EvCase1 ev1) (EvCase1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvCase1 ev1) EvCase2 = void (valNoEval DataVal ev1)
deterministicEval (EvCase1 ev1) (EvCaseLet v2) = void (valNoEval (LetVal v2 (constrNotPrim v2)) ev1)
deterministicEval EvCase2 (EvCase1 ev2) = void (valNoEval DataVal ev2)
deterministicEval EvCase2 EvCase2 = Refl
deterministicEval (EvCaseLet v1) (EvCase1 ev2) = void (valNoEval (LetVal v1 (constrNotPrim v1)) ev2)
deterministicEval (EvCaseLet v1) (EvCaseLet v2) = Refl
deterministicEval (EvTyApp1 ev1) (EvTyApp1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvTyApp1 ev1) EvTyApp2 = void (valNoEval ForallVal ev1)
deterministicEval (EvTyApp1 ev1) (EvTyAppLet v2) = void (valNoEval (LetVal v2 (forallNotPrim v2)) ev1)
deterministicEval EvTyApp2 (EvTyApp1 ev2) = void (valNoEval ForallVal ev2)
deterministicEval EvTyApp2 EvTyApp2 = Refl
deterministicEval (EvTyAppLet v1) (EvTyApp1 ev2) = void (valNoEval (LetVal v1 (forallNotPrim v1)) ev2)
deterministicEval (EvTyAppLet v1) (EvTyAppLet v2) = Refl
deterministicEval (EvUnfold1 ev1) (EvUnfold1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvUnfold1 ev1) EvUnfold2 = void (valNoEval FixVal ev1)
deterministicEval (EvUnfold1 ev1) (EvUnfoldLet v2) = void (valNoEval (LetVal v2 (fixNotPrim v2)) ev1)
deterministicEval EvUnfold2 (EvUnfold1 ev2) = void (valNoEval FixVal ev2)
deterministicEval EvUnfold2 EvUnfold2 = Refl
deterministicEval (EvUnfoldLet v1) (EvUnfold1 ev2) = void (valNoEval (LetVal v1 (fixNotPrim v1)) ev2)
deterministicEval (EvUnfoldLet v1) (EvUnfoldLet v2) = Refl
