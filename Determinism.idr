module Determinism

import Evaluation
import Lambda
import LambdaOperations
import Data.Vect
import Index
import Ty
import DeterminismLemmas

%default total

deterministicEval : Eval e e' -> Eval e e'' -> e' = e''
deterministicEval (EvApp1 ev1) (EvApp1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvApp1 ev1) EvApp2 = void (valNoEval ArrowVal ev1)
deterministicEval (EvApp1 (EvLet1 ev1)) (EvAppLet v2) = void (valNoEval v2 ev1)
deterministicEval (EvApp1 (EvLet2 vh1 ev1)) (EvAppLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval (EvApp1 (EvLet3 vh1 v1)) (EvAppLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval EvApp2 (EvApp1 ev2) = void (valNoEval ArrowVal ev2)
deterministicEval EvApp2 EvApp2 = Refl
deterministicEval (EvAppLet v1) (EvApp1 (EvLet1 ev2)) = void (valNoEval v1 ev2)
deterministicEval (EvAppLet v1) (EvApp1 (EvLet2 vh2 ev2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvAppLet v1) (EvApp1 (EvLet3 vh2 v2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvAppLet v1) (EvAppLet v2) = Refl
deterministicEval (EvLet1 ev1) (EvLet1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvLet1 ev1) (EvLet2 vh2 ev2) = void (varHeadedNoEval vh2 ev1)
deterministicEval (EvLet1 ev1) (EvLet3 vh2 v2) = void (varHeadedNoEval vh2 ev1)
deterministicEval (EvLet2 vh1 ev1) (EvLet1 ev2) = void (varHeadedNoEval vh1 ev2)
deterministicEval (EvLet2 vh1 ev1) (EvLet2 vh2 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvLet2 vh1 ev1) (EvLet3 vh2 v2) = void (valNoEval v2 ev1)
deterministicEval (EvLet3 vh1 v1) (EvLet1 ev2) = void (varHeadedNoEval vh1 ev2)
deterministicEval (EvLet3 vh1 v1) (EvLet2 vh2 ev2) = void (valNoEval v1 ev2)
deterministicEval (EvLet3 vh1 v1) (EvLet3 vh2 v2) =
    rewrite valSame v1 v2 in rewrite varHeadedSame vh1 vh2 in Refl
deterministicEval (EvFix1 ev1) (EvFix1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvFix1 ev1) EvFix2 = void (valNoEval ArrowVal ev1)
deterministicEval (EvFix1 (EvLet1 ev1)) (EvFixLet v2) = void (valNoEval v2 ev1)
deterministicEval (EvFix1 (EvLet2 vh1 ev1)) (EvFixLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval (EvFix1 (EvLet3 vh1 v1)) (EvFixLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval EvFix2 (EvFix1 ev2) = void (valNoEval ArrowVal ev2)
deterministicEval EvFix2 EvFix2 = Refl
deterministicEval (EvFixLet v1) (EvFix1 (EvLet1 ev2)) = void (valNoEval v1 ev2)
deterministicEval (EvFixLet v1) (EvFix1 (EvLet2 vh2 ev2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvFixLet v1) (EvFix1 (EvLet3 vh2 v2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvFixLet v1) (EvFixLet v2) = Refl
deterministicEval (EvCase1 ev1) (EvCase1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvCase1 ev1) EvCase2 = void (valNoEval DataVal ev1)
deterministicEval (EvCase1 (EvLet1 ev1)) (EvCaseLet v2) = void (valNoEval v2 ev1)
deterministicEval (EvCase1 (EvLet2 vh1 ev1)) (EvCaseLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval (EvCase1 (EvLet3 vh1 v1)) (EvCaseLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval EvCase2 (EvCase1 ev2) = void (valNoEval DataVal ev2)
deterministicEval EvCase2 EvCase2 = Refl
deterministicEval (EvCaseLet v1) (EvCase1 (EvLet1 ev2)) = void (valNoEval v1 ev2)
deterministicEval (EvCaseLet v1) (EvCase1 (EvLet2 vh2 ev2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvCaseLet v1) (EvCase1 (EvLet3 vh2 v2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvCaseLet v1) (EvCaseLet v2) = Refl
deterministicEval (EvTyApp1 ev1) (EvTyApp1 ev2) = rewrite deterministicEval ev1 ev2 in Refl
deterministicEval (EvTyApp1 ev1) EvTyApp2 = void (valNoEval ForallVal ev1)
deterministicEval (EvTyApp1 (EvLet1 ev1)) (EvTyAppLet v2) = void (valNoEval v2 ev1)
deterministicEval (EvTyApp1 (EvLet2 vh1 ev1)) (EvTyAppLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval (EvTyApp1 (EvLet3 vh1 v1)) (EvTyAppLet v2) = void (valNotVarHeaded v2 vh1)
deterministicEval EvTyApp2 (EvTyApp1 ev2) = void (valNoEval ForallVal ev2)
deterministicEval EvTyApp2 EvTyApp2 = Refl
deterministicEval (EvTyAppLet v1) (EvTyApp1 (EvLet1 ev2)) = void (valNoEval v1 ev2)
deterministicEval (EvTyAppLet v1) (EvTyApp1 (EvLet2 vh2 ev2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvTyAppLet v1) (EvTyApp1 (EvLet3 vh2 v2)) = void (valNotVarHeaded v1 vh2)
deterministicEval (EvTyAppLet v1) (EvTyAppLet v2) = Refl
