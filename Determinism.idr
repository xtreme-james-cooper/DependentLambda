module Determinism

import Evaluation
import Lambda
import Data.Vect
import Index

valNotVarHeaded : IsValue e -> Not (IsVarHeaded e ix)
valNotVarHeaded IntVal vh impossible
valNotVarHeaded ArrowVal vh impossible
valNotVarHeaded DataVal vh impossible
valNotVarHeaded (LetVal v) (LetVarR vh2) = valNotVarHeaded v vh2
valNotVarHeaded (LetVal v) (LetVarL vh2 vh1) = valNotVarHeaded v vh2

varHeadedSame : IsVarHeaded e ix -> IsVarHeaded e ix' -> ix = ix'
varHeadedSame VarVar VarVar = Refl
varHeadedSame (AppVar vh1) (AppVar vh2) = varHeadedSame vh1 vh2
varHeadedSame (LetVarL vh12 vh11) (LetVarL vh22 vh21) = varHeadedSame vh11 vh21
varHeadedSame (LetVarR vh12) (LetVarR vh22) = case varHeadedSame vh12 vh22 of
    Refl => Refl
varHeadedSame (FixVar vh1) (FixVar vh2) = varHeadedSame vh1 vh2
varHeadedSame (CaseVar vh1) (CaseVar vh2) = varHeadedSame vh1 vh2

varHeadedNoEval : IsVarHeaded e ix -> Not (Eval e e')
varHeadedNoEval (AppVar vh) (EvApp1 ev) = varHeadedNoEval vh ev
varHeadedNoEval (AppVar vh) EvApp2 impossible
varHeadedNoEval (AppVar (LetVarL vh2 vh1)) (EvAppLet v) = valNotVarHeaded v vh2
varHeadedNoEval (AppVar (LetVarR vh2)) (EvAppLet v) = valNotVarHeaded v vh2
varHeadedNoEval (LetVarL vh2 vh1) (EvLet1 ev) = varHeadedNoEval vh2 ev
varHeadedNoEval (LetVarR vh2) (EvLet1 ev) = varHeadedNoEval vh2 ev
varHeadedNoEval (LetVarL vh2 vh1) (EvLet2 vh ev) = varHeadedNoEval vh1 ev
varHeadedNoEval (LetVarR vh2) (EvLet2 vh ev) = ?argl14
varHeadedNoEval (LetVarL vh2 vh1) (EvLet3 vh v) = valNotVarHeaded v vh1
varHeadedNoEval (LetVarR vh2) (EvLet3 vh v) = ?argl15
varHeadedNoEval vh (EvFix1 ev) = ?argl16
varHeadedNoEval vh (EvFix2 v) = ?argl17
varHeadedNoEval vh (EvCase1 ev) = ?argl81
varHeadedNoEval vh (EvCase2 ev) = ?argl19
varHeadedNoEval vh (EvCaseLet v) = ?argl10

valNoEval : IsValue e -> Not (Eval e e')
valNoEval IntVal ev impossible
valNoEval ArrowVal ev impossible
valNoEval DataVal ev impossible
valNoEval (LetVal v1) (EvLet1 ev) = valNoEval v1 ev
valNoEval (LetVal v1) (EvLet2 vh ev) = valNotVarHeaded v1 vh
valNoEval (LetVal v1) (EvLet3 vh v2) = valNotVarHeaded v1 vh

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
deterministicEval (EvLet1 ev1) (EvLet2 vh2 ev2) = ?deterministic_5
deterministicEval (EvLet1 ev1) (EvLet3 vh2 v2) = ?deterministic_51
deterministicEval (EvLet2 vh1 ev1) ev2 = ?deterministic_6
deterministicEval (EvLet3 vh1 v1) ev2 = ?deterministic_7
deterministicEval (EvFix1 ev1) ev2 = ?deterministic_8
deterministicEval (EvFix2 v1) ev2 = ?deterministic_9
deterministicEval (EvCase1 ev1) ev2 = ?deterministic_11
deterministicEval (EvCase2 ev1) ev2 = ?deterministic_12
deterministicEval (EvCaseLet v1) ev2 = ?deterministic_13