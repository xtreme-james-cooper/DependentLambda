module Stack.Evaluation.Determinism

import public Stack.Evaluation.Evaluation

%default total

determinism : Eval s s' -> Eval s s'' -> s' = s''
determinism EvVar EvVar = Refl
determinism EvNum EvNum = Refl
determinism EvPrim EvPrim = Refl
determinism EvIsZero EvIsZero = Refl
determinism EvApp EvApp = Refl
determinism EvAbs EvAbs = Refl
determinism EvLet EvLet = Refl
determinism EvFix EvFix = Refl
determinism EvConstr EvConstr = Refl
determinism EvCase EvCase = Refl
determinism EvTyApp EvTyApp = Refl
determinism EvTyAbs EvTyAbs = Refl
determinism EvFold EvFold = Refl
determinism EvUnfold EvUnfold = Refl
determinism RetUpdate RetUpdate = Refl
determinism RetPrim1 RetPrim1 = Refl
determinism RetPrim2 RetPrim2 = Refl
determinism RetIsZeroZ RetIsZeroZ = Refl
determinism RetIsZeroZ (RetIsZeroS nz) = void (nz Refl)
determinism (RetIsZeroS nz) RetIsZeroZ = void (nz Refl)
determinism (RetIsZeroS nz) (RetIsZeroS nz') = Refl
determinism RetApp RetApp = Refl
determinism RetFix RetFix = Refl
determinism RetCase RetCase = Refl
determinism RetTyApp RetTyApp = Refl
determinism RetUnfold RetUnfold = Refl
