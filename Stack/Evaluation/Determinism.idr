module Stack.Evaluation.Determinism

import public Stack.Evaluation.Evaluation

%default total

determinism : Eval s s' -> Eval s s'' -> s' = s''
determinism ev ev' = ?argl
