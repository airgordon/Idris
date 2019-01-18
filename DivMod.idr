module DivMod

import Natural
import Prelude.Pairs
import Builtins

public export
data DivMod  : (d: Natural) -> Positive d2 -> (r: Natural) -> (q: Natural) -> (    d = (mul d2 r) + q ) ->  Type where
     DivModc : (d: Natural) -> (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> (p: (d = (mul d2 r) + q)) ->  DivMod d d1 r q p

public export
g : (Natural ** Positive)
g = ((N F) ** PositiveN F)

-- public export
-- f : (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> ( (Positive _) ** \x = (DivMod ((mul d2 r) + q) d1 r q Refl))
-- f (PositiveN d2m) r q = (((mul (N d2m) r) + q) ** DivMod ((mul (N d2m) r) + q) (PositiveN d2m) r q Refl)