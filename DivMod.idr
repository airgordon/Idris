module DivMod

import Natural
import Prelude.Pairs
import Builtins
import Zahlen


--public export
--data Divide : NonNeg n -> NonNeg d -> {tt : NonNeg t} -> {prf : (mul d t) = n} -> Type where
--    MkDiv : (nn: NonNeg n) -> (dd : NonNeg d) -> {tt : NonNeg t} -> (prf : (mul d t) = n) -> Divide nn dd {tt} {prf}

public export
data Divide : NonNeg n -> NonNeg d -> Type where
    MkDiv : {nn: NonNeg n} -> {dd : NonNeg d} -> (t : Zahlen) -> {auto tt : NonNeg t} -> (prf : (mul t d) = n) -> Divide nn dd

diw2 : (nn: NonNeg n) -> Divide nn nn
diw2 nn = MkDiv (Zpos F) Refl

diw : (nn: NonNeg n) -> Divide nn nn
diw {n = Zero} NNzero = ?gkdfjgkdfgf_4
diw {n = (Zpos y)} NNpos = ?gkdfjgkdfgf_1
diw {n = (Zneg _)} NNpos impossible
diw {n = (Zneg _)} NNzero impossible



public export
data DivMod  : (d: Natural) -> Positive d2 -> (r: Natural) -> (q: Natural) -> (    d = (mul d2 r) + q ) ->  Type where
     DivModc : (d: Natural) -> (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> (p: (d = (mul d2 r) + q)) ->  DivMod d d1 r q p

--- public export
--- g : (Natural ** ?h)

-- public export
-- f : (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> ( (Positive _) ** \x = (DivMod ((mul d2 r) + q) d1 r q Refl))
-- f (PositiveN d2m) r q = (((mul (N d2m) r) + q) ** DivMod ((mul (N d2m) r) + q) (PositiveN d2m) r q Refl)
