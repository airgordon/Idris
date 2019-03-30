module DivMod

import Natural
import Prelude.Pairs
import Builtins
import Zahlen

public export
data Divide : (n: Zahlen) -> (d: Zahlen) -> Type where
  MkDiv : (m: Zahlen) -> (prf : (mul m d) = n) -> Divide n d

divSelf : (n : Zahlen) -> Divide n n
divSelf n = MkDiv (Zpos (PositiveN F)) Refl

divOne : (n : Zahlen) -> Divide n (Zpos (PositiveN F))
divOne n = MkDiv n (rewrite mul_com {x=n} {y=Zpos (PositiveN F)} in Refl)

divZ : (d : Zahlen) -> Divide Zero d
divZ d = MkDiv Zero Refl

divPlus : (n1: Zahlen) ->
          (n2: Zahlen) ->
          (d: Zahlen) ->
          Divide n1 d -> Divide n2 d ->
          Divide (n1 + n2) d
divPlus n1 n2 d (MkDiv m1 prf1) (MkDiv m2 prf2) = MkDiv (m1 + m2) (rewrite sym prf1 in rewrite sym prf2 in distr)

public export
data DivMod  : (d: Natural) -> Positive d2 -> (r: Natural) -> (q: Natural) -> ( d = (mul d2 r) + q ) ->  Type where
     DivModc : (d: Natural) -> (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> (p: (d = (mul d2 r) + q)) ->  DivMod d d1 r q p

--- public export
--- g : (Natural ** ?h)

-- public export
-- f : (d1 : Positive d2) -> (r: Natural) -> (q: Natural) -> ( (Positive _) ** \x = (DivMod ((mul d2 r) + q) d1 r q Refl))
-- f (PositiveN d2m) r q = (((mul (N d2m) r) + q) ** DivMod ((mul (N d2m) r) + q) (PositiveN d2m) r q Refl)
