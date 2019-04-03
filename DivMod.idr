module DivMod

import Natural
import Prelude.Pairs
import Builtins
import Zahlen
import LTE

public export
data Divide : (n: Zahlen) -> (d: Zahlen) -> Type where
  MkDiv : (m: Zahlen) -> (prf : (mul m d) = n) -> Divide n d

divSelf : (n : Zahlen) -> Divide n n
divSelf n = MkDiv (Zpos F) Refl

divOne : (n : Zahlen) -> Divide n (Zpos F)
divOne n = MkDiv n (rewrite mul_com {x=n} {y=Zpos F} in Refl)

divZ : (d : Zahlen) -> Divide Zero d
divZ d = MkDiv Zero Refl

divPlus : {n1: Zahlen} ->
          {n2: Zahlen} ->
          {d: Zahlen} ->
          Divide n1 d -> Divide n2 d ->
          Divide (n1 + n2) d
divPlus {n1} {n2} {d} (MkDiv m1 prf1) (MkDiv m2 prf2) = MkDiv (m1 + m2) (rewrite sym prf1 in rewrite sym prf2 in distr)


public export
data DivMod : (n, d: Zahlen) -> Type where
     DivModc : {r: Zahlen} -> {dd : Znat d} -> {q: Zahlen} -> (qq : Znat q) -> GT d q -> (n = (mul d r) + q) -> DivMod n d

public export
data DivModN : (n, d, n1: Zahlen) -> Type where
     MkDivModN : {nn : NonNeg n} -> {dd : Znat d} -> LTE n1 n -> n1 = mul r d -> DivModN n d n1


diw2_rhs_rhs_2 : (LTE (n1 + d) n -> Void) -> DivModN n d (n1 + d) -> Void
diw2_rhs_rhs_2 f (MkDivModN x _) = f x

dhdsh : (d + mul r d = mul (plus_one r) d) -> ((mul r d) + d) = mul (plus_one r) d
dhdsh prf = rewrite sym prf in plus_com

diw2_rhs_rhs_3 : mul r d + d = mul (plus_one r) d
diw2_rhs_rhs_3 {r} {d} = dhdsh (sym (distr {y = Zpos F} {t=r} {z=d}))

total
diw2_rhs : DivModN n d n1 -> Dec (DivModN n d (n1 + d))
diw2_rhs (MkDivModN {nn} {dd} {d} {r} {n1} x prf) = case cmpr of
    Yes cmpPrf => Yes (MkDivModN {r = plus_one r} {nn} {dd} cmpPrf (rewrite prf in diw2_rhs_rhs_3))
    No contra => No (diw2_rhs_rhs_2 contra)
  where
    cmpr : Dec (LTE (n1 + d) n)
    cmpr = (LTE.cmp (n1 + d) n)

diwNn : (n, d: Zahlen) -> NonNeg n -> Znat d -> DivMod n d
diwNn n nn d x = ?fgjsfg
