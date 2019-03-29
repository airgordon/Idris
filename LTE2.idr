import Zahlen
import Natural
data LTE : Zahlen -> Zahlen -> Type where
  MkLTE :  {x, y : Zahlen} -> {z : Zahlen} -> {auto zz : NonNeg z} -> inv_plus x + y = z -> LTE x y

decrZero : decr x Zero = Zneg x
decrZero {x = F} = Refl
decrZero {x = (N s)} = rewrite decrZero {x=s} in Refl

t : {h : Zahlen} -> h = Zero -> {x : Natural} -> h = Zneg x -> Void
t {h = Zero} Refl Refl impossible
t {h = (Zpos _)} Refl _ impossible
t {h = (Zneg _)} Refl _ impossible

neg_plus_zero_isnt_zero_2 : (decr x Zero = Zero) -> (decr x Zero = Zneg x) -> Void
neg_plus_zero_isnt_zero_2 prf prf1 = t prf prf1


neg_plus_zero_isnt_zero_1 : decr x Zero = Zero -> Void
neg_plus_zero_isnt_zero_1 {x} prf = neg_plus_zero_isnt_zero_2 prf (decrZero {x})

fhgfgh_1 : LTE (Zpos s) Zero -> Void
fhgfgh_1 (MkLTE {x = Zpos x} {z = Zero} prf) = neg_plus_zero_isnt_zero_1 prf
fhgfgh_1 (MkLTE {z = (Zpos y)} prf) = ?fhgfgh_1_rhs_3
fhgfgh_1 (MkLTE {z = (Zneg y)} prf) = ?fhgfgh_1_rhs_4

fhgfgh_2_rhs_4 : LTE (Zpos (N x)) (Zpos F) -> Void
fhgfgh_2_rhs_4 {x = F} (MkLTE {zz = NNpos} Refl) impossible
fhgfgh_2_rhs_4 {x = F} (MkLTE {zz = NNzero} Refl) impossible
fhgfgh_2_rhs_4 {x = N x} (MkLTE {z = Zero} {zz = NNzero} prf) = ?fhgfgh_2_rhs_4_rhs_1
fhgfgh_2_rhs_4 {x = N x} (MkLTE {z = Zpos z} {zz = NNpos} prf) = ?fhgfgh_2_rhs_4_rhs_2
fhgfgh_2_rhs_4 {x = N _} (MkLTE {z = Zneg _} {zz = NNpos} _) impossible
fhgfgh_2_rhs_4 {x = N _} (MkLTE {z = Zneg _} {zz = NNzero} _) impossible

incrLte : LTE x y -> LTE (plus_one x) (plus_one y)
incrLte  (MkLTE {x} {y} {z} prf) = MkLTE {z} (rewrite inv_sum_rhs_2_rhs_2 x in (rewrite sym prf in eq4 (Zneg F) (inv_plus x) (Zpos F) y))

fhgfgh_2 : Dec (LTE (Zpos s) (Zpos y))
fhgfgh_2 {s = F} {y = F} = Yes (MkLTE Refl)
fhgfgh_2 {s = F} {y = N x} = Yes (MkLTE Refl)
fhgfgh_2 {s = N x} {y = F} = No (fhgfgh_2_rhs_4)
fhgfgh_2 {s = N x} {y = N y} = ?fhgfgh_2_rhs_5 (fhgfgh_2 {s=x} {y})

cmp : (x, y : Zahlen) -> Dec (LTE x y)
cmp (Zpos s) Zero = No fhgfgh_1
cmp (Zpos s) (Zpos y) = fhgfgh_2
cmp (Zpos s) (Zneg y) = ?fhgfgh_3
cmp (Zneg s) y = ?fhgfgh
cmp Zero y = ?cmp_rhs_1
