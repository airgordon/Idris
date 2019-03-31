import Zahlen
import Natural

public export
data LTE : Zahlen -> Zahlen -> Type where
  MkLTE :  {x, y : Zahlen} -> {z : Zahlen} -> {auto zz : NonNeg z} -> inv_plus x + y = z -> LTE x y

public export
total
t : {h : Zahlen} -> h = Zero -> {x : Natural} -> h = Zneg x -> Void
t {h = Zero} Refl Refl impossible
t {h = (Zpos _)} Refl _ impossible
t {h = (Zneg _)} Refl _ impossible

public export
total
t2 : {h : Zahlen} -> {s : Natural} -> h = Zpos s -> {x : Natural} -> h = Zneg x -> Void
t2 {h = Zero} Refl _ impossible
t2 {h = (Zpos _)} Refl Refl impossible
t2 {h = (Zneg _)} Refl _ impossible

public export
total
tp : (x, y : Zahlen) -> (t : Zahlen) -> Type
tp x y t = inv_plus x + y = t

public export
total
calc : (x, y : Zahlen) -> DPair Zahlen (tp x y)
calc x y = (inv_plus x + y ** Refl)

public export
total
cmp2_rhs_rhs_1 : (s : Natural) -> (pf : tp x y (Zneg s)) -> LTE x y -> Void
cmp2_rhs_rhs_1 s pf (MkLTE {zz = NNpos} prf) = t2 prf pf
cmp2_rhs_rhs_1 s pf (MkLTE {zz = NNzero} prf) = t prf pf

public export
total
cmp_rhs : (t : DPair Zahlen (tp x y)) -> Dec (LTE x y)
cmp_rhs ((Zpos s) ** pf) = Yes (MkLTE pf)
cmp_rhs ((Zneg s) ** pf) = No (cmp2_rhs_rhs_1 s pf)
cmp_rhs (Zero ** pf) = Yes (MkLTE pf)

public export
total
cmp : (x, y : Zahlen) -> Dec (LTE x y)
cmp x y = cmp_rhs (calc x y)

reflex : Main.LTE x x
reflex = MkLTE left_inv

nonneg_incr: NonNeg z -> NonNeg (plus_one z)
nonneg_incr {z = Zero} _ = NNpos
nonneg_incr {z = (Zpos y)} _ = NNpos
nonneg_incr {z = (Zneg _)} NNpos impossible
nonneg_incr {z = (Zneg _)} NNzero impossible

nonneg_plus: NonNeg x -> NonNeg y -> NonNeg (x + y)
nonneg_plus {x = Zero} NNzero yy = yy
nonneg_plus {x = (Zpos F)} _ yy = nonneg_incr yy
nonneg_plus {x = (Zpos (N s))} xx yy = nonneg_incr (nonneg_plus {x = Zpos s} NNpos yy)
nonneg_plus {x = (Zneg _)} NNpos _ impossible
nonneg_plus {x = (Zneg _)} NNzero _ impossible

trans_rhs_3_rhs_rhs_rhs : {x: Zahlen} -> x + z = x + (y + inv_plus y) + z

trans_rhs_3_rhs_rhs : {x: Zahlen} -> x + z = x + y + inv_plus y + z
trans_rhs_3_rhs_rhs {x} {y} {z} = rewrite z_assoc {x} {y} {z=inv_plus y} in trans_rhs_3_rhs_rhs_rhs {x} {y} {z}

trans_rhs_3_rhs : {x: Zahlen} -> x + z = x + y + (inv_plus y + z)
trans_rhs_3_rhs {x} {y} {z} = rewrite sym (z_assoc {x=x+y} {y=inv_plus y} {z}) in trans_rhs_3_rhs_rhs

trans_rhs_3 : (inv_plus x + y = z1) -> (inv_plus y + z = z2) -> (inv_plus x + z = z1 + z2)
trans_rhs_3 prf1 prf2 = rewrite sym prf1 in (rewrite sym prf2 in trans_rhs_3_rhs)

trans : Main.LTE x y -> Main.LTE y z -> Main.LTE x z
trans (MkLTE {z=z1} {zz=zz1} prf) (MkLTE {z=z2} {zz=zz2} prf2) = MkLTE {z = z1 + z2} {zz = nonneg_plus zz1 zz2} (trans_rhs_3 prf prf2)
