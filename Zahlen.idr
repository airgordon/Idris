module Zahlen

import Natural as Nt

--- (x : Maybe (Positive _)) ->
public export
data Zahlen = Zero | Zpos (Nt.Positive x) | Zneg (Nt.Positive x)

--- isPositive : (Zahlen _) -> Bool
--- isPositive Zpos = True
--- isPositive _ = False
---
---

public export total
plus_one : Zahlen -> Zahlen
plus_one Zero = Zpos (Nt.PositiveN F)
plus_one (Zpos (Nt.PositiveN x)) = Zpos (Nt.PositiveN (N x))
plus_one (Zneg (Nt.PositiveN F)) = Zero
plus_one (Zneg (Nt.PositiveN (N x))) = Zneg (Nt.PositiveN x)

public export total
minus_one : Zahlen -> Zahlen
minus_one Zero = Zneg (Nt.PositiveN F)
minus_one (Zneg (Nt.PositiveN x)) = Zneg (Nt.PositiveN (N x))
minus_one (Zpos (Nt.PositiveN F)) = Zero
minus_one (Zpos (Nt.PositiveN (N x))) = Zpos (Nt.PositiveN x)

public export total
incr : Nt.Natural -> Zahlen -> Zahlen
incr F y     = plus_one y
incr (N x) y = plus_one (incr x y)

public export total
decr : Nt.Natural -> Zahlen -> Zahlen
decr F y     = minus_one y
decr (N x) y = minus_one (decr x y)

public export total
(+) : Zahlen -> Zahlen -> Zahlen

(Zpos (Nt.PositiveN x)) + y = incr x y
(Zneg (Nt.PositiveN x)) + y = decr x y
Zero + y = y

public export total
g3 : z = plus_one (minus_one z)
g3 { z =  Zero                       } = Refl
g3 { z = (Zneg (Nt.PositiveN n))     } = Refl
g3 { z = (Zpos (Nt.PositiveN F))     } = Refl
g3 { z = (Zpos (Nt.PositiveN (N n))) } = Refl

public export total
g3m : z = minus_one (plus_one z)
g3m {z = Zero} = Refl
g3m {z = Zpos (Nt.PositiveN n)} = Refl
g3m {z = Zneg (Nt.PositiveN F)} = Refl
g3m {z = Zneg (Nt.PositiveN (N n))} = Refl

public export total
plus_one_assoc : plus_one y + z = plus_one (y + z)
plus_one_assoc { y =  Zero                       } = Refl
plus_one_assoc { y = (Zpos (Nt.PositiveN y))     } = Refl
plus_one_assoc { y = (Zneg (Nt.PositiveN F))     } = g3
plus_one_assoc { y = (Zneg (Nt.PositiveN (N y))) } = g3

public export total
minus_one_assoc : minus_one y + z = minus_one (y + z)
minus_one_assoc { y =  Zero                       } = Refl
minus_one_assoc { y = (Zneg (Nt.PositiveN y))     } = Refl
minus_one_assoc { y = (Zpos (Nt.PositiveN F))     } = g3m
minus_one_assoc { y = (Zpos (Nt.PositiveN (N y))) } = g3m

public export total
pos_z_assoc_r3 : plus_one t + z = plus_one (t + z)
pos_z_assoc_r3 {t = Zero} = Refl
pos_z_assoc_r3 {t = Zpos (Nt.PositiveN n)} = Refl
pos_z_assoc_r3 {t = Zneg (Nt.PositiveN F)} = g3
pos_z_assoc_r3 {t = Zneg (Nt.PositiveN (N n))} = g3

public export total
neg_z_assoc_r3 : minus_one t + z = minus_one (t + z)
neg_z_assoc_r3 {t = Zero} = Refl
neg_z_assoc_r3 {t = Zneg (Nt.PositiveN n)} = Refl
neg_z_assoc_r3 {t = Zpos (Nt.PositiveN F)} = g3m
neg_z_assoc_r3 {t = Zpos (Nt.PositiveN (N n))} = g3m

public export total
pos_z_assoc_r :
((incr n y) + z = incr n (y + z)) ->
(plus_one (incr n y)) + z = plus_one (incr n (y + z))

pos_z_assoc_r p = rewrite (sym p) in pos_z_assoc_r3

public export total
neg_z_assoc_r :
((decr n y) + z = decr n (y + z)) ->
(minus_one (decr n y)) + z = minus_one (decr n (y + z))

neg_z_assoc_r p = rewrite (sym p) in neg_z_assoc_r3

public export total
pos_z_assoc : (x : Nt.Natural) -> (incr x y) + z = incr x (y + z)
pos_z_assoc F     = plus_one_assoc
pos_z_assoc (N n) = pos_z_assoc_r (pos_z_assoc n)

public export total
neg_z_assoc : (x : Nt.Natural) -> (decr x y) + z = decr x (y + z)
neg_z_assoc F     = minus_one_assoc
neg_z_assoc (N n) = neg_z_assoc_r (neg_z_assoc n)

public export total
z_assoc :   {x : Zahlen} ->
            {y : Zahlen} ->
            {z : Zahlen} ->
            x + y + z = x + (y + z)
z_assoc {x = Zero} = Refl
z_assoc {x = Zpos (Nt.PositiveN n)} = pos_z_assoc n
z_assoc {x = Zneg (Nt.PositiveN n)} = neg_z_assoc n


public export total
incr_is_pos : (t : Nt.Natural) -> incr t Zero = Zpos (PositiveN t)
incr_is_pos F = Refl
incr_is_pos (N x) = rewrite (incr_is_pos x) in Refl

public export total
right_neutral_pos : ((Zpos n) + Zero) = Zpos n
right_neutral_pos {n = Nt.PositiveN t } = incr_is_pos t

public export total
decr_is_neg : (t : Nt.Natural) -> decr t Zero = Zneg (PositiveN t)
decr_is_neg F = Refl
decr_is_neg (N x) = rewrite (decr_is_neg x) in Refl

public export total
right_neutral_neg : ((Zneg n) + Zero) = Zneg n
right_neutral_neg {n = Nt.PositiveN t } = decr_is_neg t


public export total
right_neutral : {x: Zahlen} -> x + Zero = x
right_neutral {x = Zero} = Refl
right_neutral {x = Zneg n} = right_neutral_neg
right_neutral {x = Zpos n} = right_neutral_pos

public export total
inv_plus: Zahlen -> Zahlen
inv_plus Zero = Zero
inv_plus (Zneg x) = Zpos x
inv_plus (Zpos x) = Zneg x

public export total
left_inv_pos_r : (x : Natural) -> (t : Zahlen) -> minus_one (decr x (plus_one t)) = decr x t
left_inv_pos_r F t = cong (sym g3m)
left_inv_pos_r (N x) t = rewrite (sym (left_inv_pos_r x t)) in Refl

public export total
left_inv_neg_r : (x : Natural) -> (t : Zahlen) -> plus_one (incr x (minus_one t)) = incr x t
left_inv_neg_r F t = cong (sym g3)
left_inv_neg_r (N x) t = rewrite (sym (left_inv_neg_r x t)) in Refl

public export total
left_inv_pos : (y : Natural) -> decr y (Zpos (PositiveN y)) = Zero
left_inv_pos F = Refl
left_inv_pos (N x) = rewrite sym (left_inv_pos x) in (left_inv_pos_r x (Zpos (PositiveN x)))

public export total
left_inv_neg : (y : Natural) -> incr y (Zneg (PositiveN y)) = Zero
left_inv_neg F = Refl
left_inv_neg (N x) = rewrite sym (left_inv_neg x) in (left_inv_neg_r x (Zneg (PositiveN x)))

public export total
left_inv : {x : Zahlen} -> inv_plus x + x = Zero
left_inv {x=Zero} = Refl
left_inv {x=Zpos (Nt.PositiveN y)} = left_inv_pos y
left_inv {x=Zneg (Nt.PositiveN y)} = left_inv_neg y

public export total
right_inv : {x : Zahlen} -> x + inv_plus x = Zero
right_inv {x=Zero} = Refl
right_inv {x=Zpos (Nt.PositiveN y)} = left_inv_neg y
right_inv {x=Zneg (Nt.PositiveN y)} = left_inv_pos y

public export total
double_plus_inv : {t : Zahlen} -> t = inv_plus (inv_plus t)
double_plus_inv {t = Zero} = Refl
double_plus_inv {t = (Zpos y)} = Refl
double_plus_inv {t = (Zneg y)} = Refl

public export total
mulPos : Positive x -> Zahlen -> Zahlen
mulPos (PositiveN F) y = y
mulPos (PositiveN (N x)) y = y + mulPos (PositiveN x) y

public export total
mul : Zahlen -> Zahlen -> Zahlen
mul Zero y = Zero
mul (Zneg t) y = inv_plus (mulPos t y)
mul (Zpos t) y = mulPos t y

public export
data NonZero: Zahlen -> Type where
    PosZ: NonZero (Zpos s)
    NegZ: NonZero (Zneg s)

public export total
mul_com: {x, y : Zahlen} -> mul x y = mul y x

public export total
nsfgngf2 : (a, b, c: Zahlen) -> a + b + c = a + c + b

public export total
nsfgngf : (a, b, c, d : Zahlen) -> a + b + c + d = a + c + b + d
nsfgngf a b c d = cong (nsfgngf2 a b c)


public export total
sghgfhsfgh : (a, b, c, d : Zahlen) -> a + b + c + d = a + c + (b + d)
sghgfhsfgh a b c d = rewrite sym (z_assoc {x=(a+c)} {y=b} {z=d}) in (nsfgngf a b c d)

public export total
distr3_rhs_2_rhs_3 : (a, b, c, d : Zahlen) -> a + b + (c + d) = a + c + (b + d)
distr3_rhs_2_rhs_3 a b c d = rewrite sym (z_assoc {x=(a+b)} {y=c} {z=d}) in (sghgfhsfgh a b c d)

public export total
distr3_rhs_2 : (y : Zahlen) -> (t : Zahlen) -> (z : Positive x) -> mulPos z (y + t) = ((mulPos z y) + (mulPos z t))
distr3_rhs_2 y t (PositiveN F) = Refl
distr3_rhs_2 y t (PositiveN (N z1)) = rewrite (distr3_rhs_2 y t (PositiveN z1)) in distr3_rhs_2_rhs_3 y t (mulPos (PositiveN z1) y) (mulPos (PositiveN z1) t)


public export total
distr3 : {y, t, z : Zahlen} -> mul z (y + t) = mul z y + (mul z t)
distr3 {z=Zero} = Refl
distr3 {z=(Zpos z1)} {y=y} {t=t} = distr3_rhs_2 y t z1
distr3 {z=(Zneg z1)} = ?distr3_rhs_3

public export total
distr2 : {y, t, z : Zahlen} -> mul z (y + t) = mul z y + (mul t z)
distr2 {y=y} {t=t} {z=z} = rewrite mul_com {x=t} {y=z} in distr3

public export total
distr1 : {y, t, z : Zahlen} -> mul z (y + t) = mul y z + (mul t z)
distr1 {y=y} {t=t} {z=z} = rewrite mul_com {x=y} {y=z} in distr2

public export total
distr: {y, t, z : Zahlen} -> mul (y + t) z = mul y z + (mul t z)
distr {y=y} {t=t} {z=z} = rewrite mul_com {x=y+t} {y=z} in distr1

public export total
mul_assoc_rhs_2_rhs_3 : (x1 : Natural) -> (y : Zahlen) -> (z : Zahlen) ->
(mul (mulPos (PositiveN x1) y) z = mulPos (PositiveN x1) (mul y z)) -> mul (y + (mulPos (PositiveN x1) y)) z = ((mul y z) + (mulPos (PositiveN x1) (mul y z)))
mul_assoc_rhs_2_rhs_3 x1 y z prf = rewrite (sym prf) in distr {y=y} {t = mulPos (PositiveN x1) y} {z=z}

public export total
mul_assoc_pos : {x : Positive x1} -> {y : Zahlen} -> {z : Zahlen} -> mul (mulPos x y) z = mulPos x (mul y z)
mul_assoc_pos {x=PositiveN F} = Refl
mul_assoc_pos {x=PositiveN (N x1)} {y=y} {z=z} = mul_assoc_rhs_2_rhs_3 x1 y z (mul_assoc_pos {x = PositiveN x1} {y=y} {z=z})

public export total
mul_inv_first : (y : Zahlen) -> (z : Zahlen) -> mul (inv_plus y) z = inv_plus (mul y z)
mul_inv_first Zero z = Refl
mul_inv_first (Zpos y) z = Refl
mul_inv_first (Zneg y) z = double_plus_inv

public export total
mul_assoc_neg : (x : Positive x1) -> (y : Zahlen) -> (z : Zahlen) -> mul (inv_plus (mulPos x y)) z = inv_plus (mulPos x (mul y z))
mul_assoc_neg x y z = rewrite mul_inv_first (mulPos x y) z in cong mul_assoc_pos


public export total
mul_assoc : {x, y, z : Zahlen} -> (x `mul` y) `mul` z = x `mul` (y `mul` z)
mul_assoc {x=Zero} = Refl
mul_assoc {x=(Zpos x1)} = mul_assoc_pos
mul_assoc {x=(Zneg x1)} {y=y} {z=z} = mul_assoc_neg x1 y z
