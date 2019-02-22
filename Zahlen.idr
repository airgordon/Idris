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
inv_sum_rhs_2_rhs_2 : (b : Zahlen) -> inv_plus (plus_one b) = minus_one (inv_plus b)
inv_sum_rhs_2_rhs_2 Zero = Refl
inv_sum_rhs_2_rhs_2 (Zpos (PositiveN x)) = Refl
inv_sum_rhs_2_rhs_2 (Zneg (PositiveN F)) = Refl
inv_sum_rhs_2_rhs_2 (Zneg (PositiveN (N x))) = Refl

public export total
inv_sum_rhs_2_rhs_3 : (b : Zahlen) -> (x : Natural) -> inv_plus (incr x b) = decr x (inv_plus b)
inv_sum_rhs_2_rhs_3 b F = inv_sum_rhs_2_rhs_2 b
inv_sum_rhs_2_rhs_3 b (N x) = rewrite sym (inv_sum_rhs_2_rhs_3 b x) in inv_sum_rhs_2_rhs_2 (incr x b)

public export total
inv_sum_rhs_2 : (b : Zahlen) -> (y : Positive x) -> inv_plus ((Zpos y) + b) = ((Zneg y) + (inv_plus b))
inv_sum_rhs_2 b (PositiveN F) = inv_sum_rhs_2_rhs_2 b
inv_sum_rhs_2 b (PositiveN (N x)) = rewrite inv_sum_rhs_2_rhs_2 (incr x b) in cong (inv_sum_rhs_2_rhs_3 b x)

public export total
inv_sum_rhs_3_rhs_2 : (b : Zahlen) -> inv_plus (minus_one b) = plus_one (inv_plus b)
inv_sum_rhs_3_rhs_2 Zero = Refl
inv_sum_rhs_3_rhs_2 (Zpos (PositiveN F)) = Refl
inv_sum_rhs_3_rhs_2 (Zpos (PositiveN (N x))) = Refl
inv_sum_rhs_3_rhs_2 (Zneg (PositiveN x)) = Refl

public export total
inv_sum_rhs_3_rhs_3 : (b : Zahlen) -> (x : Natural) -> inv_plus (decr x b) = incr x (inv_plus b)
inv_sum_rhs_3_rhs_3 b F = inv_sum_rhs_3_rhs_2 b
inv_sum_rhs_3_rhs_3 b (N x) = rewrite sym (inv_sum_rhs_3_rhs_3 b x) in inv_sum_rhs_3_rhs_2 (decr x b)

public export total
inv_sum_rhs_3 : (b : Zahlen) -> (y : Positive x) -> inv_plus ((Zneg y) + b) = ((Zpos y) + (inv_plus b))
inv_sum_rhs_3 b (PositiveN F) = inv_sum_rhs_3_rhs_2 b
inv_sum_rhs_3 b (PositiveN (N x)) = rewrite inv_sum_rhs_3_rhs_2 (decr x b) in cong (inv_sum_rhs_3_rhs_3 b x)

public export total
inv_sum : {a, b : Zahlen} -> inv_plus (a + b) = inv_plus a + inv_plus b
inv_sum {a = Zero} {b = b} = Refl
inv_sum {a = (Zpos y)} {b = b} = inv_sum_rhs_2 b y
inv_sum {a = (Zneg y)} {b = b} = inv_sum_rhs_3 b y

public export total
plus_com_rhs_4_rhs_1_rhs_4 : Zpos (PositiveN (N x)) = incr x (Zpos (PositiveN F))
plus_com_rhs_4_rhs_1_rhs_4 {x = F} = Refl
plus_com_rhs_4_rhs_1_rhs_4 {x = (N x)} = rewrite sym (plus_com_rhs_4_rhs_1_rhs_4 {x = x}) in Refl

public export total
plus_com_rhs_4_rhs_1_rhs_3 : Zneg (PositiveN x) = minus_one (decr x (Zpos (PositiveN F)))
plus_com_rhs_4_rhs_1_rhs_3 {x = F} = Refl
plus_com_rhs_4_rhs_1_rhs_3 {x = (N x)} = rewrite sym (plus_com_rhs_4_rhs_1_rhs_3 {x = x}) in Refl

public export total
plus_com_rhs_4_rhs_1 : (y : Zahlen) -> plus_one y = (y + (Zpos (PositiveN F)))
plus_com_rhs_4_rhs_1 Zero = Refl
plus_com_rhs_4_rhs_1 (Zpos (PositiveN x)) = plus_com_rhs_4_rhs_1_rhs_4
plus_com_rhs_4_rhs_1 (Zneg (PositiveN F)) = Refl
plus_com_rhs_4_rhs_1 (Zneg (PositiveN (N x))) = plus_com_rhs_4_rhs_1_rhs_3

public export total
plus_com_rhs_4_rhs_2_rhs_2_rhs_2 : (z : Zahlen) -> plus_one (minus_one z) = minus_one (plus_one z)
plus_com_rhs_4_rhs_2_rhs_2_rhs_2 z = rewrite sym (g3m {z}) in sym g3

public export total
plus_com_rhs_4_rhs_2_rhs_2 : (x : Natural) -> (y : Natural) -> plus_one (decr y (Zpos (PositiveN x))) = decr y (Zpos (PositiveN (N x)))
plus_com_rhs_4_rhs_2_rhs_2 F F = Refl
plus_com_rhs_4_rhs_2_rhs_2 (N x) F = Refl
plus_com_rhs_4_rhs_2_rhs_2 x (N y) = rewrite sym (plus_com_rhs_4_rhs_2_rhs_2 x y) in plus_com_rhs_4_rhs_2_rhs_2_rhs_2 (decr y (Zpos (PositiveN x)))

public export total
plus_com_rhs_4_rhs_2_rhs_1 : (x : Natural) -> (y : Natural) -> plus_one (incr y (Zpos (PositiveN x))) = incr y (Zpos (PositiveN (N x)))
plus_com_rhs_4_rhs_2_rhs_1 F F = Refl
plus_com_rhs_4_rhs_2_rhs_1 (N x) F = Refl
plus_com_rhs_4_rhs_2_rhs_1 x (N y) = rewrite plus_com_rhs_4_rhs_2_rhs_1 x y in Refl

public export total
plus_com_rhs_4_rhs_2 : (x : Natural) -> (y : Zahlen) -> plus_one (y + Zpos (PositiveN x)) = y + Zpos (PositiveN (N x))
plus_com_rhs_4_rhs_2 x Zero = Refl
plus_com_rhs_4_rhs_2 x (Zpos (PositiveN y)) = plus_com_rhs_4_rhs_2_rhs_1 x y
plus_com_rhs_4_rhs_2 x (Zneg (PositiveN y)) = plus_com_rhs_4_rhs_2_rhs_2 x y

public export total
plus_com_rhs_4 : (x : Natural) -> (y : Zahlen) -> incr x y = (y + (Zpos (PositiveN x)))
plus_com_rhs_4 F y = plus_com_rhs_4_rhs_1 y
plus_com_rhs_4 (N x) y = rewrite plus_com_rhs_4 x y in (plus_com_rhs_4_rhs_2 x y)

public export total
plus_com_rhs_2_rhs_1_rhs_1_rhs_2 : Zpos (PositiveN x) = plus_one (incr x (Zneg (PositiveN F)))
plus_com_rhs_2_rhs_1_rhs_1_rhs_2 {x = F} = Refl
plus_com_rhs_2_rhs_1_rhs_1_rhs_2 {x = (N x)} = rewrite sym $ plus_com_rhs_2_rhs_1_rhs_1_rhs_2 {x = x} in Refl

public export total
plus_com_rhs_2_rhs_1_rhs_1 : (y : Natural) -> minus_one (Zpos (PositiveN y)) = incr y (Zneg (PositiveN F))
plus_com_rhs_2_rhs_1_rhs_1 F = Refl
plus_com_rhs_2_rhs_1_rhs_1 (N x) = plus_com_rhs_2_rhs_1_rhs_1_rhs_2

public export total
plus_com_rhs_2_rhs_1_rhs_2 : (x : Natural) -> (y : Natural) -> minus_one (incr y (Zneg (PositiveN x))) = incr y (Zneg (PositiveN (N x)))
plus_com_rhs_2_rhs_1_rhs_2 x F = sym g3m
plus_com_rhs_2_rhs_1_rhs_2 x (N y) = rewrite sym (plus_com_rhs_2_rhs_1_rhs_2 x y) in sym $ plus_com_rhs_4_rhs_2_rhs_2_rhs_2 (incr y (Zneg (PositiveN x)))

public export total
plus_com_rhs_2_rhs_1 : (x : Natural) -> (y : Natural) -> decr x (Zpos (PositiveN y)) = incr y (Zneg (PositiveN x))
plus_com_rhs_2_rhs_1 F y = plus_com_rhs_2_rhs_1_rhs_1 y
plus_com_rhs_2_rhs_1 (N x) y = rewrite plus_com_rhs_2_rhs_1 x y in (plus_com_rhs_2_rhs_1_rhs_2 x y)

public export total
plus_com_rhs_2_rhs_2_rhs_1 : Zneg (PositiveN (N y)) = decr y (Zneg (PositiveN F))
plus_com_rhs_2_rhs_2_rhs_1 {y = F} = Refl
plus_com_rhs_2_rhs_2_rhs_1 {y = (N x)} = rewrite sym $ plus_com_rhs_2_rhs_2_rhs_1 {y=x} in Refl

public export total
plus_com_rhs_2_rhs_2_rhs_2 : (x : Natural) -> (y : Natural) -> minus_one (decr y (Zneg (PositiveN x))) = decr y (Zneg (PositiveN (N x)))
plus_com_rhs_2_rhs_2_rhs_2 x F = Refl
plus_com_rhs_2_rhs_2_rhs_2 x (N y) = rewrite sym $ plus_com_rhs_2_rhs_2_rhs_2 x y in Refl

public export total
plus_com_rhs_2_rhs_2 : (x : Natural) -> (y : Natural) -> decr x (Zneg (PositiveN y)) = decr y (Zneg (PositiveN x))
plus_com_rhs_2_rhs_2 F y = plus_com_rhs_2_rhs_2_rhs_1
plus_com_rhs_2_rhs_2 (N x) y = rewrite plus_com_rhs_2_rhs_2 x y in (plus_com_rhs_2_rhs_2_rhs_2 x y)


public export total
plus_com_rhs_2 : (x : Natural) -> (y : Zahlen) -> decr x y = (y + (Zneg (PositiveN x)))
plus_com_rhs_2 x Zero = decr_is_neg x
plus_com_rhs_2 x (Zpos (PositiveN y)) = plus_com_rhs_2_rhs_1 x y
plus_com_rhs_2 x (Zneg (PositiveN y)) = plus_com_rhs_2_rhs_2 x y

public export total
plus_com: {x, y : Zahlen} -> x + y = y + x
plus_com {x = Zero} {y} = sym right_neutral
plus_com {x = (Zpos (PositiveN x))} {y} = plus_com_rhs_4 x y
plus_com {x = (Zneg (PositiveN x))} {y} = plus_com_rhs_2 x y

public export total
congf : {a, b: Type} -> (f: a -> b) -> x = y -> f x = f y
congf _ p = cong p

public export total
eq4_32 : (a, b, c: Zahlen) ->  a + (b + c) = a + c + b
eq4_32 a b c = rewrite plus_com {x=b} {y=c} in sym (z_assoc)

public export total
eq4_3 : (a, b, c: Zahlen) -> a + b + c = a + c + b
eq4_3 a b c = rewrite z_assoc {x=a} {y=b} {z=c} in eq4_32 a b c

public export total
eq4_2 : (a, b, c, d : Zahlen) -> a + b + c + d = a + c + b + d
eq4_2 a b c d = congf (+d) (eq4_3 a b c)


public export total
eq4_1 : (a, b, c, d : Zahlen) -> a + b + c + d = a + c + (b + d)
eq4_1 a b c d = rewrite sym (z_assoc {x=(a+c)} {y=b} {z=d}) in (eq4_2 a b c d)

public export total
eq4 : (a, b, c, d : Zahlen) -> a + b + (c + d) = a + c + (b + d)
eq4 a b c d = rewrite sym (z_assoc {x=(a+b)} {y=c} {z=d}) in (eq4_1 a b c d)

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
    NZpos: NonZero (Zpos s)
    NZneg: NonZero (Zneg s)

public export
data NonNeg: Zahlen -> Type where
    NNpos: NonNeg (Zpos s)
    NNzero: NonNeg Zero

public export total
y_rhs_1 : (x : Natural) -> Zero = mulPos (PositiveN x) Zero
y_rhs_1 F = Refl
y_rhs_1 (N x) = y_rhs_1 x

public export total
y_rhs_2 : (x : Natural) -> Zero = inv_plus (mulPos (PositiveN x) Zero)
y_rhs_2 F = Refl
y_rhs_2 (N x) = y_rhs_2 x

public export total
mul_com_rhs_1 : (y : Zahlen) -> Zero = mul y Zero
mul_com_rhs_1 Zero = Refl
mul_com_rhs_1 (Zpos (PositiveN x)) = y_rhs_1 x
mul_com_rhs_1 (Zneg (PositiveN x)) = y_rhs_2 x

public export total
mul_com_rhs_4_rhs_2_rhs_4_rhs_2 : (x, z : Zahlen) -> (y : Natural) -> plus_one (incr y (x + z)) = plus_one x + incr y z
mul_com_rhs_4_rhs_2_rhs_4_rhs_2 x z y = eq4 {a=Zpos (PositiveN F)} {b=Zpos (PositiveN y)} {c=x} {d=z}

public export total
mul_com_rhs_4_rhs_2_rhs_4 : (x : Zahlen) -> (y : Natural) -> incr y (mulPos (PositiveN y) x) = mulPos (PositiveN y) (plus_one x)
mul_com_rhs_4_rhs_2_rhs_4 x F = Refl
mul_com_rhs_4_rhs_2_rhs_4 x (N y) = rewrite sym (mul_com_rhs_4_rhs_2_rhs_4 x y) in mul_com_rhs_4_rhs_2_rhs_4_rhs_2 x (mulPos (PositiveN y) x) y

public export total
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_2 : (x, z : Zahlen) -> minus_one (x + z) = x + minus_one z
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_2 x z = eq4 {a=Zero} {b=Zneg (PositiveN F)} {c=x} {d=z}

public export total
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_1 : (x : Zahlen) -> (z : Zahlen) -> (inv_plus ((Zpos (PositiveN F)) + x) = ((inv_plus (Zpos (PositiveN F))) + (inv_plus x))) -> minus_one (minus_one ((inv_plus x) + z)) = ((inv_plus (plus_one x)) + (minus_one z))
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_1 x z prf1 = rewrite prf1 in (eq4 {a=Zneg (PositiveN F)} {b=Zneg (PositiveN F)} {c=inv_plus x} {d=z})

public export total
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs : (x, z : Zahlen) -> (y : Natural) -> minus_one (decr y (inv_plus x + z)) = inv_plus (plus_one x) + decr y z
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs x z F = mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_1 x z (inv_sum {a=Zpos (PositiveN F)} {b=x})
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs x z (N y) = rewrite mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs x z y in mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs_rhs_2 (inv_plus (plus_one x)) (decr y z)


public export total
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs : (x, z : Zahlen) -> (y : Natural) -> minus_one (decr y (inv_plus (x + z))) = inv_plus (plus_one x) + decr y (inv_plus z)
mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs x z y = rewrite inv_sum {a=x} {b=z} in mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs_rhs x (inv_plus z) y

public export total
mul_com_rhs_4_rhs_2_rhs_2_rhs_3 : (x : Zahlen) -> (y : Natural)
  -> decr y (inv_plus (mulPos (PositiveN y) x)) = inv_plus (mulPos (PositiveN y) (plus_one x))
  -> minus_one (decr y (inv_plus (x + mulPos (PositiveN y) x))) = inv_plus (plus_one x) + inv_plus (mulPos (PositiveN y) (plus_one x))
mul_com_rhs_4_rhs_2_rhs_2_rhs_3 x y s = rewrite sym s in mul_com_rhs_4_rhs_2_rhs_2_rhs_3_rhs x (mulPos (PositiveN y) x) y

public export total
mul_com_rhs_4_rhs_2_rhs_2 : (x : Zahlen) -> (y : Natural) -> decr y (inv_plus (mulPos (PositiveN y) x)) = inv_plus (mulPos (PositiveN y) (plus_one x))
mul_com_rhs_4_rhs_2_rhs_2 x F = sym (inv_sum_rhs_2_rhs_2 x)
mul_com_rhs_4_rhs_2_rhs_2 x (N y) = rewrite inv_sum {a=plus_one x} {b=mulPos (PositiveN y) (plus_one x)} in mul_com_rhs_4_rhs_2_rhs_2_rhs_3 x y (mul_com_rhs_4_rhs_2_rhs_2 x y)

public export total
mul_com_rhs_4_rhs_2 : (x : Zahlen) -> (y : Zahlen) -> y + mul y x = mul y (plus_one x)
mul_com_rhs_4_rhs_2 x Zero = Refl
mul_com_rhs_4_rhs_2 x (Zpos (PositiveN y)) = mul_com_rhs_4_rhs_2_rhs_4 x y
mul_com_rhs_4_rhs_2 x (Zneg (PositiveN y)) = mul_com_rhs_4_rhs_2_rhs_2 x y

public export total
mul_com_rhs_4_rhs_1_rhs_1 : Zpos (PositiveN x) = mulPos (PositiveN x) (Zpos (PositiveN F))
mul_com_rhs_4_rhs_1_rhs_1 {x = F} = Refl
mul_com_rhs_4_rhs_1_rhs_1 {x = (N t)} = rewrite sym (mul_com_rhs_4_rhs_1_rhs_1 {x=t}) in Refl

public export total
mul_com_rhs_4_rhs_1 : y = mul y (Zpos (PositiveN F))
mul_com_rhs_4_rhs_1 {y = Zero} = Refl
mul_com_rhs_4_rhs_1 {y = (Zpos (PositiveN t))} = mul_com_rhs_4_rhs_1_rhs_1
mul_com_rhs_4_rhs_1 {y = (Zneg (PositiveN t))} = rewrite sym (mul_com_rhs_4_rhs_1_rhs_1 {x=t}) in Refl

public export total
mul_com_rhs_4 : (x : Natural) -> (y : Zahlen) -> mulPos (PositiveN x) y = mul y (Zpos (PositiveN x))
mul_com_rhs_4 F y = mul_com_rhs_4_rhs_1
mul_com_rhs_4 (N x) y = rewrite mul_com_rhs_4 x y in (mul_com_rhs_4_rhs_2 (Zpos (PositiveN x)) y)

public export total
mul_com_rhs_2_rhs_1_rhs_2 : (x : Natural) -> (z : Zahlen) -> inv_plus (incr x z) = decr x (inv_plus z)
mul_com_rhs_2_rhs_1_rhs_2 F z = inv_sum_rhs_2_rhs_2 z
mul_com_rhs_2_rhs_1_rhs_2 (N x) z = rewrite sym $ mul_com_rhs_2_rhs_1_rhs_2 x z in inv_sum_rhs_2_rhs_2 (incr x z)

public export total
mul_com_rhs_2_rhs_1 : (x : Natural) -> (y : Natural) -> inv_plus (mulPos (PositiveN y) (Zpos (PositiveN x))) = mulPos (PositiveN y) (Zneg (PositiveN x))
mul_com_rhs_2_rhs_1 x F = Refl
mul_com_rhs_2_rhs_1 x (N y) = rewrite sym (mul_com_rhs_2_rhs_1 x y) in (mul_com_rhs_2_rhs_1_rhs_2 x (mulPos (PositiveN y) (Zpos (PositiveN x))))

public export total
mul_com_rhs_2_rhs_2 : (x : Natural) -> (y : Natural) -> inv_plus (inv_plus (mulPos (PositiveN y) (Zpos (PositiveN x)))) = inv_plus (mulPos (PositiveN y) (Zneg (PositiveN x)))
mul_com_rhs_2_rhs_2 x y = cong (mul_com_rhs_2_rhs_1 x y)

public export total
mul_com_rhs_2 : (x : Natural) -> (y : Zahlen) -> inv_plus (mul y (Zpos (PositiveN x))) = mul y (Zneg (PositiveN x))
mul_com_rhs_2 x Zero = Refl
mul_com_rhs_2 x (Zpos (PositiveN y)) = mul_com_rhs_2_rhs_1 x y
mul_com_rhs_2 x (Zneg (PositiveN y)) = mul_com_rhs_2_rhs_2 x y

public export total
mul_com: {x, y : Zahlen} -> mul x y = mul y x
mul_com {x = Zero} {y} = mul_com_rhs_1 y
mul_com {x = (Zpos (PositiveN x))} {y} = mul_com_rhs_4 x y
mul_com {x = (Zneg (PositiveN x))} {y} = rewrite mul_com_rhs_4 x y in (mul_com_rhs_2 x y)

public export total
distr3_rhs_2 : (y, t : Zahlen) -> (z : Positive x) -> mulPos z (y + t) = ((mulPos z y) + (mulPos z t))
distr3_rhs_2 y t (PositiveN F) = Refl
distr3_rhs_2 y t (PositiveN (N z1)) = rewrite (distr3_rhs_2 y t (PositiveN z1)) in eq4 y t (mulPos (PositiveN z1) y) (mulPos (PositiveN z1) t)

public export total
distr3_rhs_3 : (y, t : Zahlen) -> (z1 : Positive x) -> inv_plus (mulPos z1 (y + t)) = ((inv_plus (mulPos z1 y)) + (inv_plus (mulPos z1 t)))
distr3_rhs_3 y t z1 = rewrite distr3_rhs_2 y t z1 in inv_sum


public export total
distr3 : {y, t, z : Zahlen} -> mul z (y + t) = mul z y + (mul z t)
distr3 {z=Zero} = Refl
distr3 {z=(Zpos z1)} {y} {t} = distr3_rhs_2 y t z1
distr3 {z=(Zneg z1)} {y} {t} = distr3_rhs_3 y t z1

public export total
distr2 : {y, t, z : Zahlen} -> mul z (y + t) = mul z y + (mul t z)
distr2 {y} {t} {z} = rewrite mul_com {x=t} {y=z} in distr3

public export total
distr1 : {y, t, z : Zahlen} -> mul z (y + t) = mul y z + (mul t z)
distr1 {y} {t} {z} = rewrite mul_com {x=y} {y=z} in distr2

public export total
distr: {y, t, z : Zahlen} -> mul (y + t) z = mul y z + (mul t z)
distr {y} {t} {z} = rewrite mul_com {x=y+t} {y=z} in distr1

public export total
mul_assoc_rhs_2_rhs_3 : (x1 : Natural) -> (y : Zahlen) -> (z : Zahlen) ->
(mul (mulPos (PositiveN x1) y) z = mulPos (PositiveN x1) (mul y z)) -> mul (y + (mulPos (PositiveN x1) y)) z = ((mul y z) + (mulPos (PositiveN x1) (mul y z)))
mul_assoc_rhs_2_rhs_3 x1 y z prf = rewrite (sym prf) in distr {y} {t = mulPos (PositiveN x1) y} {z}

public export total
mul_assoc_pos : {x : Positive x1} -> {y : Zahlen} -> {z : Zahlen} -> mul (mulPos x y) z = mulPos x (mul y z)
mul_assoc_pos {x=PositiveN F} = Refl
mul_assoc_pos {x=PositiveN (N x1)} {y} {z} = mul_assoc_rhs_2_rhs_3 x1 y z (mul_assoc_pos {x = PositiveN x1} {y} {z})

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
mul_assoc {x=(Zneg x1)} {y} {z} = mul_assoc_neg x1 y z
