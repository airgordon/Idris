module Zahlen

import Natural as Nt

--- (x : Maybe (Positive _)) ->
public export
data Zahlen = Zero | Zpos (Nt.Positive x) | Zneg (Nt.Positive x)

--- isPositive : (Zahlen _) -> Bool
--- isPositive Zpos = True
--- isPositive _ = False
---

public export
total
plus_one : Zahlen -> Zahlen
plus_one Zero = Zpos (Nt.PositiveN F)
plus_one (Zpos (Nt.PositiveN x)) = Zpos (Nt.PositiveN (N x))
plus_one (Zneg (Nt.PositiveN F)) = Zero
plus_one (Zneg (Nt.PositiveN (N x))) = Zneg (Nt.PositiveN x)

public export
total
minus_one : Zahlen -> Zahlen
minus_one Zero = Zneg (Nt.PositiveN F)
minus_one (Zneg (Nt.PositiveN x)) = Zneg (Nt.PositiveN (N x))
minus_one (Zpos (Nt.PositiveN F)) = Zero
minus_one (Zpos (Nt.PositiveN (N x))) = Zpos (Nt.PositiveN x)

public export
total
addPos : Nt.Natural -> Zahlen -> Zahlen
addPos F y     = plus_one y
addPos (N x) y = plus_one (addPos x y)

public export
total
addNeg : Nt.Natural -> Zahlen -> Zahlen
addNeg F y     = minus_one y
addNeg (N x) y = minus_one (addNeg x y)

public export
total
(+) : Zahlen -> Zahlen -> Zahlen

(Zpos (Nt.PositiveN x)) + y = addPos x y
(Zneg (Nt.PositiveN x)) + y = addNeg x y
Zero + y = y

total
g3 : z = plus_one (minus_one z)
g3 { z =  Zero                       } = Refl
g3 { z = (Zneg (Nt.PositiveN n))     } = Refl
g3 { z = (Zpos (Nt.PositiveN F))     } = Refl
g3 { z = (Zpos (Nt.PositiveN (N n))) } = Refl

total
g3m : z = minus_one (plus_one z)
g3m {z = Zero} = Refl
g3m {z = Zpos (Nt.PositiveN n)} = Refl
g3m {z = Zneg (Nt.PositiveN F)} = Refl
g3m {z = Zneg (Nt.PositiveN (N n))} = Refl

total
plus_one_assoc : plus_one y + z = plus_one (y + z)
plus_one_assoc { y =  Zero                       } = Refl
plus_one_assoc { y = (Zpos (Nt.PositiveN y))     } = Refl
plus_one_assoc { y = (Zneg (Nt.PositiveN F))     } = g3
plus_one_assoc { y = (Zneg (Nt.PositiveN (N y))) } = g3

total
minus_one_assoc : minus_one y + z = minus_one (y + z)
minus_one_assoc { y =  Zero                       } = Refl
minus_one_assoc { y = (Zneg (Nt.PositiveN y))     } = Refl
minus_one_assoc { y = (Zpos (Nt.PositiveN F))     } = g3m
minus_one_assoc { y = (Zpos (Nt.PositiveN (N y))) } = g3m

total
pos_z_assoc_r3 : plus_one t + z = plus_one (t + z)
pos_z_assoc_r3 {t = Zero} = Refl
pos_z_assoc_r3 {t = Zpos (Nt.PositiveN n)} = Refl
pos_z_assoc_r3 {t = Zneg (Nt.PositiveN F)} = g3
pos_z_assoc_r3 {t = Zneg (Nt.PositiveN (N n))} = g3

total
neg_z_assoc_r3 : minus_one t + z = minus_one (t + z)
neg_z_assoc_r3 {t = Zero} = Refl
neg_z_assoc_r3 {t = Zneg (Nt.PositiveN n)} = Refl
neg_z_assoc_r3 {t = Zpos (Nt.PositiveN F)} = g3m
neg_z_assoc_r3 {t = Zpos (Nt.PositiveN (N n))} = g3m

total
pos_z_assoc_r :
((addPos n y) + z = addPos n (y + z)) ->
(plus_one (addPos n y)) + z = plus_one (addPos n (y + z))

pos_z_assoc_r p = rewrite (sym p) in pos_z_assoc_r3

total
neg_z_assoc_r :
((addNeg n y) + z = addNeg n (y + z)) ->
(minus_one (addNeg n y)) + z = minus_one (addNeg n (y + z))

neg_z_assoc_r p = rewrite (sym p) in neg_z_assoc_r3

total
pos_z_assoc : (x : Nt.Natural) -> (addPos x y) + z = addPos x (y + z)
pos_z_assoc F     = plus_one_assoc
pos_z_assoc (N n) = pos_z_assoc_r (pos_z_assoc n)

total
neg_z_assoc : (x : Nt.Natural) -> (addNeg x y) + z = addNeg x (y + z)
neg_z_assoc F     = minus_one_assoc
neg_z_assoc (N n) = neg_z_assoc_r (neg_z_assoc n)

total
z_assoc :   (x : Zahlen) ->
            (y : Zahlen) ->
            (z : Zahlen) ->
            x + y + z = x + (y + z)
z_assoc Zero y z = Refl
z_assoc (Zpos (Nt.PositiveN x)) y z = pos_z_assoc x
z_assoc (Zneg (Nt.PositiveN x)) y z = neg_z_assoc x
