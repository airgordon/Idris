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

--- public export
--- (+) : Zahlen -> Zahlen -> Zahlen
---
--- (Zpos (Nt.PositiveN F))     + y = plus_one y
--- (Zpos (Nt.PositiveN (N x))) + y = (Zpos (Nt.PositiveN x)) + (plus_one y)
--- (Zneg (Nt.PositiveN F))     + y = minus_one y
--- (Zneg (Nt.PositiveN (N x))) + y = (Zneg (Nt.PositiveN x)) + (minus_one y)
--- Zero + y = y


public export
total
addPos : Nt.Natural -> Zahlen -> Zahlen
addPos F y     = plus_one y
addPos (N x) y = addPos x (plus_one y)

public export
total
addNeg : Nt.Natural -> Zahlen -> Zahlen
addNeg F y     = minus_one y
addNeg (N x) y = addNeg x (minus_one y)

public export
total
(+) : Zahlen -> Zahlen -> Zahlen

(Zpos (Nt.PositiveN x)) + y = addPos x y
(Zneg (Nt.PositiveN x)) + y = addNeg x y
Zero + y = y

total g4 : (y: Natural) -> (z: Zahlen) -> addNeg y z = plus_one (addNeg y (minus_one z))
g4 F z = ?g41
g4 (N y) z = ?g42


total
plus_one_assoc : (y, z: Zahlen) -> plus_one y + z = plus_one (y + z)
plus_one_assoc Zero z = Refl
plus_one_assoc (Zneg (Nt.PositiveN y)) z = ?g2
plus_one_assoc (Zneg (Nt.PositiveN F)) z = ?g3
plus_one_assoc (Zneg (Nt.PositiveN (N y))) z = ?g4

total
pos_z_assoc : (x : Nt.Natural) -> (y, z: Zahlen) -> (addPos x y) + z = addPos x (y + z)
pos_z_assoc F y z = plus_one_assoc y z


neg_z_assoc : (x : Nt.Natural) -> (y, z: Zahlen) -> (addNeg x y) + z = addNeg x (y + z)

total
z_assoc :   (x : Zahlen) ->
            (y : Zahlen) ->
            (z : Zahlen) ->
            x + y + z = x + (y + z)
z_assoc Zero y z = Refl
z_assoc (Zpos (Nt.PositiveN x)) y z = pos_z_assoc x y z
z_assoc (Zneg (Nt.PositiveN x)) y z = neg_z_assoc x y z

