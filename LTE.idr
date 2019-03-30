import Zahlen
import Natural

public export
data LTE : Zahlen -> Zahlen -> Type where
    LteZeroPos : NonNeg t -> LTE Zero t
    LteIncr : LTE x y -> LTE (plus_one x) (plus_one y)
    LteDecr : LTE x y -> LTE (minus_one x) (minus_one y)
    --LteDecr2 : LTE x y -> LTE (minus_one x) (minus_one (minus_one y))

-- g: LTE Zero (Zneg (PositiveN F))
-- g = LteDecr2 (LteIncr (LteZeroPos NNzero))

total
cmpZ_rhs_4 : LTE Zero (Zneg y) -> Void
cmpZ_rhs_4 (LteZeroPos x) =?dhgkjdshfg_1
cmpZ_rhs_4 (LteIncr (LteZeroPos x)) =?dhgkjdshfg_2

--v : Void
--v = cmpZ_rhs_4 g

total
cmpZ : (z : Zahlen) -> Dec (LTE Zero z)
cmpZ Zero = Yes (LteZeroPos NNzero)
cmpZ (Zpos y) = Yes (LteZeroPos NNpos)
cmpZ (Zneg y) = No cmpZ_rhs_4

total
incrDecLte : Dec (LTE x y) -> Dec ( LTE (plus_one x) (plus_one y))
incrDecLte (Yes prf) = Yes (LteIncr prf)
incrDecLte {x} {y} (No contra) = No (\t => contra (rewrite g3m {z=y} in (rewrite g3m {z=x} in (LteDecr t))))

total
decrDecLte : Dec (LTE x y) -> Dec ( LTE (minus_one x) (minus_one y))
decrDecLte (Yes prf) = Yes (LteDecr prf)
decrDecLte {x} {y} (No contra) = No (\t => contra (rewrite g3 {z=y} in (rewrite g3 {z=x} in (LteIncr t))))

total
cmp : (x, y : Zahlen) -> Dec (LTE x y)
cmp Zero y = cmpZ y
cmp (Zpos (PositiveN F)) y = rewrite g3 {z=y} in incrDecLte (cmpZ (minus_one y))
cmp (Zpos (PositiveN (N x))) y = rewrite g3 {z=y} in incrDecLte (cmp (minus_one (Zpos (PositiveN (N x)))) (minus_one y))
cmp (Zneg (PositiveN F)) y = rewrite g3m {z=y} in decrDecLte (cmpZ (plus_one y))
cmp (Zneg (PositiveN (N x))) y = rewrite g3m {z=y} in decrDecLte (cmp (plus_one (Zneg (PositiveN (N x)))) (plus_one y))
