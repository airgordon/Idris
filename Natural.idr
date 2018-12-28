module Natural

import Either3

public export
data Natural: Type where
    F : Natural
    N : Natural -> Natural

public export
total (+): Natural -> Natural -> Natural
F + x = x
(N x) + y = N (x + y)

public export
total
nt_assoc :  (x : Natural) ->
            (y : Natural) ->
            (z : Natural) ->
            x + y + z = x + (y + z)
nt_assoc F y z = Refl
nt_assoc (N x) y z = cong (nt_assoc x y z)

public export
data Positive: Natural -> Type where
    PositiveN : (x: Natural) -> Positive (N x)