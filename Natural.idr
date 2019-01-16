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
nt_assoc :  {x : Natural} ->
            {y : Natural} ->
            {z : Natural} ->
            x + y + z = x + (y + z)
nt_assoc {x = F  } = Refl
nt_assoc {x = N t} = cong nt_assoc

public export
data Positive: Natural -> Type where
    PositiveN : (x: Natural) -> Positive (N x)

public export total
mul : Natural -> Natural -> Natural
mul F y = F
mul (N t) y = y + mul t y