module Utils


data Greater: Natural -> Natural -> Type where
    GreaterF : (t : Natural) -> Greater (N t) F
    GreaterN : Greater x y  -> Greater (N x) (N y)

Compare : Natural -> Natural -> Type
Compare x y = Either3 (Greater x y) (x = y) (Greater y x)

total
nxt : Compare x y -> Compare (N x) (N y)
nxt (Middle3 t) = Middle3 (cong t)
nxt (Left3 x)   = Left3  (GreaterN x)
nxt (Right3 x)  = Right3 (GreaterN x)

total
cmpr: (x: Natural) -> (y: Natural) -> Compare x y
cmpr  F       F  = Middle3 Refl
cmpr (N x)    F  = Left3  (GreaterF x)
cmpr  F    (N x) = Right3 (GreaterF x)
cmpr (N x) (N y) = nxt (cmpr x y)


data Positive: Natural -> Type where
    PositiveN : (x: Natural) -> Positive (N x)

one : Positive (N F)
one = PositiveN F

data Simple: (n : Natural) -> (p: Positive _) -> Type where
    G : (n : Natural) -> Simple n Natural.one


total
induct : (Prop : Nt -> Type)
 -> Prop F
 -> ({n: Nt} -> Prop n -> Prop (N n)) -- {n: Nt} -> why is necessary?
 -> (x : Nt)
 -> (Prop x)
induct _  z _    F     = z
induct pr z step (N y) = step (induct pr z step y)