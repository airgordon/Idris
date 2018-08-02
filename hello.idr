module Main

data Nt: Type where
    F : Nt
    N : Nt -> Nt

total (+): Nt -> Nt -> Nt
F + x = x
(N x) + y = N (x + y)

plus_commutes_Z2 : {m : Nt} -> m = m + F

plus_commutes_Z : F + m = m + F
plus_commutes_Z {m} = plus_commutes_Z2

total
induct : (Prop : Nt -> Type)
 -> Prop F
 -> ({n: Nt} -> Prop n -> Prop (N n)) -- {n: Nt} -> why is necessary?
 -> (x : Nt)
 -> (Prop x)
induct _  z _    F     = z
induct pr z step (N y) = step (induct pr z step y)

f : (x : Nt) -> (y : Nt) -> Type
f x y = (y + x = x + y)

g : (y : Nt) -> (x : Nt) -> Type
g x y = (y + x = x + y)

khwgriwhig: {z : Nt}
  -> {w : Nt}
  -> (N z) + w = N (w + z)
  -> (N z) + (N w) = (N w) + (N z)

plus_inter_step : {x : Nt} -> {y : Nt} -> (y + x = x + y) -> ((N y) + x = x + N y)
plus_inter_step {x} {y} = let d = induct (g (N y)) (plus_commutes_Z {m=N y}) khwgriwhig x in ?trivial1 d

plus_commutes : (n : Nt) -> (m : Nt) -> n + m = m + n
plus_commutes F m = plus_commutes_Z
plus_commutes n m = induct (f m) (plus_commutes_Z {m}) plus_inter_step n -- how to carry and inline (f m)
