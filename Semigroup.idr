module Semigroup

public export
interface Semigroup a where
    total plus : a -> a -> a

    total assoc: (x, y, z : a) -> (x `plus` y) `plus` z = x `plus` (y `plus` z)