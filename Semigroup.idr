module Semigroup

public export
interface Semigroup a where
    total op : a -> a -> a

    total assoc: {x, y, z : a} -> (x `op` y) `op` z = x `op` (y `op` z)
