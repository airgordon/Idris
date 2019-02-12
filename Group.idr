module Group

import Monoid
import Semigroup

public export
interface Monoid.Monoid a => Group.Group a where
    inv : a -> a
    total right_inv : {x : a} -> (x `op` (inv x)) = Monoid.neutral
    total left_inv  : {x : a} -> ((inv x) `op` x) = Monoid.neutral
