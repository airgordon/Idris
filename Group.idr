module Group

import Monoid

public export
interface Monoid.Monoid a => Group.Group a where
    inv : a -> a
    total left_inv  : {x : a} -> ((inv x) `plus` x) = neutral
    total right_inv : {x : a} -> (x `plus` (inv x)) = neutral
