module Monoid

import Semigroup

public export
interface Semigroup.Semigroup a => Monoid.Monoid a where
    neutral : a
    total left_neutral  : (x : a) -> (neutral `op` x) = x
    total right_neutral : (x : a) -> (x `op` neutral) = x

    total one_right_neutral : (e: a) -> (y: a) -> e `op` y = y -> e = Monoid.neutral
    total one_left_neutral  : (e: a) -> (y: a) -> y `op` e = y -> e = Monoid.neutral