module Monoid

import Semigroup

public export
interface Semigroup.Semigroup a => Monoid.Monoid a where

    neutral : a
    total left_neutral  : (x : a) -> (neutral `op` x) = x
    total right_neutral : (x : a) -> (x `op` neutral) = x

