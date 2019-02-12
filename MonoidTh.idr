module MonoidTh

import Semigroup
import Monoid

total only_one_left_neutral : Monoid.Monoid a => (e: a) -> ((y: a) -> (e `op` y = y)) -> e = Monoid.neutral
only_one_left_neutral e f = rewrite sym (right_neutral e) in (rewrite sym (f neutral) in Refl)

total only_one_right_neutral : Monoid.Monoid a => (e: a) -> ((y: a) -> (y `op` e = y)) -> e = Monoid.neutral
only_one_right_neutral e f = rewrite sym (left_neutral e) in (rewrite sym (f neutral) in Refl)

-- total one_left_neutral  : (e: a) -> (y: a) -> y `op` e = y -> e = Monoid.neutral
