module GroupTh

import Group
import Monoid
import Semigroup

only_one_left_inv_2 : Group.Group a => (i : a) -> (t : a) -> i = op i (op t (inv t))
only_one_left_inv_2 i t = rewrite right_inv {x=t} in sym (right_neutral i)

only_one_left_inv_1 : Group.Group a => (i : a) -> (t : a) -> i = op (op i t) (inv t)
only_one_left_inv_1 i t = rewrite (assoc {x=i} {y=t} {z=(inv t)}) in (only_one_left_inv_2 i t)

total only_one_left_inv  : Group.Group a => {i, t: a} ->  (i `op` t = Monoid.neutral) -> i = inv t
only_one_left_inv  {i} {t} p = rewrite sym (left_neutral (inv t)) in (rewrite sym p in (only_one_left_inv_1 i t))

only_one_right_inv_2 : Group.Group a => (i : a) -> (t : a) -> i = op (op (inv t) t) i
only_one_right_inv_2 i t = rewrite (left_inv {x=t}) in sym (left_neutral i)

only_one_right_inv_1 : Group.Group a => (i : a) -> (t : a) -> i = op (inv t) (op t i)
only_one_right_inv_1 i t = rewrite sym (assoc {x=(inv t)} {y=t} {z=i}) in (only_one_right_inv_2 i t)

total only_one_right_inv : Group.Group a => {i, t: a} -> (t `op` i = Monoid.neutral) -> i = inv t
only_one_right_inv {i} {t} p = rewrite sym (right_neutral (inv t)) in (rewrite sym p in (only_one_right_inv_1 i t))