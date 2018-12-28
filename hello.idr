module Main

import Semigroup
import Monoid
import Natural as Nt
import Zahlen

Semigroup.Semigroup Nt.Natural where
    plus = (+)
    assoc = nt_assoc

Monoid.Monoid Nt.Natural where
    neutral = F
    left_neutral x = Refl

    right_neutral F = Refl
    right_neutral (N x) = cong (right_neutral x)

oneZ : Zahlen
oneZ = plus_one Zero

twoZ : Zahlen
twoZ = plus_one oneZ

threeZ : Zahlen
threeZ = plus_one twoZ

m_oneZ : Zahlen
m_oneZ = minus_one Zero

m_twoZ : Zahlen
m_twoZ = minus_one m_oneZ

m_threeZ : Zahlen
m_threeZ = minus_one m_twoZ




