module Main

import Semigroup
import Monoid
import Group
import Natural as Nt
import Zahlen
import DivMod
import MonoidTh
import GroupTh
import DPairs
import LTE2

import Data.Vect

Semigroup.Semigroup Nt.Natural where
    op = (+)
    assoc = nt_assoc

Monoid.Monoid Nt.Natural where
    neutral = F
    left_neutral x = Refl
    right_neutral F = Refl
    right_neutral (N x) = cong (right_neutral x)

Semigroup.Semigroup Zahlen where
    op = (+)
    assoc = z_assoc


Monoid.Monoid Zahlen where
    neutral = Zero

    left_neutral x = Refl

    right_neutral x = Zahlen.right_neutral

Group.Group Zahlen where
    inv = Zahlen.inv_plus
    left_inv = Zahlen.left_inv
    right_inv = Zahlen.right_inv

oneZ : Zahlen
oneZ = plus_one Zero

twoZ : Zahlen
twoZ = plus_one oneZ

threeZ : Zahlen
threeZ = plus_one twoZ

fourZ : Zahlen
fourZ = plus_one threeZ

m_oneZ : Zahlen
m_oneZ = minus_one Zero

m_twoZ : Zahlen
m_twoZ = minus_one m_oneZ

m_threeZ : Zahlen
m_threeZ = minus_one m_twoZ

nz_m_threeZ: NonZero Main.m_threeZ
nz_m_threeZ = NZneg

nz_twoZ: NonNeg Main.twoZ
nz_twoZ = NNpos

nz_fourZ: NonNeg Main.fourZ
nz_fourZ = NNpos
