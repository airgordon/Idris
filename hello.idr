module Main

import Semigroup
import Monoid
import Group
import Natural as Nt
import Zahlen
import DivMod
import MonoidTh
import GroupTh

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
--
m_oneZ : Zahlen
m_oneZ = minus_one Zero

m_twoZ : Zahlen
m_twoZ = minus_one m_oneZ

m_threeZ : Zahlen
m_threeZ = minus_one m_twoZ

y: 2 = 3 -> Void
y Refl impossible

g: Nt.Positive Nt.F -> Void
g (PositiveN _) impossible

k: Void -> 5 = 5
k = absurd

j: NonZero Main.m_threeZ
j = NZneg

jj: NonNeg Main.twoZ
jj = NNpos

jj2: NonNeg Main.fourZ
jj2 = NNpos

gg: Positive2 $ N . N . N . N . N $ F
gg = Positive2N

total
fg : (z : Zahlen) -> NonZero z -> Zahlen
fg (Zpos s) _ = Zero
fg (Zneg s) _ = Zpos (PositiveN F)

f : Integer -> Type
f x = x * x = 25

h : Exists Main.f
h = Evidence 5 Refl

r : Type
r = Subset Integer f

hg1 : Main.r
hg1 = Element 5 Refl

hg2 : Main.r
hg2 = Element (-5) Refl

m : DPair Integer Main.f
m = (5 ** Refl)

vectn : Nat -> Type
vectn x = Vect x String

p : DPair Nat Main.vectn
p = (1 ** ["Hello"])

inv_ex_rhs_1 : (P : a -> Type) -> (x : a) -> (pf : P x) -> ((x1 : a) -> P x1 -> Void) -> Void
inv_ex_rhs_1 P x pf f = f x pf

inv_ex : {a: Type} -> {P: a -> Type} -> Exists P -> Not ((x:a) -> Not (P x))
inv_ex {P} (Evidence x pf) = inv_ex_rhs_1 P x pf

inv_any : {a : Type} -> {P: a -> Type} -> ((x : a) -> P x) -> Not (Exists (\t => (Not (P t))))
inv_any f (Evidence r pf) = pf (f r)

rg : Divide Main.jj2 Main.jj {t = Main.jj}
rg = MkDiv Main.jj2 Main.jj Refl

hg3 : Main.r
hg3 = Element (-5) Refl
