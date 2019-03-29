module DPairs

import Data.Vect

square : Integer -> Type
square x = x * x = 25

thereAreSqNum : Exists DPairs.square
thereAreSqNum = Evidence 5 Refl

squareNum : Type
squareNum = Subset Integer DPairs.square

_5isInSquare : DPairs.squareNum
_5isInSquare = Element 5 Refl

_m5isInSquare : DPairs.squareNum
_m5isInSquare = Element (-5) Refl

_5isSquare : DPair Integer DPairs.square
_5isSquare = (5 ** Refl)

vectn : Nat -> Type
vectn x = Vect x String

-- sigma type
thereAreVectN : DPair Nat DPairs.vectn
thereAreVectN = (1 ** ["Hello"])

-- product type
anyLenVect: (x: Nat) -> vectn x
anyLenVect Z = []
anyLenVect (S k) = "anyLenVect" :: (anyLenVect k)

inv_ex_rhs_1 : (P : a -> Type) -> (x : a) -> (pf : P x) -> ((x1 : a) -> P x1 -> Void) -> Void
inv_ex_rhs_1 P x pf square = square x pf

inv_ex : {a: Type} -> {P: a -> Type} -> Exists P -> Not ((x:a) -> Not (P x))
inv_ex {P} (Evidence x pf) = inv_ex_rhs_1 P x pf

inv_any : {a : Type} -> {P: a -> Type} -> ((x : a) -> P x) -> Not (Exists (\t => (Not (P t))))
inv_any square (Evidence squareNum pf) = pf (square squareNum)


data DP : (t : Type) -> ((x:t) -> Type) -> Type where
  Mk : (t : Type) -> (f: ((x:t) -> Type)) -> (y:t) -> (f y) -> DP t f

_5isInSquare2 : DP Integer DPairs.square
_5isInSquare2 = Mk Integer DPairs.square 5 Refl
