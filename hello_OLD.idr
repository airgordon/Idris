module Main

data Nt: Type where
    F : Nt
    N : Nt -> Nt

total vl : Nat -> Nt
vl Z = F
vl (S x) = N (vl x)

total isZero1 : Nt -> Bool
isZero1 F = True
isZero1 (N x) = False

data Vct : Nt -> Type -> Type where
   Nil  : Vct F b
   (::) : b -> Vct k b -> Vct (N k) b


yy: Vct F Double
yy = Nil

xx: Vct (vl 5) Double
xx = 1.45640 :: 1.4560 :: 4561.0 :: 12456.0 :: 456.0 :: yy

zz: Vct (vl 5) String
zz = "3" :: "2" :: "3" :: "7" :: "5" :: Nil

total f: {a: Type} -> {x : Nt} -> Vct (N x) a -> Vct x a
f (x :: xs) = xs

using (x:a, y:a, xs:Vct n a)
  data IsElem : a -> Vct n a -> Type where
     Here  : IsElem x (x :: xs)
     There : IsElem x xs -> IsElem x (y :: xs)

h : IsElem "7" Main.zz
h = There (There (There Here))

g: Vct (vl 6) Double
g = 5.5784 :: xx

a : Nt
a = N F

b : Nt
b = N F



