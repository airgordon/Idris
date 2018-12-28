module Either3

public export
data Either3: (a, b, c: Type) -> Type where
    Left3   : (x : a) -> Either3 a b c
    Middle3 : (x : b) -> Either3 a b c
    Right3  : (x : c) -> Either3 a b c