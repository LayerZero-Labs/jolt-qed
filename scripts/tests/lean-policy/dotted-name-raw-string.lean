import Lean
open Lean Parser in
def Foo.r : Parser := ident
syntax "baz" Foo.r"a\"x" : term
theorem bad : False := by admit
-- "
