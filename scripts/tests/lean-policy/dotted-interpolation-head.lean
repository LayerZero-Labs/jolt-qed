import Lean
open Lean Parser in
def Foo.s! : Parser := ident
syntax "baz" Foo.s!"{" : term
theorem bad : False := by admit
-- "}"
