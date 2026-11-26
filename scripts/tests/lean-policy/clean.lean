/- A comment that mentions sorry, /- nested -/ admit and axiom bad : False. -/
-- maxHeartbeats in a line comment
/-- A docstring: `native_decide` is banned. -/
def message : String := "sorry, admit, bv_decide"
def raw : String := r#"sorryAx "and" axiom bad : False"#
def quote : Char := '"'
def brace : String := "};"
def «name with spaces» : Nat := 0
def x' : Nat := «name with spaces»
def shown : String := s!"{x'} and {message}"
set_option maxRecDepth 750 in
def is_CSR_accessible : Nat := 0
def joined : String := s!"{", ".intercalate ["a", "b"]} -- not a comment"
def negated : Bool := !s!"{", ".intercalate ["a", "b"]}" == "" && !r"\" == "" && !'"' == 'a'
