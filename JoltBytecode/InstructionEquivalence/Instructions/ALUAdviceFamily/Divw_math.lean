import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Architectural DIVW/REMW values

The expansion-specific lemmas for the former two-advice signed word programs
were removed with that obsolete expansion. These definitions remain shared by
the signed statements and the unchanged unsigned word proofs.
-/

/-- The pure 64-bit value written by execute_DIVW. -/
def sail_divw_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_low else BitVec.toInt rs1_low
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_low else BitVec.toInt rs2_low
  let quotient :=
    if (rs2_int == 0) then -1 else Int.tdiv rs1_int rs2_int
  let quotient :=
    if LeanRV64D.Functions.not is_unsigned && (quotient ≥b (2 ^i 31))
    then -(2 ^i 31)
    else quotient
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-- The pure 64-bit value written by execute_REMW. -/
def sail_remw_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_low else BitVec.toInt rs1_low
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_low else BitVec.toInt rs2_low
  let remainder :=
    if (rs2_int == 0) then rs1_int else Int.tmod rs1_int rs2_int
  sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)

/-- The single advice word emitted by Rust for `DIVW`.

It is the signed word quotient represented in 64 bits, except that the
`i32::MIN / -1` overflow case is deliberately zero-extended so the unsigned
magnitude checks see `2^31`. -/
def divw_advice_value
    (dividend divisor : BitVec 64) : BitVec 64 :=
  let dividendWord := Sail.BitVec.extractLsb dividend 31 0
  let divisorWord := Sail.BitVec.extractLsb divisor 31 0
  if divisorWord = 0#32 then (-1 : BitVec 64)
  else if dividendWord = BitVec.intMin 32 ∧ divisorWord = (-1 : BitVec 32) then
    (1 : BitVec 64) <<< 31
  else sail_divw_value dividend divisor false

/-- The single advice word emitted by Rust for `REMW`.

Rust uses zero advice on word division by zero; otherwise it supplies the
zero-extended magnitude of the signed word quotient. -/
def remw_advice_value
    (dividend divisor : BitVec 64) : BitVec 64 :=
  let divisorWord := Sail.BitVec.extractLsb divisor 31 0
  if divisorWord = 0#32 then 0
  else bv_abs (sail_divw_value dividend divisor false)

end
