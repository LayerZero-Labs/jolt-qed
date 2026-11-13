import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.metadata
import JoltConstraints.ConstraintGen.Generated.R1CS
import JoltConstraints.ConstraintGen.Generated.Relations
import JoltConstraints.ConstraintGen.Generated.KindTables

set_option autoImplicit false

/-! # What the generated constraint data means (T3)

This file is the handwritten, trusted part of the T3 check. It says which
witness column each name in the generated data stands for, and how a row or a
claim constrains a witness. `ConstraintGen/Equiv.lean` proves that, under this
reading, the generated data and the handwritten constraints are equivalent.

Each map below is an exhaustive `match` on a generated type. A name that Jolt
adds or renames changes the generated type, and this file then fails to
elaborate until someone maps the new name. -/

namespace JoltConstraints.ConstraintGen

open scoped BigOperators
open Generated

variable {F : Type} [Field F] {params : WitnessParams}

/-! ## R1CS rows -/

/-- The witness value of an R1CS variable at cycle `t`. `One` is the constant
column; `Branch` is the instruction flag of that name, one of Jolt's two
product-factor columns.
Jolt: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`RV64_VARIABLE_NAMES`). -/
def Generated.R1CSVar.value (w : WitnessType F params) (t : Fin params.traceLength) : R1CSVar → F
  | .One => 1
  | .LeftInstructionInput => w.LeftInstructionInput t
  | .RightInstructionInput => w.RightInstructionInput t
  | .Product => w.Product t
  | .ShouldBranch => w.ShouldBranch t
  | .PC => w.PC t
  | .UnexpandedPC => w.UnexpandedPC t
  | .Imm => w.Imm t
  | .RamAddress => w.RamAddress t
  | .Rs1Value => w.Rs1Value t
  | .Rs2Value => w.Rs2Value t
  | .RdWriteValue => w.RdWriteValue t
  | .RamReadValue => w.RamReadValue t
  | .RamWriteValue => w.RamWriteValue t
  | .LeftLookupOperand => w.LeftLookupOperand t
  | .RightLookupOperand => w.RightLookupOperand t
  | .NextUnexpandedPC => w.NextUnexpandedPC t
  | .NextPC => w.NextPC t
  | .NextIsVirtual => w.NextIsVirtual t
  | .NextIsFirstInSequence => w.NextIsFirstInSequence t
  | .LookupOutput => w.LookupOutput t
  | .ShouldJump => w.ShouldJump t
  | .OpFlags_AddOperands => w.OpFlags .AddOperands t
  | .OpFlags_SubtractOperands => w.OpFlags .SubtractOperands t
  | .OpFlags_MultiplyOperands => w.OpFlags .MultiplyOperands t
  | .OpFlags_Load => w.OpFlags .Load t
  | .OpFlags_Store => w.OpFlags .Store t
  | .OpFlags_Jump => w.OpFlags .Jump t
  | .OpFlags_WriteLookupOutputToRD => w.OpFlags .WriteLookupOutputToRD t
  | .OpFlags_VirtualInstruction => w.OpFlags .VirtualInstruction t
  | .OpFlags_Assert => w.OpFlags .Assert t
  | .OpFlags_DoNotUpdateUnexpandedPC => w.OpFlags .DoNotUpdateUnexpandedPC t
  | .OpFlags_Advice => w.OpFlags .Advice t
  | .OpFlags_IsCompressed => w.OpFlags .IsCompressed t
  | .OpFlags_IsFirstInSequence => w.OpFlags .IsFirstInSequence t
  | .OpFlags_IsLastInSequence => w.OpFlags .IsLastInSequence t
  | .Branch => w.InstructionFlags .Branch t
  | .NextIsNoop => w.NextIsNoop t

/-- The value of a linear combination: the sum of coefficient times value.
For example, `[(x, 1), (y, -1)]` has value `1 * x + (-1 * y + 0)`. -/
def lcValue {V : Type} (value : V → F) (lc : List (V × Int)) : F :=
  lc.foldr (fun term acc => (term.2 : F) * value term.1 + acc) 0

/-- A row holds for a witness when `A · B = C` at every padded cycle. -/
def R1CSRow.Holds (row : R1CSRow R1CSVar) (w : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    lcValue (R1CSVar.value w t) row.a * lcValue (R1CSVar.value w t) row.b =
      lcValue (R1CSVar.value w t) row.c

/-! ## Per-kind flags -/

/-- The Jolt instruction kind of a Lean instruction: the kind with the same
name. Every `JoltISA.Instr` constructor is named after its Jolt kind
(`JoltInstructionKind::name`). -/
def kindOf : JoltISA.Instr → JoltKind
  | .ADDI .. => .ADDI
  | .ADDIW .. => .ADDIW
  | .ANDI .. => .ANDI
  | .ORI .. => .ORI
  | .XORI .. => .XORI
  | .SLTI .. => .SLTI
  | .SLTIU .. => .SLTIU
  | .LUI .. => .LUI
  | .AUIPC .. => .AUIPC
  | .JAL .. => .JAL
  | .JALR .. => .JALR
  | .BEQ .. => .BEQ
  | .BNE .. => .BNE
  | .BLT .. => .BLT
  | .BGE .. => .BGE
  | .BLTU .. => .BLTU
  | .BGEU .. => .BGEU
  | .FENCE => .FENCE
  | .ADD .. => .ADD
  | .ADDW .. => .ADDW
  | .SUB .. => .SUB
  | .SUBW .. => .SUBW
  | .MUL .. => .MUL
  | .MULW .. => .MULW
  | .MULHU .. => .MULHU
  | .ANDN .. => .ANDN
  | .VirtualMULI .. => .VirtualMULI
  | .VirtualMULIW .. => .VirtualMULIW
  | .VirtualPow2 .. => .VirtualPow2
  | .VirtualPow2W .. => .VirtualPow2W
  | .VirtualPow2I .. => .VirtualPow2I
  | .VirtualPow2IW .. => .VirtualPow2IW
  | .VirtualShiftRightBitmask .. => .VirtualShiftRightBitmask
  | .VirtualShiftRightBitmaskI .. => .VirtualShiftRightBitmaskI
  | .VirtualShiftRightBitmaskW .. => .VirtualShiftRightBitmaskW
  | .VirtualSRLI .. => .VirtualSRLI
  | .VirtualSRAI .. => .VirtualSRAI
  | .VirtualSRLIW .. => .VirtualSRLIW
  | .VirtualSRAIW .. => .VirtualSRAIW
  | .VirtualSRL .. => .VirtualSRL
  | .VirtualSRA .. => .VirtualSRA
  | .VirtualSRLW .. => .VirtualSRLW
  | .VirtualSRAW .. => .VirtualSRAW
  | .VirtualROTRI .. => .VirtualROTRI
  | .VirtualROTRIW .. => .VirtualROTRIW
  | .VirtualRev8W .. => .VirtualRev8W
  | .VirtualXORROT32 .. => .VirtualXORROT32
  | .VirtualXORROT24 .. => .VirtualXORROT24
  | .VirtualXORROT16 .. => .VirtualXORROT16
  | .VirtualXORROT63 .. => .VirtualXORROT63
  | .VirtualXORROTL1 .. => .VirtualXORROTL1
  | .VirtualXORROTW16 .. => .VirtualXORROTW16
  | .VirtualXORROTW12 .. => .VirtualXORROTW12
  | .VirtualXORROTW8 .. => .VirtualXORROTW8
  | .VirtualXORROTW7 .. => .VirtualXORROTW7
  | .VirtualXORROTW22 .. => .VirtualXORROTW22
  | .VirtualXORROTW19 .. => .VirtualXORROTW19
  | .VirtualXORROTW6 .. => .VirtualXORROTW6
  | .OR .. => .OR
  | .XOR .. => .XOR
  | .AND .. => .AND
  | .SLT .. => .SLT
  | .SLTU .. => .SLTU
  | .VirtualWindowMaskB .. => .VirtualWindowMaskB
  | .VirtualWindowMaskH .. => .VirtualWindowMaskH
  | .VirtualWindowMaskW .. => .VirtualWindowMaskW
  | .VirtualPext .. => .VirtualPext
  | .VirtualPextSigned .. => .VirtualPextSigned
  | .VirtualShiftDataB .. => .VirtualShiftDataB
  | .VirtualShiftDataH .. => .VirtualShiftDataH
  | .VirtualShiftDataW .. => .VirtualShiftDataW
  | .VirtualSignExtendWord .. => .VirtualSignExtendWord
  | .VirtualZeroExtendWord .. => .VirtualZeroExtendWord
  | .VirtualMovsign .. => .VirtualMovsign
  | .VirtualLoadB .. => .VirtualLoadB
  | .VirtualLoadH .. => .VirtualLoadH
  | .VirtualLoadW .. => .VirtualLoadW
  | .VirtualStoreB .. => .VirtualStoreB
  | .VirtualStoreH .. => .VirtualStoreH
  | .VirtualStoreW .. => .VirtualStoreW
  | .LD .. => .LD
  | .SD .. => .SD
  | .VirtualAdvice .. => .VirtualAdvice
  | .VirtualAdviceLoad .. => .VirtualAdviceLoad
  | .VirtualHostIO => .VirtualHostIO
  | .VirtualAssertEQ .. => .VirtualAssertEQ
  | .VirtualAssertValidDiv0 .. => .VirtualAssertValidDiv0
  | .VirtualNegateIf .. => .VirtualNegateIf
  | .VirtualAssertValidUnsignedRemainder .. => .VirtualAssertValidUnsignedRemainder
  | .VirtualAssertMulUNoOverflow .. => .VirtualAssertMulUNoOverflow
  | .VirtualAssertLTE .. => .VirtualAssertLTE

/-- The stamp class of a row, as the generated stamp table keys it:
`(virtual_sequence_remaining, is_first_in_sequence, is_compressed)`, with every
nonzero count replaced by `1`. Jolt reads the count only through `is_some`,
`== Some(0)` and `unwrap_or(0) != 0` (`jolt_instruction!` in
`crates/jolt-riscv/src/lib.rs`), so all nonzero counts give the same flags. The
generator checks this on the counts `1..=1024` and `65535`. -/
def stampClass (row : JoltInstructionRow) : Option Nat × Bool × Bool :=
  (row.virtual_sequence_remaining.map (fun n => if n = 0 then 0 else 1),
    row.is_first_in_sequence, row.is_compressed)

/-- The circuit flags that Jolt adds for a stamp class, from the generated
stamp table. -/
def stampFlags (key : Option Nat × Bool × Bool) : List CircuitFlags :=
  (stampCircuitFlags.lookup key).getD []

/-- The circuit flags of a bytecode row according to the generated tables:
the flags of its kind at the canonical stamp, plus the flags its stamp adds. -/
def generatedCircuitFlags (row : JoltInstructionRow) : List CircuitFlags :=
  kindCircuitFlags (kindOf row.instruction) ++ stampFlags (stampClass row)

/-! ## The four relations

A claim of an unbatched relation says `input = Σ_j weight(j) · output(j)`,
where `j` runs over the output relation's variables. The weights here are of
three shapes (Jolt: `crates/jolt-claims/src/protocols/jolt/ids.rs`,
`JoltDerivedId`, and the four `unbatched_relation` functions):

* `*_EqCycle` is `eq(r_cycle, cycle)` over the cycle variables only. The
  output is a polynomial over (address, cycle), so the claim sums the output
  over every address at the same cycle: over RAM addresses for
  `RamReadWrite_EqCycle` and over the 128 registers for
  `RegistersReadWrite_EqCycle`.
* `InstructionInput_EqProduct` is `eq` over the cycle variables of the
  product sumcheck. The claim is the same identity at every cycle.
* `SpartanShift_EqPlusOne*` is `eq+1(r, cycle)`, which selects the next cycle.
  At the last cycle there is no next one, so the right side is zero there.
  These are the only claims with `offset = true`.

Read pointwise, each claim is an identity between witness columns at every
cycle. `Holds` states that identity. -/

/-- The value at cycle `t` of a polynomial that depends only on the cycle.
The six address-indexed polynomials evaluate to `0` here; `ramValue` and
`registerValue` give their values. -/
def Generated.RelationPoly.cycleValue (w : WitnessType F params) (t : Fin params.traceLength) :
    RelationPoly → F
  | .Imm => w.Imm t
  | .InstructionFlags_IsNoop => w.InstructionFlags .IsNoop t
  | .InstructionFlags_LeftOperandIsPC => w.InstructionFlags .LeftOperandIsPC t
  | .InstructionFlags_LeftOperandIsRs1Value => w.InstructionFlags .LeftOperandIsRs1Value t
  | .InstructionFlags_RightOperandIsImm => w.InstructionFlags .RightOperandIsImm t
  | .InstructionFlags_RightOperandIsRdWriteValue => w.InstructionFlags .RightOperandIsRdWriteValue t
  | .InstructionFlags_RightOperandIsRs2Value => w.InstructionFlags .RightOperandIsRs2Value t
  | .LeftInstructionInput => w.LeftInstructionInput t
  | .NextIsFirstInSequence => w.NextIsFirstInSequence t
  | .NextIsNoop => w.NextIsNoop t
  | .NextIsVirtual => w.NextIsVirtual t
  | .NextPC => w.NextPC t
  | .NextUnexpandedPC => w.NextUnexpandedPC t
  | .OpFlags_IsFirstInSequence => w.OpFlags .IsFirstInSequence t
  | .OpFlags_VirtualInstruction => w.OpFlags .VirtualInstruction t
  | .PC => w.PC t
  | .RamInc => w.RamInc t
  | .RamReadValue => w.RamReadValue t
  | .RamWriteValue => w.RamWriteValue t
  | .RdInc => w.RdInc t
  | .RdWriteValue => w.RdWriteValue t
  | .RightInstructionInput => w.RightInstructionInput t
  | .Rs1Value => w.Rs1Value t
  | .Rs2Value => w.Rs2Value t
  | .UnexpandedPC => w.UnexpandedPC t
  | .RamRa => 0
  | .RamVal => 0
  | .RdWa => 0
  | .RegistersVal => 0
  | .Rs1Ra => 0
  | .Rs2Ra => 0

/-- The value at RAM address `k` and cycle `t`: `RamRa` and `RamVal` read the
address, every cycle polynomial reads cycle `t`, and register polynomials are
`0`. -/
def Generated.RelationPoly.ramValue (w : WitnessType F params) (k : Fin params.ramSize)
    (t : Fin params.traceLength) : RelationPoly → F
  | .RamRa => w.RamRa k t
  | .RamVal => w.RamVal k t
  | p => p.cycleValue w t

/-- The value at register `r` and cycle `t`: the four register polynomials read
the register, every cycle polynomial reads cycle `t`, and RAM polynomials are
`0`. -/
def Generated.RelationPoly.registerValue (w : WitnessType F params) (r : Fin 128)
    (t : Fin params.traceLength) : RelationPoly → F
  | .RdWa => w.RdWa r t
  | .RegistersVal => w.RegistersVal r t
  | .Rs1Ra => w.Rs1Ra r t
  | .Rs2Ra => w.Rs2Ra r t
  | p => p.cycleValue w t

/-- The value of a claim expression under a valuation of its polynomials. -/
def ClaimExpr.eval {P : Type} (value : P → F) : ClaimExpr P → F
  | .const c => (c : F)
  | .poly p => value p
  | .add l r => l.eval value + r.eval value
  | .mul l r => l.eval value * r.eval value
  | .sub l r => l.eval value - r.eval value

/-- Whether a claim with this weight evaluates its output at the next cycle. -/
def Generated.RelationWeight.offset : RelationWeight → Bool
  | .RamReadWrite_EqCycle | .RegistersReadWrite_EqCycle | .InstructionInput_EqProduct => false
  | .SpartanShift_EqPlusOneOuter | .SpartanShift_EqPlusOneProduct => true

/-- What a claim says about a witness, read pointwise as described above. The
first conjunct checks that the claim's `offset` agrees with its weight. -/
def RelationClaim.Holds (claim : RelationClaim RelationId RelationPoly RelationWeight)
    (w : WitnessType F params) : Prop :=
  claim.offset = claim.outputWeight.offset ∧
  ∀ t : Fin params.traceLength,
    claim.input.eval (RelationPoly.cycleValue w t) =
      match claim.outputWeight with
      | .RamReadWrite_EqCycle =>
          ∑ k : Fin params.ramSize, claim.output.eval (RelationPoly.ramValue w k t)
      | .RegistersReadWrite_EqCycle =>
          ∑ r : Fin 128, claim.output.eval (RelationPoly.registerValue w r t)
      | .InstructionInput_EqProduct => claim.output.eval (RelationPoly.cycleValue w t)
      | .SpartanShift_EqPlusOneOuter | .SpartanShift_EqPlusOneProduct =>
          if next : t.val + 1 < params.traceLength then
            claim.output.eval (RelationPoly.cycleValue w ⟨t.val + 1, next⟩)
          else 0

/-- A relation holds when each of its claims does. -/
def Relation.Holds (relation : Relation RelationId RelationPoly RelationWeight)
    (w : WitnessType F params) : Prop :=
  ∀ claim ∈ relation.claims, claim.Holds w

end JoltConstraints.ConstraintGen
