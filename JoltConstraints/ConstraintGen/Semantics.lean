import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.metadata
import JoltConstraints.ConstraintGen.Generated.R1CS
import JoltConstraints.ConstraintGen.Generated.Relations
import JoltConstraints.ConstraintGen.Generated.KindTables

set_option autoImplicit false

/-! # What the generated constraint data means (T3)

This file is the handwritten, trusted part of the T3 check. It says which
witness column each name in the generated data stands for, and how a row or a
claim constrains a witness. `ConstraintGen/Equiv.lean` proves that, under this
reading, the unchanged data agree; it marks the known repin mismatches explicitly.

Each map below is an exhaustive `match` on a generated type. A name that Jolt
adds or renames changes the generated type, and this file then fails to
elaborate until someone maps the new name. -/

namespace JoltConstraints.ConstraintGen

open scoped BigOperators
open Generated

variable {F : Type} [Field F] {params : WitnessParams}

/-- Inputs absent from the old witness model, kept explicit during the repin.
`halt` and `haltPanic` are the two new circuit-flag columns; `writeProtected k`
is the verifier's public mask C at remapped RAM word k.
For example, C is one on a code word and zero on a heap word.
These inputs are unconstrained here: no old witness is claimed to determine them.
Jolt at ff6fc6568: `crates/jolt-riscv/src/flags.rs` (`CircuitFlags`) and
`crates/jolt-verifier/src/stages/stage2/ram_read_write_checking.rs`
(`RamReadWriteChecking::public_value`). -/
structure RepinInputs (F : Type) (params : WitnessParams) where
  halt : Fin params.traceLength → F
  haltPanic : Fin params.traceLength → F
  writeProtected : Fin params.ramSize → F

/-! ## R1CS rows -/

/-- The witness value of an R1CS variable at cycle `t`. `One` is the constant
column; `Branch` is the instruction flag of that name, one of Jolt's two
product-factor columns.
Jolt: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`RV64_VARIABLE_NAMES`). -/
def Generated.R1CSVar.value (w : WitnessType F params) (extra : RepinInputs F params) (t : Fin params.traceLength) : R1CSVar → F
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
  | .IsNoop => w.InstructionFlags .IsNoop t
  | .OpFlags_Halt => extra.halt t
  | .OpFlags_HaltPanic => extra.haltPanic t

/-- The value of a linear combination: the sum of coefficient times value.
For example, `[(x, 1), (y, -1)]` has value `1 * x + (-1 * y + 0)`. -/
def lcValue {V : Type} (value : V → F) (lc : List (V × Int)) : F :=
  lc.foldr (fun term acc => (term.2 : F) * value term.1 + acc) 0

/-- A row holds for a witness when `A · B = C` at every padded cycle. -/
def R1CSRow.Holds (row : R1CSRow R1CSVar) (w : WitnessType F params) (extra : RepinInputs F params) : Prop :=
  ∀ t : Fin params.traceLength,
    lcValue (R1CSVar.value w extra t) row.a * lcValue (R1CSVar.value w extra t) row.b =
      lcValue (R1CSVar.value w extra t) row.c

/-! ## Per-kind flags -/

/-- Embed an old lookup table by name, e.g. old `And` becomes generated `And`. -/
def liftLookupTable : LookupTableKind → LookupTable
  | .RangeCheck => .RangeCheck
  | .RangeCheckAligned => .RangeCheckAligned
  | .And => .And
  | .Andn => .Andn
  | .Or => .Or
  | .Xor => .Xor
  | .Equal => .Equal
  | .SignedGreaterThanEqual => .SignedGreaterThanEqual
  | .UnsignedGreaterThanEqual => .UnsignedGreaterThanEqual
  | .NotEqual => .NotEqual
  | .SignedLessThan => .SignedLessThan
  | .UnsignedLessThan => .UnsignedLessThan
  | .SignMask => .SignMask
  | .UpperWord => .UpperWord
  | .UnsignedLessThanEqual => .UnsignedLessThanEqual
  | .ValidUnsignedRemainder => .ValidUnsignedRemainder
  | .ValidDiv0 => .ValidDiv0
  | .LowerHalfWord => .LowerHalfWord
  | .SignExtendWord => .SignExtendWord
  | .Pow2 => .Pow2
  | .Pow2W => .Pow2W
  | .ShiftRightBitmask => .ShiftRightBitmask
  | .VirtualRev8W => .VirtualRev8W
  | .VirtualSRL => .VirtualSRL
  | .VirtualSRA => .VirtualSRA
  | .VirtualROTR => .VirtualROTR
  | .VirtualROTRW => .VirtualROTRW
  | .VirtualNegateIf => .VirtualNegateIf
  | .MulUNoOverflow => .MulUNoOverflow
  | .VirtualXORROT32 => .VirtualXORROT32
  | .VirtualXORROT24 => .VirtualXORROT24
  | .VirtualXORROT16 => .VirtualXORROT16
  | .VirtualXORROT63 => .VirtualXORROT63
  | .VirtualXORROTW16 => .VirtualXORROTW16
  | .VirtualXORROTW12 => .VirtualXORROTW12
  | .VirtualXORROTW8 => .VirtualXORROTW8
  | .VirtualXORROTW7 => .VirtualXORROTW7
  | .WindowMaskW => .WindowMaskW
  | .PextSigned => .PextSigned
  | .VirtualXORROTW22 => .VirtualXORROTW22
  | .VirtualXORROTW19 => .VirtualXORROTW19
  | .VirtualXORROTW6 => .VirtualXORROTW6
  | .ShiftRightBitmaskW => .ShiftRightBitmaskW
  | .VirtualSRLW => .VirtualSRLW
  | .VirtualSRAW => .VirtualSRAW
  | .Pext => .Pext
  | .WindowMaskB => .WindowMaskB
  | .WindowMaskH => .WindowMaskH
  | .ShiftDataB => .ShiftDataB
  | .ShiftDataH => .ShiftDataH
  | .ShiftDataW => .ShiftDataW
  | .VirtualXORROTL1 => .VirtualXORROTL1
  | .AddressOffsetB => .AddressOffsetB
  | .AddressOffsetH => .AddressOffsetH
  | .AddressOffsetW => .AddressOffsetW

/-- Read a generated flag in the old instruction model.
For example, `Load` reads `opcodeFlag`; both halt flags are false because old instructions lack them. -/
def legacyOpcodeFlag (i : JoltISA.Instr) : CircuitFlag → Bool
  | .AddOperands => JoltMetadata.opcodeFlag i .AddOperands
  | .SubtractOperands => JoltMetadata.opcodeFlag i .SubtractOperands
  | .MultiplyOperands => JoltMetadata.opcodeFlag i .MultiplyOperands
  | .Load => JoltMetadata.opcodeFlag i .Load
  | .Store => JoltMetadata.opcodeFlag i .Store
  | .Jump => JoltMetadata.opcodeFlag i .Jump
  | .WriteLookupOutputToRD => JoltMetadata.opcodeFlag i .WriteLookupOutputToRD
  | .VirtualInstruction => JoltMetadata.opcodeFlag i .VirtualInstruction
  | .Assert => JoltMetadata.opcodeFlag i .Assert
  | .DoNotUpdateUnexpandedPC => JoltMetadata.opcodeFlag i .DoNotUpdateUnexpandedPC
  | .Advice => JoltMetadata.opcodeFlag i .Advice
  | .IsCompressed => JoltMetadata.opcodeFlag i .IsCompressed
  | .IsFirstInSequence => JoltMetadata.opcodeFlag i .IsFirstInSequence
  | .IsLastInSequence => JoltMetadata.opcodeFlag i .IsLastInSequence
  | .Halt | .HaltPanic => false

/-- Read a generated flag in an old stamped row, e.g. `IsCompressed` reads the old row flag.
The halt flags are false on every old row. -/
def legacyCircuitFlag (row : JoltInstructionRow) : CircuitFlag → Bool
  | .AddOperands => JoltMetadata.circuitFlag row .AddOperands
  | .SubtractOperands => JoltMetadata.circuitFlag row .SubtractOperands
  | .MultiplyOperands => JoltMetadata.circuitFlag row .MultiplyOperands
  | .Load => JoltMetadata.circuitFlag row .Load
  | .Store => JoltMetadata.circuitFlag row .Store
  | .Jump => JoltMetadata.circuitFlag row .Jump
  | .WriteLookupOutputToRD => JoltMetadata.circuitFlag row .WriteLookupOutputToRD
  | .VirtualInstruction => JoltMetadata.circuitFlag row .VirtualInstruction
  | .Assert => JoltMetadata.circuitFlag row .Assert
  | .DoNotUpdateUnexpandedPC => JoltMetadata.circuitFlag row .DoNotUpdateUnexpandedPC
  | .Advice => JoltMetadata.circuitFlag row .Advice
  | .IsCompressed => JoltMetadata.circuitFlag row .IsCompressed
  | .IsFirstInSequence => JoltMetadata.circuitFlag row .IsFirstInSequence
  | .IsLastInSequence => JoltMetadata.circuitFlag row .IsLastInSequence
  | .Halt | .HaltPanic => false

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
generator checks that every count in `1..=1024` and `65535` adds the same flags
as count `1` (`stamp_uniformity`). -/
def stampClass (row : JoltInstructionRow) : Option Nat × Bool × Bool :=
  (row.virtual_sequence_remaining.map (fun n => if n = 0 then 0 else 1),
    row.is_first_in_sequence, row.is_compressed)

/-- The circuit flags that Jolt adds for a stamp class, from the generated
stamp table. -/
def stampFlags (key : Option Nat × Bool × Bool) : List CircuitFlag :=
  (stampCircuitFlags.lookup key).getD []

/-- The circuit flags of a bytecode row according to the generated tables:
the flags of its kind at the canonical stamp, plus the flags its stamp adds. -/
def generatedCircuitFlags (row : JoltInstructionRow) : List CircuitFlag :=
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

This reading is valid only for a claim whose input relation, offset and
polynomials fit its weight, and for a relation whose weights all belong to it.
`RelationClaim.WellFormed` and `Relation.Holds` check those conditions, so a
generated claim that pairs a weight with the wrong relation, offset or
polynomial fails the proofs in `Equiv.lean`.

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
  | .OpFlags_Load => w.OpFlags .Load t
  | .OpFlags_Store => w.OpFlags .Store t
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

/-- Which witness space a relation polynomial lives in. -/
inductive PolyDomain where
  | cycle
  | ram
  | registers
  deriving DecidableEq, Repr

/-- The witness space of each relation polynomial. -/
def Generated.RelationPoly.domain : RelationPoly → PolyDomain
  | .Imm => .cycle
  | .InstructionFlags_IsNoop => .cycle
  | .InstructionFlags_LeftOperandIsPC => .cycle
  | .InstructionFlags_LeftOperandIsRs1Value => .cycle
  | .InstructionFlags_RightOperandIsImm => .cycle
  | .InstructionFlags_RightOperandIsRdWriteValue => .cycle
  | .InstructionFlags_RightOperandIsRs2Value => .cycle
  | .LeftInstructionInput => .cycle
  | .NextIsFirstInSequence => .cycle
  | .NextIsNoop => .cycle
  | .NextIsVirtual => .cycle
  | .NextPC => .cycle
  | .NextUnexpandedPC => .cycle
  | .OpFlags_Load | .OpFlags_Store => .cycle
  | .OpFlags_IsFirstInSequence => .cycle
  | .OpFlags_VirtualInstruction => .cycle
  | .PC => .cycle
  | .RamInc => .cycle
  | .RamRa => .ram
  | .RamReadValue => .cycle
  | .RamVal => .ram
  | .RamWriteValue => .cycle
  | .RdInc => .cycle
  | .RdWa => .registers
  | .RdWriteValue => .cycle
  | .RegistersVal => .registers
  | .RightInstructionInput => .cycle
  | .Rs1Ra => .registers
  | .Rs1Value => .cycle
  | .Rs2Ra => .registers
  | .Rs2Value => .cycle
  | .UnexpandedPC => .cycle

/-- The address space an output weight sums over (`cycle` when it sums over
none). -/
def Generated.RelationWeight.outputDomain : RelationWeight → PolyDomain
  | .RamReadWrite_EqCycle | .RamReadWrite_WriteProtectedEqCycle => .ram
  | .RegistersReadWrite_EqCycle => .registers
  | .InstructionInput_EqProduct | .SpartanShift_EqPlusOneOuter
  | .SpartanShift_EqPlusOneProduct => .cycle

/-- The relation whose sumcheck uses this weight. -/
def Generated.RelationWeight.outputRelation : RelationWeight → RelationId
  | .RamReadWrite_EqCycle | .RamReadWrite_WriteProtectedEqCycle => .RamReadWriteChecking
  | .RegistersReadWrite_EqCycle => .RegistersReadWriteChecking
  | .InstructionInput_EqProduct => .InstructionInputVirtualization
  | .SpartanShift_EqPlusOneOuter | .SpartanShift_EqPlusOneProduct => .SpartanShift

/-- The relation whose opening point this weight is built from, and so the
input relation of every claim that uses it. The two shift weights use
different opening points (Jolt:
`crates/jolt-verifier/src/stages/stage3/spartan_shift.rs:102-110`), so the
pointwise reading below is valid only when each is paired with its own input
relation. -/
def Generated.RelationWeight.inputRelation : RelationWeight → RelationId
  | .RamReadWrite_EqCycle | .RamReadWrite_WriteProtectedEqCycle => .SpartanOuter
  | .RegistersReadWrite_EqCycle => .RegistersClaimReduction
  | .InstructionInput_EqProduct => .SpartanProductVirtualization
  | .SpartanShift_EqPlusOneOuter => .SpartanOuter
  | .SpartanShift_EqPlusOneProduct => .SpartanProductVirtualization

/-- The polynomials a claim expression mentions. -/
def ClaimExpr.polys {P : Type} : ClaimExpr P → List P
  | .const _ => []
  | .poly p => [p]
  | .add l r | .mul l r | .sub l r => l.polys ++ r.polys

/-- The value of a claim expression under a valuation of its polynomials. -/
def ClaimExpr.eval {P : Type} (value : P → F) : ClaimExpr P → F
  | .const c => (c : F)
  | .poly p => value p
  | .add l r => l.eval value + r.eval value
  | .mul l r => l.eval value * r.eval value
  | .sub l r => l.eval value - r.eval value

/-- Whether a claim with this weight evaluates its output at the next cycle. -/
def Generated.RelationWeight.offset : RelationWeight → Bool
  | .RamReadWrite_EqCycle | .RamReadWrite_WriteProtectedEqCycle | .RegistersReadWrite_EqCycle | .InstructionInput_EqProduct => false
  | .SpartanShift_EqPlusOneOuter | .SpartanShift_EqPlusOneProduct => true

/-- The conditions under which `Holds` may read a claim pointwise: the claim's
input relation and offset are the ones its weight belongs with, its input
mentions only cycle polynomials, and its output mentions only cycle
polynomials and polynomials over the weight's address space. -/
def RelationClaim.WellFormed (claim : RelationClaim RelationId RelationPoly RelationWeight) :
    Bool :=
  claim.inputRelation == claim.outputWeight.inputRelation &&
    claim.offset == claim.outputWeight.offset &&
    claim.input.polys.all (·.domain == .cycle) &&
    claim.output.polys.all fun p =>
      p.domain == .cycle || p.domain == claim.outputWeight.outputDomain

/-- What a claim says about a witness, read pointwise as described above. The
first conjunct requires the claim to be well formed. -/
def RelationClaim.Holds (claim : RelationClaim RelationId RelationPoly RelationWeight)
    (w : WitnessType F params) (extra : RepinInputs F params) : Prop :=
  claim.WellFormed = true ∧
  ∀ t : Fin params.traceLength,
    claim.input.eval (RelationPoly.cycleValue w t) =
      match claim.outputWeight with
      | .RamReadWrite_EqCycle =>
          ∑ k : Fin params.ramSize, claim.output.eval (RelationPoly.ramValue w k t)
      | .RamReadWrite_WriteProtectedEqCycle =>
          ∑ k : Fin params.ramSize, extra.writeProtected k *
            claim.output.eval (RelationPoly.ramValue w k t)
      | .RegistersReadWrite_EqCycle =>
          ∑ r : Fin 128, claim.output.eval (RelationPoly.registerValue w r t)
      | .InstructionInput_EqProduct => claim.output.eval (RelationPoly.cycleValue w t)
      | .SpartanShift_EqPlusOneOuter | .SpartanShift_EqPlusOneProduct =>
          if next : t.val + 1 < params.traceLength then
            claim.output.eval (RelationPoly.cycleValue w ⟨t.val + 1, next⟩)
          else 0

/-- A relation holds when every claim's weight belongs to it and each claim
holds. -/
def Relation.Holds (relation : Relation RelationId RelationPoly RelationWeight)
    (w : WitnessType F params) (extra : RepinInputs F params) : Prop :=
  relation.claims.all (·.outputWeight.outputRelation == relation.outputRelation) = true ∧
    ∀ claim ∈ relation.claims, claim.Holds w extra

end JoltConstraints.ConstraintGen
