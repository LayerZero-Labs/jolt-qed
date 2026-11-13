import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import JoltConstraints.Constraints.All
import JoltConstraints.ConstraintGen.Semantics

set_option autoImplicit false

/-! # The handwritten constraints equal the generated ones (T3)

Each theorem here says that a handwritten definition in `JoltConstraints/` and
the data that `constraint-gen` extracted from Jolt describe the same thing,
under the reading in `ConstraintGen/Semantics.lean`.

* `rv64RowNN_holds_iff`: R1CS row `NN` of `rv64_trace_constraints` holds iff the
  matching handwritten constraint holds. `rv64Rows_holds_iff` collects all 22.
* `*_holds_iff` for the four relations: each zklean-extractor relation holds
  iff its handwritten claims hold.
* `kindCircuitFlags_kindOf`, `kindInstructionFlags_kindOf`,
  `kindLookupTable_kindOf`, `kindRafFlag_kindOf`: Lean's per-instruction
  metadata equals Jolt's per-kind table at every instruction.
* `circuitFlag_iff_generated`: a bytecode row's circuit flag, including the
  flags its sequence stamp sets, matches the generated tables.
* `padding_*`: the padding row of `bytecodeCircuitFlag` and its neighbors
  matches Jolt's `NoOp` kind.
* `ConstraintEquations.generated`: the handwritten `ConstraintEquations`
  imply every generated row and relation. -/

namespace JoltConstraints.ConstraintGen

open scoped BigOperators
open Generated

variable {F : Type} [Field F] {params : WitnessParams}

/-! ## R1CS rows -/

/-- Prove `row.Holds w ↔ def w` for an R1CS row whose two sides are the same
polynomial identity up to ring arithmetic. -/
macro "row_equiv" row:ident def_:ident : tactic =>
  `(tactic| (
    unfold R1CSRow.Holds $def_:ident
    refine forall_congr' fun t => ?_
    simp only [$row:ident, lcValue, List.foldr, R1CSVar.value]
    push_cast
    constructor <;> intro h <;> first | linear_combination h | linear_combination -h))

theorem rv64Row00_holds_iff (w : WitnessType F params) :
    rv64Row00.Holds w ↔ ramAddrEqRs1PlusImmMinusLookupIfLoadStore w := by
  row_equiv rv64Row00 ramAddrEqRs1PlusImmMinusLookupIfLoadStore

theorem rv64Row01_holds_iff (w : WitnessType F params) :
    rv64Row01.Holds w ↔ ramAddrEqZeroIfNotLoadStore w := by
  row_equiv rv64Row01 ramAddrEqZeroIfNotLoadStore

theorem rv64Row02_holds_iff (w : WitnessType F params) :
    rv64Row02.Holds w ↔ ramReadEqRamWriteIfLoad w := by
  row_equiv rv64Row02 ramReadEqRamWriteIfLoad

theorem rv64Row03_holds_iff (w : WitnessType F params) :
    rv64Row03.Holds w ↔ ramReadEqRdWriteIfLoad w := by
  row_equiv rv64Row03 ramReadEqRdWriteIfLoad

theorem rv64Row04_holds_iff (w : WitnessType F params) :
    rv64Row04.Holds w ↔ rs2EqRamWriteIfStore w := by
  row_equiv rv64Row04 rs2EqRamWriteIfStore

theorem rv64Row05_holds_iff (w : WitnessType F params) :
    rv64Row05.Holds w ↔ leftLookupZeroIfAddSubMul w := by
  row_equiv rv64Row05 leftLookupZeroIfAddSubMul

theorem rv64Row06_holds_iff (w : WitnessType F params) :
    rv64Row06.Holds w ↔ leftLookupEqLeftInputOtherwise w := by
  row_equiv rv64Row06 leftLookupEqLeftInputOtherwise

theorem rv64Row07_holds_iff (w : WitnessType F params) :
    rv64Row07.Holds w ↔ rightLookupAdd w := by
  row_equiv rv64Row07 rightLookupAdd

theorem rv64Row08_holds_iff (w : WitnessType F params) :
    rv64Row08.Holds w ↔ rightLookupSub w := by
  row_equiv rv64Row08 rightLookupSub

theorem rv64Row09_holds_iff (w : WitnessType F params) :
    rv64Row09.Holds w ↔ rightLookupEqProductIfMul w := by
  row_equiv rv64Row09 rightLookupEqProductIfMul

theorem rv64Row10_holds_iff (w : WitnessType F params) :
    rv64Row10.Holds w ↔ rightLookupEqRightInputOtherwise w := by
  row_equiv rv64Row10 rightLookupEqRightInputOtherwise

theorem rv64Row11_holds_iff (w : WitnessType F params) :
    rv64Row11.Holds w ↔ assertLookupOne w := by
  row_equiv rv64Row11 assertLookupOne

theorem rv64Row12_holds_iff (w : WitnessType F params) :
    rv64Row12.Holds w ↔ rdWriteEqLookupIfWriteLookupToRd w := by
  row_equiv rv64Row12 rdWriteEqLookupIfWriteLookupToRd

theorem rv64Row13_holds_iff (w : WitnessType F params) :
    rv64Row13.Holds w ↔ rdWriteEqPCPlusConstIfJump w := by
  row_equiv rv64Row13 rdWriteEqPCPlusConstIfJump

theorem rv64Row14_holds_iff (w : WitnessType F params) :
    rv64Row14.Holds w ↔ nextUnexpandedPCEqLookupIfShouldJump w := by
  row_equiv rv64Row14 nextUnexpandedPCEqLookupIfShouldJump

theorem rv64Row15_holds_iff (w : WitnessType F params) :
    rv64Row15.Holds w ↔ nextUnexpandedPCEqPCPlusImmIfShouldBranch w := by
  row_equiv rv64Row15 nextUnexpandedPCEqPCPlusImmIfShouldBranch

theorem rv64Row16_holds_iff (w : WitnessType F params) :
    rv64Row16.Holds w ↔ nextUnexpandedPCUpdateOtherwise w := by
  row_equiv rv64Row16 nextUnexpandedPCUpdateOtherwise

theorem rv64Row17_holds_iff (w : WitnessType F params) :
    rv64Row17.Holds w ↔ nextPCEqPCPlusOneIfInline w := by
  row_equiv rv64Row17 nextPCEqPCPlusOneIfInline

theorem rv64Row18_holds_iff (w : WitnessType F params) :
    rv64Row18.Holds w ↔ mustStartSequenceFromBeginning w := by
  row_equiv rv64Row18 mustStartSequenceFromBeginning

theorem rv64Row19_holds_iff (w : WitnessType F params) :
    rv64Row19.Holds w ↔ productEqLeftInputMulRightInput w := by
  row_equiv rv64Row19 productEqLeftInputMulRightInput

theorem rv64Row20_holds_iff (w : WitnessType F params) :
    rv64Row20.Holds w ↔ shouldBranchEqLookupOutputMulBranch w := by
  row_equiv rv64Row20 shouldBranchEqLookupOutputMulBranch

theorem rv64Row21_holds_iff (w : WitnessType F params) :
    rv64Row21.Holds w ↔ shouldJumpEqJumpMulNotNextIsNoop w := by
  row_equiv rv64Row21 shouldJumpEqJumpMulNotNextIsNoop

/-- All 22 rows hold iff the 22 handwritten R1CS constraints hold. -/
theorem rv64Rows_holds_iff (w : WitnessType F params) :
    (∀ row ∈ rv64Rows, row.Holds w) ↔
      ramAddrEqRs1PlusImmMinusLookupIfLoadStore w ∧
      ramAddrEqZeroIfNotLoadStore w ∧
      ramReadEqRamWriteIfLoad w ∧
      ramReadEqRdWriteIfLoad w ∧
      rs2EqRamWriteIfStore w ∧
      leftLookupZeroIfAddSubMul w ∧
      leftLookupEqLeftInputOtherwise w ∧
      rightLookupAdd w ∧
      rightLookupSub w ∧
      rightLookupEqProductIfMul w ∧
      rightLookupEqRightInputOtherwise w ∧
      assertLookupOne w ∧
      rdWriteEqLookupIfWriteLookupToRd w ∧
      rdWriteEqPCPlusConstIfJump w ∧
      nextUnexpandedPCEqLookupIfShouldJump w ∧
      nextUnexpandedPCEqPCPlusImmIfShouldBranch w ∧
      nextUnexpandedPCUpdateOtherwise w ∧
      nextPCEqPCPlusOneIfInline w ∧
      mustStartSequenceFromBeginning w ∧
      productEqLeftInputMulRightInput w ∧
      shouldBranchEqLookupOutputMulBranch w ∧
      shouldJumpEqJumpMulNotNextIsNoop w := by
  simp only [rv64Rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    rv64Row00_holds_iff w, rv64Row01_holds_iff w, rv64Row02_holds_iff w, rv64Row03_holds_iff w, rv64Row04_holds_iff w, rv64Row05_holds_iff w, rv64Row06_holds_iff w, rv64Row07_holds_iff w, rv64Row08_holds_iff w, rv64Row09_holds_iff w, rv64Row10_holds_iff w, rv64Row11_holds_iff w, rv64Row12_holds_iff w, rv64Row13_holds_iff w, rv64Row14_holds_iff w, rv64Row15_holds_iff w, rv64Row16_holds_iff w, rv64Row17_holds_iff w, rv64Row18_holds_iff w, rv64Row19_holds_iff w, rv64Row20_holds_iff w, rv64Row21_holds_iff w]

/-! ## The four relations -/

/-- Close `claim.Holds w ↔ def w` when the claim's pointwise identity is the
handwritten definition up to unfolding. -/
macro "claim_rfl" : tactic => `(tactic| exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)

theorem ramReadWriteChecking_holds_iff (w : WitnessType F params) :
    ramReadWriteChecking.Holds w ↔
      ramReadValueEqRamRead w ∧ ramWriteValueEqRamReadWrite w := by
  simp only [Relation.Holds, ramReadWriteChecking, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  refine and_congr ?_ ?_ <;> claim_rfl

theorem registersReadWriteChecking_holds_iff (w : WitnessType F params) :
    registersReadWriteChecking.Holds w ↔
      rdWriteValueEqRegistersReadWrite w ∧ rs1ValueEqRegistersRead w ∧
        rs2ValueEqRegistersRead w := by
  simp only [Relation.Holds, registersReadWriteChecking, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  refine and_congr ?_ (and_congr ?_ ?_) <;> claim_rfl

/-- Jolt lists the right input's claim first. -/
theorem instructionInputVirtualization_holds_iff (w : WitnessType F params) :
    instructionInputVirtualization.Holds w ↔
      rightInstructionInputEqSelection w ∧ leftInstructionInputEqSelection w := by
  simp only [Relation.Holds, instructionInputVirtualization, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  refine and_congr ?_ ?_ <;> claim_rfl

/-- Jolt states the last claim as `1 - NextIsNoop = shift(1 - IsNoop)`. At the
last cycle the shift is zero, so `NextIsNoop` is one there, which is the
handwritten `else 1`. -/
theorem spartanShift_holds_iff (w : WitnessType F params) :
    spartanShift.Holds w ↔
      nextUnexpandedPCEqShift w ∧ nextPCEqShift w ∧ nextIsVirtualEqShift w ∧
        nextIsFirstInSequenceEqShift w ∧ nextIsNoopEqShift w := by
  simp only [Relation.Holds, spartanShift, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))) <;> try claim_rfl
  unfold RelationClaim.Holds nextIsNoopEqShift
  simp only [ClaimExpr.eval, RelationPoly.cycleValue, RelationWeight.offset, Int.cast_one,
    true_and]
  refine forall_congr' fun t => ?_
  split_ifs <;> constructor <;> intro h <;> linear_combination -h

/-! ## Per-kind flags, lookup table and RAF flag -/

theorem mem_circuitFlagOrder (f : CircuitFlags) : f ∈ circuitFlagOrder := by
  cases f <;> decide

theorem mem_instructionFlagOrder (f : InstructionFlags) : f ∈ instructionFlagOrder := by
  cases f <;> decide

/-- Jolt's canonical-stamp circuit flags of an instruction's kind are the
flags `opcodeFlag` sets, in Jolt's order. -/
theorem kindCircuitFlags_kindOf (i : JoltISA.Instr) :
    kindCircuitFlags (kindOf i) = circuitFlagOrder.filter (JoltMetadata.opcodeFlag i ·) := by
  cases i <;> rfl

theorem kindInstructionFlags_kindOf (i : JoltISA.Instr) :
    kindInstructionFlags (kindOf i) =
      instructionFlagOrder.filter (JoltMetadata.instructionFlag i ·) := by
  cases i <;> rfl

theorem kindLookupTable_kindOf (i : JoltISA.Instr) :
    kindLookupTable (kindOf i) = JoltMetadata.lookupTable i := by
  cases i <;> rfl

theorem kindRafFlag_kindOf (i : JoltISA.Instr) :
    kindRafFlag (kindOf i) = JoltMetadata.instructionRafFlag i := by
  cases i <;> rfl

theorem mem_kindCircuitFlags_kindOf (i : JoltISA.Instr) (f : CircuitFlags) :
    f ∈ kindCircuitFlags (kindOf i) ↔ JoltMetadata.opcodeFlag i f = true := by
  simp [kindCircuitFlags_kindOf, List.mem_filter, mem_circuitFlagOrder]

theorem mem_kindInstructionFlags_kindOf (i : JoltISA.Instr) (f : InstructionFlags) :
    f ∈ kindInstructionFlags (kindOf i) ↔ JoltMetadata.instructionFlag i f = true := by
  simp [kindInstructionFlags_kindOf, List.mem_filter, mem_instructionFlagOrder]

/-! ## Flags set by the sequence stamp -/

/-- `stampFlags` of a row's stamp class, case by case. -/
theorem mem_stampFlags_stampClass (row : JoltInstructionRow) (f : CircuitFlags) :
    f ∈ stampFlags (stampClass row) ↔
      (f = .VirtualInstruction ∧ row.virtual_sequence_remaining.isSome) ∨
      (f = .IsLastInSequence ∧ row.virtual_sequence_remaining = some 0) ∨
      (f = .DoNotUpdateUnexpandedPC ∧ row.virtual_sequence_remaining.getD 0 ≠ 0) ∨
      (f = .IsCompressed ∧ row.is_compressed) ∨
      (f = .IsFirstInSequence ∧ row.is_first_in_sequence) := by
  rcases row with ⟨instruction, address, _ | n, first, compressed⟩
  · dsimp only [stampClass]
    cases first <;> cases compressed <;> cases f <;> decide
  · by_cases hn : n = 0
    · subst hn
      dsimp only [stampClass]
      cases first <;> cases compressed <;> cases f <;> decide
    · have hs : stampClass ⟨instruction, address, some n, first, compressed⟩ =
          (some 1, first, compressed) := by
        simp [stampClass]; exact hn
      have hlast : (some n = some (0 : BitVec 16)) ↔ False := by simp; exact hn
      have hdo : (some n).getD 0 ≠ 0 ↔ True := by simp; exact hn
      rw [hs]
      dsimp only
      simp only [hlast, hdo, Option.isSome_some]
      cases first <;> cases compressed <;> cases f <;> decide

/-- A bytecode row's circuit flag, as `JoltMetadata.circuitFlag` computes it,
is set iff the generated tables list it for the row's kind and stamp class. -/
theorem circuitFlag_iff_generated (row : JoltInstructionRow) (f : CircuitFlags) :
    JoltMetadata.circuitFlag row f = true ↔ f ∈ generatedCircuitFlags row := by
  rw [generatedCircuitFlags, List.mem_append, mem_kindCircuitFlags_kindOf,
    mem_stampFlags_stampClass]
  rcases row with ⟨instruction, address, vsr, first, compressed⟩
  cases f <;> simp [JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag]

/-! ## Padding rows are Jolt's `NoOp` -/

/-- A padding bytecode address sets the circuit flags of Jolt's `NoOp`. -/
theorem padding_circuitFlag (f : CircuitFlags) :
    (f = .DoNotUpdateUnexpandedPC) ↔ f ∈ kindCircuitFlags .NoOp := by
  cases f <;> decide

/-- A padding bytecode address sets the instruction flags of Jolt's `NoOp`. -/
theorem padding_instructionFlag (f : InstructionFlags) :
    (f = .IsNoop) ↔ f ∈ kindInstructionFlags .NoOp := by
  cases f <;> decide

/-- Jolt's `NoOp` selects no lookup table and has no RAF flag, as a padding
address does in `bytecodeLookupTableFlag` and `bytecodeRafFlag`. -/
theorem padding_lookupTable_rafFlag :
    kindLookupTable .NoOp = none ∧ kindRafFlag .NoOp = false := ⟨rfl, rfl⟩

/-! ## Link to `ConstraintEquations` -/

/-- A witness that satisfies the handwritten `ConstraintEquations` satisfies
all 22 generated R1CS rows and the four generated relations. The converse
holds for these 34 conjuncts by the `_holds_iff` theorems above;
`ConstraintEquations` has further conjuncts that T3 does not generate. -/
theorem ConstraintEquations.generated {bytecode : Array JoltInstructionRow}
    {initialRam : Nat → BitVec 64} {io : JoltDevice} {entry : Fin (2 ^ params.logBytecodeK)}
    {w : WitnessType F params} (h : ConstraintEquations bytecode initialRam io entry w) :
    (∀ row ∈ rv64Rows, row.Holds w) ∧ ramReadWriteChecking.Holds w ∧
      registersReadWriteChecking.Holds w ∧ instructionInputVirtualization.Holds w ∧
      spartanShift.Holds w :=
  ⟨(rv64Rows_holds_iff w).2 ⟨h.ramAddrEqRs1PlusImmMinusLookupIfLoadStore, h.ramAddrEqZeroIfNotLoadStore, h.ramReadEqRamWriteIfLoad, h.ramReadEqRdWriteIfLoad, h.rs2EqRamWriteIfStore, h.leftLookupZeroIfAddSubMul, h.leftLookupEqLeftInputOtherwise, h.rightLookupAdd, h.rightLookupSub, h.rightLookupEqProductIfMul, h.rightLookupEqRightInputOtherwise, h.assertLookupOne, h.rdWriteEqLookupIfWriteLookupToRd, h.rdWriteEqPCPlusConstIfJump, h.nextUnexpandedPCEqLookupIfShouldJump, h.nextUnexpandedPCEqPCPlusImmIfShouldBranch, h.nextUnexpandedPCUpdateOtherwise, h.nextPCEqPCPlusOneIfInline, h.mustStartSequenceFromBeginning, h.productEqLeftInputMulRightInput, h.shouldBranchEqLookupOutputMulBranch, h.shouldJumpEqJumpMulNotNextIsNoop⟩,
    (ramReadWriteChecking_holds_iff w).2 ⟨h.ramReadValueEqRamRead, h.ramWriteValueEqRamReadWrite⟩,
    (registersReadWriteChecking_holds_iff w).2
      ⟨h.rdWriteValueEqRegistersReadWrite, h.rs1ValueEqRegistersRead, h.rs2ValueEqRegistersRead⟩,
    (instructionInputVirtualization_holds_iff w).2
      ⟨h.rightInstructionInputEqSelection, h.leftInstructionInputEqSelection⟩,
    (spartanShift_holds_iff w).2
      ⟨h.nextUnexpandedPCEqShift, h.nextPCEqShift, h.nextIsVirtualEqShift,
        h.nextIsFirstInSequenceEqShift, h.nextIsNoopEqShift⟩⟩

end JoltConstraints.ConstraintGen
