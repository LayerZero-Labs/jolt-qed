import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import JoltConstraints.translation.Constraints.All
import JoltConstraints.ConstraintGen.Semantics

set_option autoImplicit false

/-! # Comparisons with generated Jolt-main constraints (T3)

The comparisons use the regenerated data at ff6fc6568 and the reading in
`ConstraintGen/Semantics.lean`.
Rows 14 and 21, the enlarged RAM relation, and total kind coverage are marked
mismatch admissions.
All other proofs below are kernel checked independently of those admissions,
except the aggregate row and `ConstraintEquations.generated` assembly theorems
that explicitly use them.
Neither aggregate certifies the old model against Jolt main.

* `rv64RowNN_holds_iff`: R1CS row `NN` of `rv64_trace_constraints` holds iff the
  matching handwritten constraint holds. `rv64Rows_holds_iff` collects all 22.
* `*_holds_iff` for the four relations: each zklean-extractor relation holds
  iff its handwritten claims hold.
* `kindCircuitFlags_kindOf`, `kindInstructionFlags_kindOf`,
  `kindLookupTable_kindOf`, `kindRafFlag_kindOf`: Lean's per-instruction
  metadata equals Jolt's per-kind table at every instruction.
* A `run_meta` check: `kindOf` maps every Lean instruction to the Jolt kind of
  the same name, and every Jolt kind except `NoOp` has a Lean instruction.
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
variable (extra : RepinInputs F params) (claimedPanic : Bool)

/-! ## R1CS rows -/

/-- Prove `row.Holds w extra ↔ def w` for an R1CS row whose two sides are the same
polynomial identity up to ring arithmetic. -/
macro "row_equiv" row:ident def_:ident : tactic =>
  `(tactic| (
    unfold R1CSRow.Holds $def_:ident
    refine forall_congr' fun t => ?_
    simp only [$row:ident, lcValue, List.foldr, R1CSVar.value]
    push_cast
    constructor <;> intro h <;> first | linear_combination h | linear_combination -h))

/-- Compare generated row 00 with `ramAddrEqRs1PlusImmMinusLookupIfLoadStore` at every padded cycle.
For example, its generated identity is `(OpFlags_Load + OpFlags_Store) * (RamAddress + -Rs1Value + -Imm + LookupOutput) = 0`. -/
theorem rv64Row00_holds_iff (w : WitnessType F params) :
    rv64Row00.Holds w extra ↔ ramAddrEqRs1PlusImmMinusLookupIfLoadStore w := by
  row_equiv rv64Row00 ramAddrEqRs1PlusImmMinusLookupIfLoadStore

/-- Compare generated row 01 with `ramAddrEqZeroIfNotLoadStore` at every padded cycle.
For example, its generated identity is `(One + -OpFlags_Load + -OpFlags_Store) * (RamAddress) = 0`. -/
theorem rv64Row01_holds_iff (w : WitnessType F params) :
    rv64Row01.Holds w extra ↔ ramAddrEqZeroIfNotLoadStore w := by
  row_equiv rv64Row01 ramAddrEqZeroIfNotLoadStore

/-- Compare generated row 02 with `ramReadEqRamWriteIfLoad` at every padded cycle.
For example, its generated identity is `(OpFlags_Load) * (RamReadValue + -RamWriteValue) = 0`. -/
theorem rv64Row02_holds_iff (w : WitnessType F params) :
    rv64Row02.Holds w extra ↔ ramReadEqRamWriteIfLoad w := by
  row_equiv rv64Row02 ramReadEqRamWriteIfLoad

/-- Compare generated row 03 with `ramReadEqRdWriteIfLoad` at every padded cycle.
For example, its generated identity is `(OpFlags_Load) * (RamReadValue + -RdWriteValue) = 0`. -/
theorem rv64Row03_holds_iff (w : WitnessType F params) :
    rv64Row03.Holds w extra ↔ ramReadEqRdWriteIfLoad w := by
  row_equiv rv64Row03 ramReadEqRdWriteIfLoad

/-- Compare generated row 04 with `rs2EqRamWriteIfStore` at every padded cycle.
For example, its generated identity is `(OpFlags_Store) * (Rs2Value + -RamWriteValue) = 0`. -/
theorem rv64Row04_holds_iff (w : WitnessType F params) :
    rv64Row04.Holds w extra ↔ rs2EqRamWriteIfStore w := by
  row_equiv rv64Row04 rs2EqRamWriteIfStore

/-- Compare generated row 05 with `leftLookupZeroIfAddSubMul` at every padded cycle.
For example, its generated identity is `(OpFlags_AddOperands + OpFlags_SubtractOperands + OpFlags_MultiplyOperands) * (LeftLookupOperand) = 0`. -/
theorem rv64Row05_holds_iff (w : WitnessType F params) :
    rv64Row05.Holds w extra ↔ leftLookupZeroIfAddSubMul w := by
  row_equiv rv64Row05 leftLookupZeroIfAddSubMul

/-- Compare generated row 06 with `leftLookupEqLeftInputOtherwise` at every padded cycle.
For example, its generated identity is `(One + -OpFlags_AddOperands + -OpFlags_SubtractOperands + -OpFlags_MultiplyOperands) * (LeftLookupOperand + -LeftInstructionInput) = 0`. -/
theorem rv64Row06_holds_iff (w : WitnessType F params) :
    rv64Row06.Holds w extra ↔ leftLookupEqLeftInputOtherwise w := by
  row_equiv rv64Row06 leftLookupEqLeftInputOtherwise

/-- Compare generated row 07 with `rightLookupAdd` at every padded cycle.
For example, its generated identity is `(OpFlags_AddOperands) * (RightLookupOperand + -LeftInstructionInput + -RightInstructionInput) = 0`. -/
theorem rv64Row07_holds_iff (w : WitnessType F params) :
    rv64Row07.Holds w extra ↔ rightLookupAdd w := by
  row_equiv rv64Row07 rightLookupAdd

/-- Compare generated row 08 with `rightLookupSub` at every padded cycle.
For example, its generated identity is `(OpFlags_SubtractOperands) * (RightLookupOperand + -LeftInstructionInput + RightInstructionInput + -18446744073709551616*One) = 0`. -/
theorem rv64Row08_holds_iff (w : WitnessType F params) :
    rv64Row08.Holds w extra ↔ rightLookupSub w := by
  row_equiv rv64Row08 rightLookupSub

/-- Compare generated row 09 with `rightLookupEqProductIfMul` at every padded cycle.
For example, its generated identity is `(OpFlags_MultiplyOperands) * (RightLookupOperand + -Product) = 0`. -/
theorem rv64Row09_holds_iff (w : WitnessType F params) :
    rv64Row09.Holds w extra ↔ rightLookupEqProductIfMul w := by
  row_equiv rv64Row09 rightLookupEqProductIfMul

/-- Compare generated row 10 with `rightLookupEqRightInputOtherwise` at every padded cycle.
For example, its generated identity is `(One + -OpFlags_AddOperands + -OpFlags_SubtractOperands + -OpFlags_MultiplyOperands + -OpFlags_Advice) * (RightLookupOperand + -RightInstructionInput) = 0`. -/
theorem rv64Row10_holds_iff (w : WitnessType F params) :
    rv64Row10.Holds w extra ↔ rightLookupEqRightInputOtherwise w := by
  row_equiv rv64Row10 rightLookupEqRightInputOtherwise

/-- Compare generated row 11 with `assertLookupOne` at every padded cycle.
For example, its generated identity is `(OpFlags_Assert) * (LookupOutput + -One) = 0`. -/
theorem rv64Row11_holds_iff (w : WitnessType F params) :
    rv64Row11.Holds w extra ↔ assertLookupOne w := by
  row_equiv rv64Row11 assertLookupOne

/-- Compare generated row 12 with `rdWriteEqLookupIfWriteLookupToRd` at every padded cycle.
For example, its generated identity is `(OpFlags_WriteLookupOutputToRD) * (RdWriteValue + -LookupOutput) = 0`. -/
theorem rv64Row12_holds_iff (w : WitnessType F params) :
    rv64Row12.Holds w extra ↔ rdWriteEqLookupIfWriteLookupToRd w := by
  row_equiv rv64Row12 rdWriteEqLookupIfWriteLookupToRd

/-- Compare generated row 13 with `rdWriteEqPCPlusConstIfJump` at every padded cycle.
For example, its generated identity is `(OpFlags_Jump) * (RdWriteValue + -UnexpandedPC + -4*One + 2*OpFlags_IsCompressed) = 0`. -/
theorem rv64Row13_holds_iff (w : WitnessType F params) :
    rv64Row13.Holds w extra ↔ rdWriteEqPCPlusConstIfJump w := by
  row_equiv rv64Row13 rdWriteEqPCPlusConstIfJump

/-- Compare generated row 14 with `nextUnexpandedPCEqLookupIfShouldJump` at every padded cycle.
For example, its generated identity is `(OpFlags_Jump) * (NextUnexpandedPC + -LookupOutput) = 0`. This comparison is an admitted mismatch. -/
theorem rv64Row14_holds_iff (w : WitnessType F params) :
    rv64Row14.Holds w extra ↔ nextUnexpandedPCEqLookupIfShouldJump w := by
  sorry -- mismatch: generated row 14 uses Jump rather than ShouldJump after Jolt #2451.

/-- Compare generated row 15 with `nextUnexpandedPCEqPCPlusImmIfShouldBranch` at every padded cycle.
For example, its generated identity is `(ShouldBranch) * (NextUnexpandedPC + -UnexpandedPC + -Imm) = 0`. -/
theorem rv64Row15_holds_iff (w : WitnessType F params) :
    rv64Row15.Holds w extra ↔ nextUnexpandedPCEqPCPlusImmIfShouldBranch w := by
  row_equiv rv64Row15 nextUnexpandedPCEqPCPlusImmIfShouldBranch

/-- Compare generated row 16 with `nextUnexpandedPCUpdateOtherwise` at every padded cycle.
For example, its generated identity is `(One + -ShouldBranch + -OpFlags_Jump) * (NextUnexpandedPC + -UnexpandedPC + -4*One + 4*OpFlags_DoNotUpdateUnexpandedPC + 2*OpFlags_IsCompressed) = 0`. -/
theorem rv64Row16_holds_iff (w : WitnessType F params) :
    rv64Row16.Holds w extra ↔ nextUnexpandedPCUpdateOtherwise w := by
  row_equiv rv64Row16 nextUnexpandedPCUpdateOtherwise

/-- Compare generated row 17 with `nextPCEqPCPlusOneIfInline` at every padded cycle.
For example, its generated identity is `(OpFlags_VirtualInstruction + -OpFlags_IsLastInSequence) * (NextPC + -PC + -One) = 0`. -/
theorem rv64Row17_holds_iff (w : WitnessType F params) :
    rv64Row17.Holds w extra ↔ nextPCEqPCPlusOneIfInline w := by
  row_equiv rv64Row17 nextPCEqPCPlusOneIfInline

/-- Compare generated row 18 with `mustStartSequenceFromBeginning` at every padded cycle.
For example, its generated identity is `(NextIsVirtual + -NextIsFirstInSequence) * (One + -OpFlags_DoNotUpdateUnexpandedPC) = 0`. -/
theorem rv64Row18_holds_iff (w : WitnessType F params) :
    rv64Row18.Holds w extra ↔ mustStartSequenceFromBeginning w := by
  row_equiv rv64Row18 mustStartSequenceFromBeginning

/-- Compare generated row 19 with `productEqLeftInputMulRightInput` at every padded cycle.
For example, its generated identity is `(LeftInstructionInput) * (RightInstructionInput) = Product`. -/
theorem rv64Row19_holds_iff (w : WitnessType F params) :
    rv64Row19.Holds w extra ↔ productEqLeftInputMulRightInput w := by
  row_equiv rv64Row19 productEqLeftInputMulRightInput

/-- Compare generated row 20 with `shouldBranchEqLookupOutputMulBranch` at every padded cycle.
For example, its generated identity is `(LookupOutput) * (Branch) = ShouldBranch`. -/
theorem rv64Row20_holds_iff (w : WitnessType F params) :
    rv64Row20.Holds w extra ↔ shouldBranchEqLookupOutputMulBranch w := by
  row_equiv rv64Row20 shouldBranchEqLookupOutputMulBranch

/-- Compare generated row 21 with `shouldJumpEqJumpMulNotNextIsNoop` at every padded cycle.
For example, its generated identity is `2 * (NextIsNoop - IsNoop) = (2 - panic) * Halt + HaltPanic`. This comparison is an admitted mismatch. -/
theorem rv64Row21_holds_iff (w : WitnessType F params) :
    (rv64Row21 claimedPanic).Holds w extra ↔ shouldJumpEqJumpMulNotNextIsNoop w := by
  sorry -- mismatch: generated row 21 is the panic-dependent halt lane after Jolt #2451.

/-- Assemble all 22 comparisons, including the admitted row-14 and row-21 mismatches.
For example, the load-address row is checked, while the halt-lane comparison is admitted. -/
theorem rv64Rows_holds_iff (w : WitnessType F params) :
    (∀ row ∈ rv64Rows claimedPanic, row.Holds w extra) ↔
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
    rv64Row00_holds_iff extra w, rv64Row01_holds_iff extra w, rv64Row02_holds_iff extra w, rv64Row03_holds_iff extra w, rv64Row04_holds_iff extra w, rv64Row05_holds_iff extra w, rv64Row06_holds_iff extra w, rv64Row07_holds_iff extra w, rv64Row08_holds_iff extra w, rv64Row09_holds_iff extra w, rv64Row10_holds_iff extra w, rv64Row11_holds_iff extra w, rv64Row12_holds_iff extra w, rv64Row13_holds_iff extra w, rv64Row14_holds_iff extra w, rv64Row15_holds_iff extra w, rv64Row16_holds_iff extra w, rv64Row17_holds_iff extra w, rv64Row18_holds_iff extra w, rv64Row19_holds_iff extra w, rv64Row20_holds_iff extra w, rv64Row21_holds_iff extra claimedPanic w]

/-! ## The four relations -/

/-- Close `claim.Holds w extra ↔ def w` when the claim's pointwise identity is the
handwritten definition up to unfolding; `decide` checks that the claim is well
formed. -/
macro "claim_rfl" : tactic => `(tactic| exact ⟨fun h => h.2, fun h => ⟨by decide, h⟩⟩)

/-- Compare all generated RAM claims with the two old RAM value equations.
For example, generated claim 2 also forbids changing a protected word; that absent old condition makes this an admitted mismatch. -/
theorem ramReadWriteChecking_holds_iff (w : WitnessType F params) :
    ramReadWriteChecking.Holds w extra ↔
      ramReadValueEqRamRead w ∧ ramWriteValueEqRamReadWrite w := by
  sorry -- mismatch: RamReadWriteChecking adds protected-store and selector-sum claims in Jolt #2408; #2509 removes N.

/-- The three generated register claims are the old read/write equations.
For example, the destination claim sums RdWa * (RegistersVal + RdInc) over all 128 registers. -/
theorem registersReadWriteChecking_holds_iff (w : WitnessType F params) :
    registersReadWriteChecking.Holds w extra ↔
      rdWriteValueEqRegistersReadWrite w ∧ rs1ValueEqRegistersRead w ∧
        rs2ValueEqRegistersRead w := by
  refine (and_iff_right (by decide)).trans ?_
  simp only [registersReadWriteChecking, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  refine and_congr ?_ (and_congr ?_ ?_) <;> claim_rfl

/-- Jolt lists the right input's claim first. -/
theorem instructionInputVirtualization_holds_iff (w : WitnessType F params) :
    instructionInputVirtualization.Holds w extra ↔
      rightInstructionInputEqSelection w ∧ leftInstructionInputEqSelection w := by
  refine (and_iff_right (by decide)).trans ?_
  simp only [instructionInputVirtualization, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  refine and_congr ?_ ?_ <;> claim_rfl

/-- Jolt states the last claim as `1 - NextIsNoop = shift(1 - IsNoop)`. At the
last cycle the shift is zero, so `NextIsNoop` is one there, which is the
handwritten `else 1`. -/
theorem spartanShift_holds_iff (w : WitnessType F params) :
    spartanShift.Holds w extra ↔
      nextUnexpandedPCEqShift w ∧ nextPCEqShift w ∧ nextIsVirtualEqShift w ∧
        nextIsFirstInSequenceEqShift w ∧ nextIsNoopEqShift w := by
  refine (and_iff_right (by decide)).trans ?_
  simp only [spartanShift, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · claim_rfl
  · claim_rfl
  · claim_rfl
  · claim_rfl
  unfold RelationClaim.Holds nextIsNoopEqShift
  refine (and_iff_right (by decide)).trans ?_
  simp only [ClaimExpr.eval, RelationPoly.cycleValue, Int.cast_one]
  refine forall_congr' fun t => ?_
  split_ifs <;> constructor <;> intro h <;> linear_combination -h

/-! ## Per-kind flags, lookup table and RAF flag -/

/-- Every generated circuit flag occurs in the generated order; for example, Halt is included. -/
theorem mem_circuitFlagOrder (f : CircuitFlag) : f ∈ circuitFlagOrder := by
  cases f <;> decide

/-- Every instruction flag occurs in the generated order; for example, IsNoop is included. -/
theorem mem_instructionFlagOrder (f : InstructionFlags) : f ∈ instructionFlagOrder := by
  cases f <;> decide

/-- Jolt's canonical-stamp circuit flags of an instruction's kind are the
flags `opcodeFlag` sets, in Jolt's order. -/
theorem kindCircuitFlags_kindOf (i : JoltISA.Instr) :
    kindCircuitFlags (kindOf i) = circuitFlagOrder.filter (legacyOpcodeFlag i ·) := by
  cases i <;> rfl

/-- Old instruction-routing flags equal the generated kind entry.
For example, LD selects RightOperandIsRdWriteValue. -/
theorem kindInstructionFlags_kindOf (i : JoltISA.Instr) :
    kindInstructionFlags (kindOf i) =
      instructionFlagOrder.filter (JoltMetadata.instructionFlag i ·) := by
  cases i <;> rfl

/-- Old lookup-table selections equal the generated entries after embedding names.
For example, AND selects the generated And table. -/
theorem kindLookupTable_kindOf (i : JoltISA.Instr) :
    kindLookupTable (kindOf i) = (JoltMetadata.lookupTable i).map liftLookupTable := by
  cases i <;> rfl

/-- The old RAF selector equals the generated kind entry.
For example, the combined-operand ADD kind has its old RAF flag. -/
theorem kindRafFlag_kindOf (i : JoltISA.Instr) :
    kindRafFlag (kindOf i) = JoltMetadata.instructionRafFlag i := by
  cases i <;> rfl

/-! `kindOf` maps each `JoltISA.Instr` constructor to the Jolt kind of the same
name.
The elaboration-time check preserves that name test and checks the exact set
of missing kinds against the four recorded repin gaps.
An unrecorded gap, or a mapping arm naming the wrong kind, fails the build.
The total-coverage expectation is separately stated with a marked mismatch
below; the check does not claim those four old constructors exist. -/

open Lean Meta in
run_meta do
  let env ← getEnv
  let some (.inductInfo instr) := env.find? ``JoltISA.Instr
    | throwError "JoltISA.Instr is not an inductive type"
  let some (.inductInfo kind) := env.find? ``Generated.JoltKind
    | throwError "JoltKind is not an inductive type"
  let instrNames := instr.ctors.map (·.lastComponentAsString)
  for c in instr.ctors do
    let ctor ← getConstInfoCtor c
    let image ← forallTelescope ctor.type fun xs _ =>
      whnf (mkApp (mkConst ``kindOf) (mkAppN (mkConst c) xs))
    let some k := image.constName?
      | throwError "kindOf {c} does not reduce to a JoltKind constructor"
    unless k.lastComponentAsString == c.lastComponentAsString do
      throwError "kindOf maps {c} to {k}"
  let expectedMissing := ["VirtualXORROT2", "VirtualXORROT61", "JoltSuccess", "JoltPanic"]
  let missing := (kind.ctors.map (·.lastComponentAsString)).filter fun n =>
    n != "NoOp" && !instrNames.contains n
  unless missing.length == expectedMissing.length &&
      expectedMissing.all missing.contains do
    throwError "Kind coverage mismatch changed: expected {expectedMissing}, found {missing}"

/-- Total kind coverage expected by T3, including kinds the old ISA cannot yet express.
For example, `JoltSuccess` currently has no preimage; this is an admitted mismatch,
not a certificate that the old ISA models halts or the two new XOR rotations. -/
theorem kindCoverage_matches : ∀ k : JoltKind,
    k = .NoOp ∨ ∃ i : JoltISA.Instr, kindOf i = k := by
  sorry -- mismatch: JoltSuccess/JoltPanic (#2417), VirtualXORROT2/VirtualXORROT61 (#2369) have no old constructors.

/-- Generated kind-list membership reads the old opcode flag.
For example, Load belongs to the LD entry, and Halt belongs to no old instruction entry. -/
theorem mem_kindCircuitFlags_kindOf (i : JoltISA.Instr) (f : CircuitFlag) :
    f ∈ kindCircuitFlags (kindOf i) ↔ legacyOpcodeFlag i f = true := by
  simp [kindCircuitFlags_kindOf, List.mem_filter, mem_circuitFlagOrder]

/-- Generated routing-list membership reads the old instruction flag.
For example, RightOperandIsRdWriteValue belongs to the LD entry. -/
theorem mem_kindInstructionFlags_kindOf (i : JoltISA.Instr) (f : InstructionFlags) :
    f ∈ kindInstructionFlags (kindOf i) ↔ JoltMetadata.instructionFlag i f = true := by
  simp [kindInstructionFlags_kindOf, List.mem_filter, mem_instructionFlagOrder]

/-! ## Flags set by the sequence stamp -/

/-- `stampFlags` of a row's stamp class, case by case. -/
theorem mem_stampFlags_stampClass (row : JoltInstructionRow) (f : CircuitFlag) :
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
theorem circuitFlag_iff_generated (row : JoltInstructionRow) (f : CircuitFlag) :
    legacyCircuitFlag row f = true ↔ f ∈ generatedCircuitFlags row := by
  rw [generatedCircuitFlags, List.mem_append, mem_kindCircuitFlags_kindOf,
    mem_stampFlags_stampClass]
  rcases row with ⟨instruction, address, vsr, first, compressed⟩
  cases f <;> simp [legacyCircuitFlag, legacyOpcodeFlag, JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag]

/-! ## Padding rows are Jolt's `NoOp` -/

/-- A padding bytecode address sets the circuit flags of Jolt's `NoOp`. -/
theorem padding_circuitFlag (f : CircuitFlag) :
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

/-- Assemble the expected old-model-to-generated implication, using the marked
row-14, row-21 and RAM-relation admissions above.
For example, the load rows are proved, but the new halt lane and protected-store
claim remain mismatches, so this theorem is not a Jolt-main correctness certificate.
The row list uses the context's `io.panic` as the public panic bit.
`ConstraintEquations` has 29 further conjuncts that T3 does not generate. -/
theorem ConstraintEquations.generated {bytecode : Array JoltInstructionRow}
    {initialRam : Nat → BitVec 64} {io : JoltDevice} {entry : Fin (2 ^ params.logBytecodeK)}
    {w : WitnessType F params} (h : ConstraintEquations bytecode initialRam io entry w) :
    (∀ row ∈ rv64Rows io.panic, row.Holds w extra) ∧ ramReadWriteChecking.Holds w extra ∧
      registersReadWriteChecking.Holds w extra ∧ instructionInputVirtualization.Holds w extra ∧
      spartanShift.Holds w extra :=
  ⟨(rv64Rows_holds_iff extra io.panic w).2 ⟨h.ramAddrEqRs1PlusImmMinusLookupIfLoadStore, h.ramAddrEqZeroIfNotLoadStore, h.ramReadEqRamWriteIfLoad, h.ramReadEqRdWriteIfLoad, h.rs2EqRamWriteIfStore, h.leftLookupZeroIfAddSubMul, h.leftLookupEqLeftInputOtherwise, h.rightLookupAdd, h.rightLookupSub, h.rightLookupEqProductIfMul, h.rightLookupEqRightInputOtherwise, h.assertLookupOne, h.rdWriteEqLookupIfWriteLookupToRd, h.rdWriteEqPCPlusConstIfJump, h.nextUnexpandedPCEqLookupIfShouldJump, h.nextUnexpandedPCEqPCPlusImmIfShouldBranch, h.nextUnexpandedPCUpdateOtherwise, h.nextPCEqPCPlusOneIfInline, h.mustStartSequenceFromBeginning, h.productEqLeftInputMulRightInput, h.shouldBranchEqLookupOutputMulBranch, h.shouldJumpEqJumpMulNotNextIsNoop⟩,
    (ramReadWriteChecking_holds_iff extra w).2 ⟨h.ramReadValueEqRamRead, h.ramWriteValueEqRamReadWrite⟩,
    (registersReadWriteChecking_holds_iff extra w).2
      ⟨h.rdWriteValueEqRegistersReadWrite, h.rs1ValueEqRegistersRead, h.rs2ValueEqRegistersRead⟩,
    (instructionInputVirtualization_holds_iff extra w).2
      ⟨h.rightInstructionInputEqSelection, h.leftInstructionInputEqSelection⟩,
    (spartanShift_holds_iff extra w).2
      ⟨h.nextUnexpandedPCEqShift, h.nextPCEqShift, h.nextIsVirtualEqShift,
        h.nextIsFirstInSequenceEqShift, h.nextIsNoopEqShift⟩⟩


end JoltConstraints.ConstraintGen
