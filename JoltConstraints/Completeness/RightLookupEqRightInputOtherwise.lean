import JoltConstraints.Constraints.RightLookupEqRightInputOtherwise
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Completeness.Helpers.AddressSum
import JoltConstraints.Soundness.Layer4.Interleave

set_option autoImplicit false

namespace JoltConstraints

/-- The address source and signed immediate of ShiftDataB/H/W, or `none`
for other instructions; for example, ShiftDataB with address x2 and offset -2
returns `(x2, -2)`.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs`
(`LookupQuery::to_instruction_inputs`) at `c6703570`. -/
def shiftDataAddress? : JoltISA.Instr → Option (JoltISA.Src × BitVec 64)
  | .VirtualShiftDataB _ _ address imm | .VirtualShiftDataH _ _ address imm
  | .VirtualShiftDataW _ _ address imm => some (address, imm)
  | _ => none

/-- Constraint (11) has the form
`g · (RightLookupOperand t - RightInstructionInput t) = 0`,
where `g = 1 - AddOperands - SubtractOperands - MultiplyOperands - Advice`.
On a ShiftData row, that is when the instruction at cycle `t` is
`VirtualShiftDataB`, `VirtualShiftDataH` or `VirtualShiftDataW`, `g = 1`.
So (11) needs `RightLookupOperand t = RightInstructionInput t`.
Jolt's prover sets `RightInstructionInput t = rs2 + imm` and
`RightLookupOperand t = (rs2 + imm) mod 2^64`.
When `rs2 + imm` wraps, for example `rs2 = 0` and `imm = -16`, the two differ
by `2^64`, and the constraint is not satisfied.
Left as `sorry` until a16z/jolt#1949 is fixed.

Rust, at `c6703570`:
- (11): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
  (`RightLookupEqRightInputOtherwise`).
- ShiftData's flags, so `g = 1`: `crates/jolt-riscv/src/instructions/virt/shift_data_b.rs`
  (`jolt_instruction!`).
- `RightInstructionInput = rs2 + imm`:
  `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs`
  (`LookupQuery::to_instruction_inputs`).
- `RightLookupOperand` wrapped to 64 bits: `crates/jolt-lookup-tables/src/traits.rs`
  (`LookupQuery::to_lookup_operands`, `(y as u64) as u128`).
- Both read by Jolt's prover in `crates/jolt-witness/src/witnesses/operands.rs`
  (`RightInstructionInput`, `RightLookupOperand`). -/
theorem _root_.HonestTrace.shiftData_address_noWrap
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Nat) (inBounds : t < trace.rows.size)
    {address : JoltISA.Src} {imm : BitVec 64}
    (shiftData : shiftDataAddress? trace.bytecode[(trace.rows[t]'inBounds).rowIndex].instruction =
      some (address, imm)) :
    let sum := ((JoltISA.sourceValue address (trace.rows[t]'inBounds).preState).toNat : Int) + imm.toInt
    0 ≤ sum ∧ sum < 2 ^ 64 := by
  sorry

/-- A ShiftData row's wrapped address casts to its right instruction input;
for example, address 10 and immediate -2 both encode field value 8.
The bounds come only from the approved honest-row #1949 obligation.
Jolt's prover: `crates/jolt-lookup-tables/src/traits.rs`
(`LookupQuery::to_lookup_operands`) at `c6703570`. -/
private theorem shiftData_lookup_sum {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Nat) (ht : t < trace.rows.size)
    {address : JoltISA.Src} {imm : BitVec 64}
    (shiftData : shiftDataAddress? trace.bytecode[(trace.rows[t]'ht).rowIndex].instruction =
      some (address, imm)) :
    (((JoltISA.sourceValue address (trace.rows[t]'ht).preState) + imm).toNat : F) =
      ((JoltISA.sourceValue address (trace.rows[t]'ht).preState).toNat : F) + (imm.toInt : F) := by
  have bounds := trace.shiftData_address_noWrap t ht shiftData
  have cast := encodedInt_cast (F := F) 64 _ bounds.1 bounds.2
  simpa only [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.ofInt_toInt, BitVec.setWidth_eq, Int.cast_add, Int.cast_natCast] using cast

/-- On an honest separate-operand row, the lookup index's even bits encode the selected
right input; LD uses its captured destination and ShiftData uses address plus
immediate, for example 10 + (-2) = 8, subject to the explicit #1949 obligation.
Jolt's prover: `crates/jolt-lookup-tables/src/traits.rs` (`to_lookup_operands`)
and `instructions/virt/shift_data_b.rs` (`to_instruction_inputs`) at `c6703570`. -/
private theorem lookupIndex_right_eq_input {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (t : Fin params.traceLength) (ht : t.val < trace.rows.size)
    (separate : JoltMetadata.hasCombinedLookupOperands
      trace.bytecode[(trace.rows[t.val]'ht).rowIndex].instruction ≠ true) :
    ((uninterleave (TraceWitness.lookupIndex trace t.val).toFin).2.toNat : F) =
      TraceWitness.RightInstructionInput params trace t := by
  have unpackZero : uninterleave (0 : Fin (2^128)) = (0, 0) := rfl
  simp only [Fin.getElem_fin] at separate
  simp only [TraceWitness.lookupIndex, TraceWitness.RightInstructionInput,
    TraceWitness.Rs2Value, TraceWitness.Imm, TraceWitness.RdWriteValue, ht, dif_pos]
  generalize hi : trace.bytecode[(trace.rows[t.val]'ht).rowIndex.val].instruction = instruction
    at separate ⊢
  cases instruction <;>
    simp [JoltMetadata.hasCombinedLookupOperands, JoltMetadata.opcodeFlag] at separate
  all_goals simp [TraceWitness.instructionLookupIndex, JoltMetadata.instructionFlag,
    JoltMetadata.immediate, TraceWitness.rdValue, uninterleave_interleave,
    unpackZero]
  all_goals first
    | simpa only [BitVec.toNat_add, Nat.reducePow] using
        (shiftData_lookup_sum (F := F) trace t.val ht (by simp [shiftDataAddress?, hi]))
    | norm_cast

private theorem rightLookupOtherwiseForOpcode {F : Type} [Field F]
    (instruction : JoltISA.Instr) (lookup right : F) :
    ((1 : F) - (if JoltMetadata.opcodeFlag instruction .AddOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .SubtractOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .MultiplyOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .Advice then 1 else 0)) *
      ((if JoltMetadata.hasCombinedLookupOperands instruction then lookup else right) - right) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, JoltMetadata.hasCombinedLookupOperands]

/-- Constraint (11) preserves the right input on separate-operand rows;
for example, LD's right input is its captured destination.
ShiftData's address sum uses the explicit #1949 wrap obligation.
Jolt's verifier: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`RightLookupEqRightInputOtherwise`) at `c6703570`. -/
theorem honestWitness_rightLookupEqRightInputOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightLookupEqRightInputOtherwise
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · by_cases combined : JoltMetadata.hasCombinedLookupOperands
        trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex].instruction = true
    · simp only [Fin.getElem_fin] at combined
      simpa [HonestTrace.honestWitness, TraceWitness.OpFlags,
        TraceWitness.RightLookupOperand, JoltMetadata.circuitFlag, inBounds, combined] using
          (rightLookupOtherwiseForOpcode (F := F)
            trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex].instruction
            ((TraceWitness.lookupIndex trace t.val).toNat : F)
            (TraceWitness.RightInstructionInput params trace t))
    · have input := lookupIndex_right_eq_input (F := F) params trace t inBounds combined
      simp only [Fin.getElem_fin] at combined
      simp [HonestTrace.honestWitness, TraceWitness.RightLookupOperand,
        inBounds, combined, input]
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.RightLookupOperand, TraceWitness.RightInstructionInput, inBounds]

end JoltConstraints
