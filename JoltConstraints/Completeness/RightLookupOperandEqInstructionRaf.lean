import JoltConstraints.Completeness.Helpers.InstructionReadSelection
import JoltConstraints.Constraints.RightLookupOperandEqInstructionRaf
import JoltConstraints.Soundness.Layer4.Interleave

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- A combined index selects all 128 bits; otherwise its even bits give the
right operand, for example 2 from the interleaving of 1 and 2.
Jolt's verifier: `crates/jolt-claims/src/protocols/jolt/relations/instruction/read_raf.rs`
(`ReadRaf::output_expression`) at `c6703570`. -/
private theorem rightLookupRaf_select {F : Type} [Field F]
    (combined : Bool) (index : BitVec 128) :
    (if combined then (index.toNat : F) else ((uninterleave index.toFin).2.toNat : F)) =
      (1 - if combined then 1 else 0) * lookupAddressRight index.toFin +
        (if combined then 1 else 0) * (index.toNat : F) := by
  cases combined <;> simp [lookupAddressRight_eq_uninterleave]

/-- Completeness of constraint (41) for the honest witness.
Uses the address-chunk selection and operand-encoding correspondence.
For example, an addition row selects the full 128-bit index, while LD selects
its even bits, which encode the captured destination.
Jolt's prover: `crates/jolt-witness/src/witnesses/operands.rs`
(`RightLookupOperand`) at `c6703570`. -/
theorem honestWitness_rightLookupOperandEqInstructionRaf
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : rightLookupOperandEqInstructionRaf
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  rw [instructionRead_honest params trace ramFits traceFits bytecodeDomain
    (fun address =>
      (1 - (HonestTrace.honestWitness (F := F) params trace).InstructionRafFlag t) *
          lookupAddressRight address +
        (HonestTrace.honestWitness (F := F) params trace).InstructionRafFlag t *
          (address.val : F)) t]
  by_cases inBounds : t.val < trace.rows.size
  · simp only [HonestTrace.honestWitness, TraceWitness.RightLookupOperand,
      TraceWitness.InstructionRafFlag, inBounds, dite_true]
    exact rightLookupRaf_select _ _
  · simp [HonestTrace.honestWitness, TraceWitness.RightLookupOperand,
      TraceWitness.InstructionRafFlag, TraceWitness.lookupIndex,
      lookupAddressRight, inBounds]

end JoltConstraints
