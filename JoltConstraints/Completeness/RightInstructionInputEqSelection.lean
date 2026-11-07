import JoltConstraints.Constraints.RightInstructionInputEqSelection
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (33) selects a sum of flagged inputs, including the captured
load destination; for example, ShiftData selects both its address and immediate.
Jolt's verifier: `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs`
(`InputVirtualization::unbatched_relation`) at `c6703570`. -/
theorem honestWitness_rightInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightInstructionInputEqSelection
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · simp only [HonestTrace.honestWitness, TraceWitness.RightInstructionInput,
      TraceWitness.InstructionFlags, dif_pos h, ite_mul, one_mul, zero_mul]
  · simp [HonestTrace.honestWitness, TraceWitness.RightInstructionInput,
      TraceWitness.InstructionFlags, h]

end JoltConstraints
