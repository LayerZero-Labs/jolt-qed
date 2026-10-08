import JoltConstraints.Constraints.ShouldJumpEqJumpMulNotNextIsNoop
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness; proof pending.
Strict padding ensures that the final cycle is a no-op, as in Rust
`ProverConfig::derive_from_rows`; a final real jump would violate this equation. -/
theorem honestWitness_shouldJumpEqJumpMulNotNextIsNoop
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    shouldJumpEqJumpMulNotNextIsNoop
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases next : t.val + 1 < params.traceLength
  · simp [HonestTrace.honestWitness, TraceWitness.ShouldJump,
      TraceWitness.NextIsNoop, next]
  · have padding : ¬ t.val < trace.rows.size := by
      have rowsLt := tracePadded.2
      omega
    simp [HonestTrace.honestWitness, TraceWitness.ShouldJump,
      TraceWitness.NextIsNoop, TraceWitness.OpFlags, next, padding]

end JoltConstraints
