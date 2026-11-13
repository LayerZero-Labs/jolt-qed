import JoltConstraints.Constraints.ShouldJumpEqJumpMulNotNextIsNoop
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies `ShouldJump = Jump · (1 − NextIsNoop)`. At the
final cycle the missing successor counts as a no-op and `ShouldJump` is zero, so
the equation holds there too, also when a real jump fills the last cycle.
See jolt/crates/jolt-witness/src/witnesses/flags.rs:28-34, 116-128 at 3cc6e7bd1. -/
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
  · simp [HonestTrace.honestWitness, TraceWitness.ShouldJump,
      TraceWitness.NextIsNoop, next]

end JoltConstraints
