import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (22) in `constraints.md` (stage 2):
ShouldJump is the jump flag multiplied by one minus the next no-op flag.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def shouldJumpEqJumpMulNotNextIsNoop {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldJump t = witness.OpFlags .Jump t * (1 - witness.NextIsNoop t)

/-- Completeness target for the honest witness; proof pending.
Strict padding ensures that the final cycle is a no-op, as in Rust
`ProverConfig::derive_from_rows`; a final real jump would violate this equation. -/
theorem honestWitness_shouldJumpEqJumpMulNotNextIsNoop
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    shouldJumpEqJumpMulNotNextIsNoop
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain) := by
  intro t
  by_cases next : t.val + 1 < params.traceLength
  · simp [JoltProgram.honestWitness, HonestWitness.ShouldJump,
      HonestWitness.NextIsNoop, next]
  · have padding : ¬ t.val < trace.rows.size := by
      have rowsLt := tracePadded.2
      omega
    simp [JoltProgram.honestWitness, HonestWitness.ShouldJump,
      HonestWitness.NextIsNoop, HonestWitness.OpFlags, next, padding]

end JoltConstraints
