import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (60) in `constraints.md` (stage 7):
every instruction-address chunk selects exactly one entry at every padded cycle.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs#L82-L90 -/
def instructionRaChunkHammingWeight {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.instructionChunks) (t : Fin params.traceLength),
    (∑ entry : Fin (2 ^ params.chunkBits), witness.InstructionRaChunk chunk entry t) = 1

/-- The honest witness satisfies constraint (60); proof pending. -/
theorem honestWitness_instructionRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength) :
    instructionRaChunkHammingWeight
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
