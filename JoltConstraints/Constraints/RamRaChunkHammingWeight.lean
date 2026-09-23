import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (62) in `constraints.md` (stage 7):
each RAM-address chunk has hamming weight equal to RamHammingWeight at that cycle.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs#L82-L90 -/
def ramRaChunkHammingWeight {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.ramChunks) (t : Fin params.traceLength),
    (∑ entry : Fin (2 ^ params.chunkBits), witness.RamRaChunk chunk entry t) =
      witness.RamHammingWeight t

/-- The honest witness satisfies constraint (62); proof pending.
RamFits ensures every nonzero raw access remaps, so the raw-address activity
flag agrees with the presence of a selected RAM chunk entry. -/
theorem honestWitness_ramRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramRaChunkHammingWeight
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
