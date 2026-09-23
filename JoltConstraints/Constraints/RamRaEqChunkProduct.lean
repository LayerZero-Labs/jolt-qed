import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- A remapped RAM address digit, most significant first, including leading zero bits. -/
def ramAddressChunk (params : WitnessParams) (address : Fin params.ramSize)
    (chunk : Fin params.ramChunks) : Fin (2 ^ params.chunkBits) :=
  ⟨(address.val / 2 ^ ((params.ramChunks - 1 - chunk.val) * params.chunkBits)) %
      2 ^ params.chunkBits,
    Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)⟩

/-- Constraint (58) in `constraints.md` (stage 6b):
the full RAM address selector is the product of its selected address chunks.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/ram.rs#L163-L172 -/
def ramRaEqChunkProduct {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
    witness.RamRa address t =
      ∏ chunk : Fin params.ramChunks,
        witness.RamRaChunk chunk (ramAddressChunk params address chunk) t

/-- Completeness target for the honest witness; proof pending.
At least one RAM chunk is required: a padding row has RamRa = 0, whereas an
empty product is 1. RamFits rules out remapping failures and address truncation. -/
theorem honestWitness_ramRaEqChunkProduct
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength)
    (ramChunksPos : 0 < params.ramChunks) :
    ramRaEqChunkProduct
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
