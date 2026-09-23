import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (56) in `constraints.md` (stage 6a–6b):
every RAM-address chunk selector is Boolean.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L40-L58 -/
def ramRaChunkBooleanity {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.ramChunks) (entry : Fin (2 ^ params.chunkBits))
      (t : Fin params.traceLength),
    witness.RamRaChunk chunk entry t *
      (witness.RamRaChunk chunk entry t - 1) = 0

/-- The honest witness satisfies constraint (56). -/
theorem honestWitness_ramRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramRaChunkBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk entry t
  dsimp [JoltProgram.honestWitness, HonestWitness.RamRaChunk,
    HonestWitness.addressChunkEntry]
  cases h : HonestWitness.remappedRamAddress trace t.val <;> simp_all

end JoltConstraints
