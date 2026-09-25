import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (55) in `constraints.md` (stage 6a–6b):
every bytecode-address chunk selector is Boolean.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L40-L58 -/
def bytecodeRaChunkBooleanity {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.bytecodeChunks) (entry : Fin (2 ^ params.chunkBits))
      (t : Fin params.traceLength),
    witness.BytecodeRaChunk chunk entry t *
      (witness.BytecodeRaChunk chunk entry t - 1) = 0

/-- The honest witness satisfies constraint (55). -/
theorem honestWitness_bytecodeRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    bytecodeRaChunkBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk entry t
  dsimp [JoltProgram.honestWitness, HonestWitness.BytecodeRaChunk,
    HonestWitness.addressChunkEntry]
  split_ifs <;> simp_all

end JoltConstraints
