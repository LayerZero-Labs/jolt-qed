import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (54) in `constraints.md` (stage 6a–6b):
every instruction-address chunk selector is Boolean.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L39-L61 -/
def instructionRaChunkBooleanity {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.instructionChunks) (entry : Fin (2 ^ params.chunkBits))
      (t : Fin params.traceLength),
    witness.InstructionRaChunk chunk entry t *
      (witness.InstructionRaChunk chunk entry t - 1) = 0

end JoltConstraints
