import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (56) in `constraints.md` (stage 6a–6b):
every RAM-address chunk selector is Boolean.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L39-L61 -/
def ramRaChunkBooleanity {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.ramChunks) (entry : Fin (2 ^ params.chunkBits))
      (t : Fin params.traceLength),
    witness.RamRaChunk chunk entry t *
      (witness.RamRaChunk chunk entry t - 1) = 0

end JoltConstraints
