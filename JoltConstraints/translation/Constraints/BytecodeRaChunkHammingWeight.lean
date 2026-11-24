import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (61) in `constraints.md` (stage 7):
every bytecode-address chunk selects exactly one entry at every padded cycle.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs -/
def bytecodeRaChunkHammingWeight {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.bytecodeChunks) (t : Fin params.traceLength),
    (∑ entry : Fin (2 ^ params.chunkBits), witness.BytecodeRaChunk chunk entry t) = 1

end JoltConstraints
