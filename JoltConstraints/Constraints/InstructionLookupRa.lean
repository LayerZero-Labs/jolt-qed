import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.lookup_table
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The `chunk`th virtual chunk of a 128-bit lookup address, most significant first. -/
def instructionLookupChunk (params : WitnessParams) (address : Fin (2 ^ 128))
    (chunk : Fin params.virtualInstructionChunks) : Fin (2 ^ params.virtualChunkBits) :=
  ⟨(address.val /
      2 ^ ((params.virtualInstructionChunks - 1 - chunk.val) * params.virtualChunkBits)) %
      2 ^ params.virtualChunkBits,
    Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)⟩

/-- `LookupRa(x,t)` in `constraints.md`: multiply the virtual instruction-address
entries selected by the chunks of `x`. -/
noncomputable def instructionLookupRa {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (address : Fin (2 ^ 128))
    (t : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.virtualInstructionChunks,
    witness.InstructionRa chunk (instructionLookupChunk params address chunk) t

end JoltConstraints
