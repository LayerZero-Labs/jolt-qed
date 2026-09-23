import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The small chunk at offset h inside virtual chunk j has index j*n + h,
where n = virtualChunkBits / chunkBits. The parameter divisibility proofs
establish that this index is in range; no modulo wrapping is used. -/
def instructionSmallChunkIndex (params : WitnessParams)
    (chunk : Fin params.virtualInstructionChunks)
    (offset : Fin (params.virtualChunkBits / params.chunkBits)) : Fin params.instructionChunks :=
  ⟨chunk.val * (params.virtualChunkBits / params.chunkBits) + offset.val, by
    have chunkLt : chunk.val < 128 / params.virtualChunkBits := chunk.isLt
    have offsetLt := offset.isLt
    have bitsPos := params.chunkBits_pos
    change _ < (128 + params.chunkBits - 1) / params.chunkBits
    calc
      _ < chunk.val * (params.virtualChunkBits / params.chunkBits) +
          params.virtualChunkBits / params.chunkBits := Nat.add_lt_add_left offsetLt _
      _ = (chunk.val + 1) * (params.virtualChunkBits / params.chunkBits) := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (128 / params.virtualChunkBits) * (params.virtualChunkBits / params.chunkBits) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt chunkLt)
      _ = 128 / params.chunkBits :=
        Nat.div_mul_div params.virtualChunkBits_dvd_lookup params.chunkBits_dvd_virtual
      _ ≤ (128 + params.chunkBits - 1) / params.chunkBits := Nat.div_le_div_right (by omega)⟩

/-- Split a virtual address into small digits in most-significant-first order. -/
def instructionVirtualAddressDigit (params : WitnessParams)
    (address : Fin (2 ^ params.virtualChunkBits))
    (offset : Fin (params.virtualChunkBits / params.chunkBits)) : Fin (2 ^ params.chunkBits) :=
  ⟨(address.val / 2 ^ ((params.virtualChunkBits / params.chunkBits - 1 - offset.val) *
      params.chunkBits)) % 2 ^ params.chunkBits,
    Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)⟩

/-- Constraint (59) in `constraints.md`: each virtual instruction selector is
reconstructed from its consecutive small chunks.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs#L402-L417 -/
def instructionRaEqChunkProduct {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (chunk : Fin params.virtualInstructionChunks)
      (address : Fin (2 ^ params.virtualChunkBits)) (t : Fin params.traceLength),
    witness.InstructionRa chunk address t =
      ∏ offset : Fin (params.virtualChunkBits / params.chunkBits),
        witness.InstructionRaChunk (instructionSmallChunkIndex params chunk offset)
          (instructionVirtualAddressDigit params address offset) t

/-- Completeness target for the honest witness; proof pending.
The small and virtual chunks decompose the same 128-bit lookup address.
WitnessParams carries both required chunk-width divisibility conditions. -/
theorem honestWitness_instructionRaEqChunkProduct
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace) :
    instructionRaEqChunkProduct
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
