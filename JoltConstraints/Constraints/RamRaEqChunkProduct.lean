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

/-- Completeness target for the honest witness.
At least one RAM chunk is required: a padding row has RamRa = 0, whereas an
empty product is 1. RamFits rules out remapping failures and address truncation. -/
theorem honestWitness_ramRaEqChunkProduct
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (ramChunksPos : 0 < params.ramChunks) :
    ramRaEqChunkProduct
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  have cover : params.logRamK ≤ params.ramChunks * params.chunkBits := by
    dsimp [WitnessParams.ramChunks]
    have hrem := Nat.mod_lt (params.logRamK + params.chunkBits - 1)
      params.chunkBits_pos
    have hdiv := Nat.mod_add_div
      (params.logRamK + params.chunkBits - 1) params.chunkBits
    have hdiv' :
        (params.logRamK + params.chunkBits - 1) % params.chunkBits +
        (params.logRamK + params.chunkBits - 1) / params.chunkBits *
          params.chunkBits = params.logRamK + params.chunkBits - 1 := by
      simpa [Nat.mul_comm] using hdiv
    omega
  intro address t
  dsimp [ramRaEqChunkProduct, JoltProgram.honestWitness,
    HonestWitness.RamRa, HonestWitness.RamRaChunk]
  cases hr : HonestWitness.remappedRamAddress trace t.val with
  | none =>
      simp [HonestWitness.addressChunkEntry]
      rw [zero_pow (Nat.ne_of_gt ramChunksPos)]
  | some b =>
      by_cases heq : b = address.val
      · subst b
        simp [HonestWitness.addressChunkEntry, ramAddressChunk,
          HonestWitness.addressChunk]
      · have hdiff : ∃ chunk : Fin params.ramChunks,
            HonestWitness.addressChunk params.chunkBits chunk address.val ≠
              HonestWitness.addressChunk params.chunkBits chunk b := by
          by_contra hn
          have hd : ∀ chunk : Fin params.ramChunks,
              HonestWitness.addressChunk params.chunkBits chunk address.val =
                HonestWitness.addressChunk params.chunkBits chunk b := by
            intro chunk
            by_contra hneq
            exact hn ⟨chunk, hneq⟩
          have ha : address.val < 2 ^ (params.ramChunks * params.chunkBits) :=
            address.isLt.trans_le
              (Nat.pow_le_pow_right (by decide) cover)
          have hb : b < 2 ^ (params.ramChunks * params.chunkBits) :=
            (params.remappedRamAddress_lt trace ramFits t b hr).trans_le
              (Nat.pow_le_pow_right (by decide) cover)
          exact heq (HonestWitness.addressChunk_injective params.chunkBits
            params.ramChunks address.val b ha hb hd).symm
        obtain ⟨chunk, hneq⟩ := hdiff
        have hopt : (some b : Option Nat) ≠ some address.val := by
          simp [heq]
        rw [if_neg hopt]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ chunk)
        change address.val /
          2 ^ ((params.ramChunks - 1 - chunk.val) * params.chunkBits) %
          2 ^ params.chunkBits ≠ b /
          2 ^ ((params.ramChunks - 1 - chunk.val) * params.chunkBits) %
          2 ^ params.chunkBits at hneq
        change (if address.val /
          2 ^ ((params.ramChunks - 1 - chunk.val) * params.chunkBits) %
          2 ^ params.chunkBits = HonestWitness.addressChunk params.chunkBits chunk b
          then (1 : F) else 0) = 0
        exact if_neg hneq

end JoltConstraints
