import JoltConstraints.Constraints.InstructionRaEqChunkProduct
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

private theorem mod_pow_div_digit (x bits n offset : Nat) (ho : offset < n) :
    (x % 2 ^ (n * bits) / 2 ^ ((n - 1 - offset) * bits)) % 2 ^ bits =
      (x / 2 ^ ((n - 1 - offset) * bits)) % 2 ^ bits := by
  have hpow : 2 ^ (n * bits) =
      2 ^ ((n - 1 - offset) * bits) * 2 ^ ((offset + 1) * bits) := by
    rw [← pow_add]
    rw [← add_mul]
    have hsum : n - 1 - offset + (offset + 1) = n := by omega
    rw [hsum]
  rw [hpow, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  apply pow_dvd_pow 2
  have : 1 ≤ offset + 1 := by omega
  simpa only [one_mul] using Nat.mul_le_mul_right bits this

private theorem instruction_shift_split (p : WitnessParams)
    (chunk : Fin p.virtualInstructionChunks)
    (offset : Fin (p.virtualChunkBits / p.chunkBits)) :
    (p.instructionChunks - 1 - (instructionSmallChunkIndex p chunk offset).val) * p.chunkBits =
      (p.virtualInstructionChunks - 1 - chunk.val) * p.virtualChunkBits +
        (p.virtualChunkBits / p.chunkBits - 1 - offset.val) * p.chunkBits := by
  rcases p.proverChunkConfig with ⟨_, hb, hv⟩ | ⟨_, hb, hv⟩
  · have hc : chunk.val < 8 := by
      simpa [WitnessParams.virtualInstructionChunks, hv] using chunk.isLt
    have ho : offset.val < 4 := by simpa [hb, hv] using offset.isLt
    simp [instructionSmallChunkIndex, WitnessParams.instructionChunks,
      WitnessParams.virtualInstructionChunks, hb, hv]
    omega
  · have hc : chunk.val < 4 := by
      simpa [WitnessParams.virtualInstructionChunks, hv] using chunk.isLt
    have ho : offset.val < 4 := by simpa [hb, hv] using offset.isLt
    simp [instructionSmallChunkIndex, WitnessParams.instructionChunks,
      WitnessParams.virtualInstructionChunks, hb, hv]
    omega

private theorem virtual_digit_eq_small (p : WitnessParams)
    (chunk : Fin p.virtualInstructionChunks)
    (offset : Fin (p.virtualChunkBits / p.chunkBits)) (x : Nat) :
    (HonestWitness.addressChunk p.virtualChunkBits chunk x /
        2 ^ ((p.virtualChunkBits / p.chunkBits - 1 - offset.val) * p.chunkBits)) %
        2 ^ p.chunkBits =
      HonestWitness.addressChunk p.chunkBits
        (instructionSmallChunkIndex p chunk offset) x := by
  let coarse := (p.virtualInstructionChunks - 1 - chunk.val) * p.virtualChunkBits
  let inner := (p.virtualChunkBits / p.chunkBits - 1 - offset.val) * p.chunkBits
  let small := (p.instructionChunks - 1 -
    (instructionSmallChunkIndex p chunk offset).val) * p.chunkBits
  have hsum : small = coarse + inner := instruction_shift_split p chunk offset
  have hbits : (p.virtualChunkBits / p.chunkBits) * p.chunkBits =
      p.virtualChunkBits := Nat.div_mul_cancel p.chunkBits_dvd_virtual
  change ((x / 2 ^ coarse % 2 ^ p.virtualChunkBits) / 2 ^ inner) %
      2 ^ p.chunkBits = (x / 2 ^ small) % 2 ^ p.chunkBits
  rw [← hbits]
  rw [mod_pow_div_digit (x / 2 ^ coarse) p.chunkBits
    (p.virtualChunkBits / p.chunkBits) offset.val offset.isLt]
  rw [Nat.div_div_eq_div_mul]
  rw [← pow_add, ← hsum]

/-- Completeness target for the honest witness.
The small and virtual chunks decompose the same 128-bit lookup address.
WitnessParams carries both required chunk-width divisibility conditions. -/
theorem honestWitness_instructionRaEqChunkProduct
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    instructionRaEqChunkProduct
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk address t
  let x := (HonestWitness.lookupIndex trace t.val).toNat
  let actual := HonestWitness.addressChunk params.virtualChunkBits chunk x
  let n := params.virtualChunkBits / params.chunkBits
  have hbits : n * params.chunkBits = params.virtualChunkBits :=
    Nat.div_mul_cancel params.chunkBits_dvd_virtual
  have hactual : actual < 2 ^ params.virtualChunkBits := by
    exact Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)
  have haddress : address.val < 2 ^ (n * params.chunkBits) := by
    simpa only [hbits] using address.isLt
  have hactual' : actual < 2 ^ (n * params.chunkBits) := by
    simpa only [hbits] using hactual
  have digit (offset : Fin n) :
      (instructionVirtualAddressDigit params address offset).val =
        HonestWitness.addressChunk params.chunkBits offset address.val := rfl
  have actual_digit (offset : Fin n) :
      HonestWitness.addressChunk params.chunkBits offset actual =
        HonestWitness.addressChunk params.chunkBits
          (instructionSmallChunkIndex params chunk offset) x := by
    exact virtual_digit_eq_small params chunk offset x
  change (if address.val = actual then (1 : F) else 0) =
    ∏ offset : Fin n,
      HonestWitness.addressChunkEntry params.chunkBits
        (instructionSmallChunkIndex params chunk offset) (some x)
          (instructionVirtualAddressDigit params address offset)
  by_cases heq : address.val = actual
  · simp only [heq, ↓reduceIte]
    symm
    apply Finset.prod_eq_one
    intro offset _
    dsimp [HonestWitness.addressChunkEntry]
    rw [if_pos]
    calc
      (instructionVirtualAddressDigit params address offset).val =
          HonestWitness.addressChunk params.chunkBits offset address.val := digit offset
      _ = HonestWitness.addressChunk params.chunkBits offset actual := by rw [heq]
      _ = HonestWitness.addressChunk params.chunkBits
          (instructionSmallChunkIndex params chunk offset) x := actual_digit offset
  · simp only [heq, ↓reduceIte]
    have hdiff : ∃ offset : Fin n,
        (instructionVirtualAddressDigit params address offset).val ≠
          HonestWitness.addressChunk params.chunkBits
            (instructionSmallChunkIndex params chunk offset) x := by
      by_contra hn
      have hd : ∀ offset : Fin n,
          HonestWitness.addressChunk params.chunkBits offset address.val =
            HonestWitness.addressChunk params.chunkBits offset actual := by
        intro offset
        have he : (instructionVirtualAddressDigit params address offset).val =
            HonestWitness.addressChunk params.chunkBits
              (instructionSmallChunkIndex params chunk offset) x := by
          by_contra hne
          exact hn ⟨offset, hne⟩
        simpa only [digit offset, ← actual_digit offset] using he
      exact heq (HonestWitness.addressChunk_injective params.chunkBits n
        address.val actual haddress hactual' hd)
    obtain ⟨offset, hne⟩ := hdiff
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ offset)
    dsimp [HonestWitness.addressChunkEntry]
    exact if_neg hne

end JoltConstraints
