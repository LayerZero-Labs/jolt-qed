import JoltConstraints.Constraints.LookupOutputEqInstructionReadRaf

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

theorem instructionLookupRa_honest {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (address : Fin (2 ^ 128)) (t : Fin params.traceLength) :
    instructionLookupRa
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain)
      address t =
      if address.val = (HonestWitness.lookupIndex trace t.val).toNat then 1 else 0 := by
  have hcover : params.virtualInstructionChunks * params.virtualChunkBits = 128 := by
    exact Nat.div_mul_cancel params.virtualChunkBits_dvd_lookup
  have ha : address.val < 2 ^ (params.virtualInstructionChunks * params.virtualChunkBits) := by
    simpa only [hcover] using address.isLt
  have hb : (HonestWitness.lookupIndex trace t.val).toNat <
      2 ^ (params.virtualInstructionChunks * params.virtualChunkBits) := by
    simpa only [hcover] using (HonestWitness.lookupIndex trace t.val).isLt
  unfold instructionLookupRa
  by_cases heq : address.val = (HonestWitness.lookupIndex trace t.val).toNat
  · simp only [heq, ↓reduceIte]
    apply Finset.prod_eq_one
    intro chunk _
    dsimp [JoltProgram.honestWitness, HonestWitness.InstructionRa,
      HonestWitness.addressChunkEntry, instructionLookupChunk,
      HonestWitness.addressChunk]
    simp [heq]
  · simp only [heq, ↓reduceIte]
    have hdiff : ∃ chunk : Fin params.virtualInstructionChunks,
        HonestWitness.addressChunk params.virtualChunkBits chunk address.val ≠
          HonestWitness.addressChunk params.virtualChunkBits chunk
            (HonestWitness.lookupIndex trace t.val).toNat := by
      by_contra hn
      have hd : ∀ chunk : Fin params.virtualInstructionChunks,
          HonestWitness.addressChunk params.virtualChunkBits chunk address.val =
            HonestWitness.addressChunk params.virtualChunkBits chunk
              (HonestWitness.lookupIndex trace t.val).toNat := by
        intro chunk
        by_contra hneq
        exact hn ⟨chunk, hneq⟩
      exact heq (HonestWitness.addressChunk_injective params.virtualChunkBits
        params.virtualInstructionChunks address.val
        (HonestWitness.lookupIndex trace t.val).toNat ha hb hd)
    obtain ⟨chunk, hneq⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ chunk)
    dsimp [JoltProgram.honestWitness, HonestWitness.InstructionRa,
      HonestWitness.addressChunkEntry, instructionLookupChunk,
      HonestWitness.addressChunk]
    change address.val /
      2 ^ ((params.virtualInstructionChunks - 1 - chunk.val) * params.virtualChunkBits) %
        2 ^ params.virtualChunkBits ≠
      (HonestWitness.lookupIndex trace t.val).toNat /
        2 ^ ((params.virtualInstructionChunks - 1 - chunk.val) * params.virtualChunkBits) %
          2 ^ params.virtualChunkBits at hneq
    exact if_neg hneq

/-- A fixed instruction-read column evaluates at the honest lookup index. -/
theorem instructionRead_honest {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (value : Fin (2 ^ 128) → F) (t : Fin params.traceLength) :
    (∑ address : Fin (2 ^ 128),
      instructionLookupRa
        (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain)
        address t * value address) =
      value ⟨(HonestWitness.lookupIndex trace t.val).toNat,
        (HonestWitness.lookupIndex trace t.val).isLt⟩ := by
  let selected : Fin (2 ^ 128) :=
    ⟨(HonestWitness.lookupIndex trace t.val).toNat,
      (HonestWitness.lookupIndex trace t.val).isLt⟩
  have hsel : ∀ address : Fin (2 ^ 128),
      (address.val = (HonestWitness.lookupIndex trace t.val).toNat) ↔
        address = selected := by
    intro address
    simp [selected, Fin.ext_iff]
  simp_rw [instructionLookupRa_honest params trace ramFits traceFits bytecodeDomain]
  simp_rw [hsel]
  simp [Finset.sum_ite_eq', selected]

end JoltConstraints
