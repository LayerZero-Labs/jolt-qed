import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

private theorem bytecodeChunks_cover (params : WitnessParams) :
    params.logBytecodeK ≤ params.bytecodeChunks * params.chunkBits := by
  dsimp [WitnessParams.bytecodeChunks]
  have hrem := Nat.mod_lt (params.logBytecodeK + params.chunkBits - 1)
    params.chunkBits_pos
  have hdiv := Nat.mod_add_div
    (params.logBytecodeK + params.chunkBits - 1) params.chunkBits
  have hdiv' :
      (params.logBytecodeK + params.chunkBits - 1) % params.chunkBits +
      (params.logBytecodeK + params.chunkBits - 1) / params.chunkBits *
        params.chunkBits = params.logBytecodeK + params.chunkBits - 1 := by
    simpa [Nat.mul_comm] using hdiv
  omega

private theorem bytecodePc_lt (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (t : Fin params.traceLength) :
    HonestWitness.bytecodePc trace t.val < 2 ^ params.logBytecodeK := by
  have hrows := bytecodeDomain.rowsFit
  unfold HonestWitness.bytecodePc
  split_ifs with h
  · have hindex := (getElem trace.rows t.val h).rowIndex.isLt
    omega
  · exact pow_pos (by decide : 0 < (2 : Nat)) _

private theorem bytecodeAddress_lt_chunks (params : WitnessParams)
    (address : Fin (2 ^ params.logBytecodeK)) :
    address.val < 2 ^ (params.bytecodeChunks * params.chunkBits) := by
  exact address.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (bytecodeChunks_cover params))

theorem bytecodeRa_honest {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (address : Fin (2 ^ params.logBytecodeK)) (t : Fin params.traceLength) :
    bytecodeRa (JoltProgram.honestWitness (F := F) params trace ramFits
      traceFits bytecodeDomain) address t =
      if address.val = HonestWitness.bytecodePc trace t.val then 1 else 0 := by
  unfold bytecodeRa
  by_cases heq : address.val = HonestWitness.bytecodePc trace t.val
  · simp only [heq, ↓reduceIte]
    apply Finset.prod_eq_one
    intro chunk _
    dsimp [JoltProgram.honestWitness, HonestWitness.BytecodeRaChunk,
      HonestWitness.addressChunkEntry, bytecodeAddressChunk,
      HonestWitness.addressChunk]
    simp [heq]
  · simp only [heq, ↓reduceIte]
    have hdiff : ∃ chunk : Fin params.bytecodeChunks,
        HonestWitness.addressChunk params.chunkBits chunk address.val ≠
          HonestWitness.addressChunk params.chunkBits chunk
            (HonestWitness.bytecodePc trace t.val) := by
      by_contra hn
      have hd : ∀ chunk : Fin params.bytecodeChunks,
          HonestWitness.addressChunk params.chunkBits chunk address.val =
            HonestWitness.addressChunk params.chunkBits chunk
              (HonestWitness.bytecodePc trace t.val) := by
        intro chunk
        by_contra hneq
        exact hn ⟨chunk, hneq⟩
      exact heq (HonestWitness.addressChunk_injective params.chunkBits
        params.bytecodeChunks address.val (HonestWitness.bytecodePc trace t.val)
        (bytecodeAddress_lt_chunks params address)
        (lt_of_lt_of_le (bytecodePc_lt params trace bytecodeDomain t)
          (Nat.pow_le_pow_right (by decide) (bytecodeChunks_cover params))) hd)
    obtain ⟨chunk, hneq⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ chunk)
    dsimp [JoltProgram.honestWitness, HonestWitness.BytecodeRaChunk,
      HonestWitness.addressChunkEntry, bytecodeAddressChunk,
      HonestWitness.addressChunk]
    change address.val / 2 ^ ((params.bytecodeChunks - 1 - chunk.val) * params.chunkBits) %
        2 ^ params.chunkBits ≠
      HonestWitness.bytecodePc trace t.val /
        2 ^ ((params.bytecodeChunks - 1 - chunk.val) * params.chunkBits) %
          2 ^ params.chunkBits at hneq
    simp [hneq]

/-- Reading any fixed bytecode column with the honest chunk selectors returns
the column value at this cycle's bytecode slot, including slot zero on padding. -/
theorem bytecodeRead_honest {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (value : Nat → F) (t : Fin params.traceLength) :
    (∑ address : Fin (2 ^ params.logBytecodeK),
      value address.val * bytecodeRa
        (JoltProgram.honestWitness (F := F) params trace ramFits traceFits
          bytecodeDomain) address t) =
      value (HonestWitness.bytecodePc trace t.val) := by
  let selected : Fin (2 ^ params.logBytecodeK) :=
    ⟨HonestWitness.bytecodePc trace t.val, bytecodePc_lt params trace bytecodeDomain t⟩
  have hsel : ∀ address : Fin (2 ^ params.logBytecodeK),
      (address.val = HonestWitness.bytecodePc trace t.val) ↔ address = selected := by
    intro address
    simp [selected, Fin.ext_iff]
  simp_rw [bytecodeRa_honest params trace ramFits traceFits bytecodeDomain]
  simp_rw [hsel]
  simp [Finset.sum_ite_eq', selected]

end JoltConstraints
