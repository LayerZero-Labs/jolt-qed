import JoltConstraints.Constraints.RamRaChunkHammingWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (62).
RamFits ensures every nonzero raw access remaps, so the raw-address activity
flag agrees with the presence of a selected RAM chunk entry. -/
theorem honestWitness_ramRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramRaChunkHammingWeight
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let instruction :=
      (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).expandedInstruction
    have fits := ramFits ⟨t.val, h⟩
    dsimp [WitnessParams.RamFits] at fits
    dsimp [ramRaChunkHammingWeight, JoltProgram.honestWitness,
      HonestWitness.RamRaChunk, HonestWitness.RamHammingWeight,
      HonestWitness.remappedRamAddress]
    simp only [dif_pos h]
    cases ha : HonestWitness.ramAccessAddress instruction row.preState with
    | none => simp [HonestWitness.addressChunkEntry]
    | some raw =>
      simp only [instruction, row, ha] at fits
      rcases fits with hzero | ⟨address, hremap, _⟩
      · subst raw
        simp [HonestWitness.remapRamAddress, HonestWitness.addressChunkEntry]
      · have hnonzero : raw ≠ 0 := by
          intro hz
          subst raw
          simp [HonestWitness.remapRamAddress] at hremap
        simp [hremap, HonestWitness.sum_addressChunkEntry_some]
        exact hnonzero
  · simp [JoltProgram.honestWitness,
      HonestWitness.RamRaChunk, HonestWitness.RamHammingWeight,
      HonestWitness.remappedRamAddress, HonestWitness.addressChunkEntry, h]

end JoltConstraints
