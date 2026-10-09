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
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramRaChunkHammingWeight
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let instruction :=
      (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
    have fits := ramFits ⟨t.val, h⟩
    dsimp [WitnessParams.RamFits] at fits
    dsimp [ramRaChunkHammingWeight, HonestTrace.honestWitness,
      TraceWitness.RamRaChunk, TraceWitness.RamHammingWeight,
      TraceWitness.remappedRamAddress]
    simp only [dif_pos h]
    cases ha : TraceWitness.ramAccessAddress instruction row.preState with
    | none => simp [TraceWitness.addressChunkEntry]
    | some raw =>
      simp only [instruction, row, ha] at fits
      rcases fits with hzero | ⟨address, hremap, _⟩
      · subst raw
        simp [TraceWitness.remapRamAddress, TraceWitness.addressChunkEntry]
      · have hnonzero : raw ≠ 0 := by
          intro hz
          subst raw
          simp [TraceWitness.remapRamAddress] at hremap
        simp [hremap, TraceWitness.sum_addressChunkEntry_some]
        exact hnonzero
  · simp [HonestTrace.honestWitness,
      TraceWitness.RamRaChunk, TraceWitness.RamHammingWeight,
      TraceWitness.remappedRamAddress, TraceWitness.addressChunkEntry, h]

end JoltConstraints
