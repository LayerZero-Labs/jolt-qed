import JoltConstraints.Soundness.Layer1.Addresses
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! `InstructionRa` is the lookup selector over `virtualChunkBits` bits. It is
not committed: the constraints rebuild it from the committed small chunks.
This use of "virtual" in the parameter name is unrelated to virtual instructions. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- The lookup chunk width `virtualChunkBits` is a whole number of small chunk
widths (`chunkBits_dvd_virtual`), so every small-digit tuple encodes one address,
with no unused high bits. -/
theorem instructionVirtualAddressDigit_bijective (params : WitnessParams) :
    Function.Bijective (instructionVirtualAddressDigit params) := by
  have width : params.virtualChunkBits / params.chunkBits * params.chunkBits =
      params.virtualChunkBits := Nat.div_mul_cancel params.chunkBits_dvd_virtual
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b same
    apply Fin.ext
    apply TraceWitness.addressChunk_injective params.chunkBits
      (params.virtualChunkBits / params.chunkBits) a.val b.val
    · simpa only [width] using a.isLt
    · simpa only [width] using b.isLt
    · intro offset
      exact congrArg Fin.val (congrFun same offset)
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm params.chunkBits, width]

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

/-- Every entry of a lookup selector is zero or one. -/
theorem instructionRa_zero_or_one
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.virtualInstructionChunks)
    (address : Fin (2 ^ params.virtualChunkBits)) (t : Fin params.traceLength) :
    witness.InstructionRa chunk address t = 0 ∨ witness.InstructionRa chunk address t = 1 := by
  rw [equations.instructionRaEqChunkProduct chunk address t]
  exact boolean_prod_zero_or_one _ (fun offset =>
    equations.instructionRaChunkBooleanity (instructionSmallChunkIndex params chunk offset)
      (instructionVirtualAddressDigit params address offset) t)

/-- A lookup selector selects at most one address. -/
theorem instructionRa_at_most_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.virtualInstructionChunks) (t : Fin params.traceLength)
    (a b : Fin (2 ^ params.virtualChunkBits))
    (selectedA : witness.InstructionRa chunk a t = 1)
    (selectedB : witness.InstructionRa chunk b t = 1) : a = b := by
  rw [equations.instructionRaEqChunkProduct chunk a t] at selectedA
  rw [equations.instructionRaEqChunkProduct chunk b t] at selectedB
  have digitsA := (boolean_prod_eq_one_iff _ (fun offset =>
    equations.instructionRaChunkBooleanity (instructionSmallChunkIndex params chunk offset)
      (instructionVirtualAddressDigit params a offset) t)).mp selectedA
  have digitsB := (boolean_prod_eq_one_iff _ (fun offset =>
    equations.instructionRaChunkBooleanity (instructionSmallChunkIndex params chunk offset)
      (instructionVirtualAddressDigit params b offset) t)).mp selectedB
  apply (instructionVirtualAddressDigit_bijective params).injective
  funext offset
  obtain ⟨chosen, _, unique⟩ := instruction_chunk_unique charAbove2pow127 context equations
    (instructionSmallChunkIndex params chunk offset) t
  exact (unique _ (digitsA offset)).trans (unique _ (digitsB offset)).symm

/-- At every cycle, each lookup selector selects exactly one address.
No characteristic bound on its entire address domain is required. -/
theorem instructionRa_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.virtualInstructionChunks) (t : Fin params.traceLength) :
    ∃! address, witness.InstructionRa chunk address t = 1 := by
  classical
  have each : ∀ offset : Fin (params.virtualChunkBits / params.chunkBits),
      ∃ entry, witness.InstructionRaChunk (instructionSmallChunkIndex params chunk offset) entry t = 1 :=
    fun offset => (instruction_chunk_unique charAbove2pow127 context equations
      (instructionSmallChunkIndex params chunk offset) t).exists
  choose digits selected using each
  obtain ⟨chosen, chosenDigits⟩ :=
    (instructionVirtualAddressDigit_bijective params).surjective digits
  have one : witness.InstructionRa chunk chosen t = 1 := by
    rw [equations.instructionRaEqChunkProduct chunk chosen t]
    apply Finset.prod_eq_one
    intro offset _
    rw [congrFun chosenDigits offset]
    exact selected offset
  exact ⟨chosen, one, fun address ha =>
    instructionRa_at_most_one charAbove2pow127 context equations chunk t address chosen ha one⟩

end JoltConstraints.Soundness
