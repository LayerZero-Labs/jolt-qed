import JoltConstraints.Soundness.Layer1.Instruction

/-! The lookup equations read a full 128-bit address using the product of
the `InstructionRa` lookup selectors. Reconstruct that address from their unique
choices, then collapse the lookup-output and operand sums. These are field
equalities; identifying the active table and interpreting its operands belong
to Layer 4. Instruction execution belongs to Layer 5b.

`InstructionRafFlag = 1` uses the whole 128-bit address as the right operand
and zero as the left operand. At flag 0, the address interleaves the operands:
odd bit positions hold the left operand and even positions hold the right,
counting from bit 0 at the least significant end. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- Chunks of `virtualChunkBits` bits cover all 128 lookup-address bits exactly,
so every tuple of chunk addresses corresponds to one full lookup address. -/
theorem instructionLookupChunk_bijective (params : WitnessParams) :
    Function.Bijective (instructionLookupChunk params) := by
  have width : params.virtualInstructionChunks * params.virtualChunkBits = 128 :=
    Nat.div_mul_cancel params.virtualChunkBits_dvd_lookup
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b same
    apply Fin.ext
    apply TraceWitness.addressChunk_injective params.virtualChunkBits
      params.virtualInstructionChunks a.val b.val
    · simpa only [width] using a.isLt
    · simpa only [width] using b.isLt
    · intro chunk
      exact congrArg Fin.val (congrFun same chunk)
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm params.virtualChunkBits, width]

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

private theorem instructionRa_boolean
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.virtualInstructionChunks)
    (address : Fin (2 ^ params.virtualChunkBits)) (t : Fin params.traceLength) :
    witness.InstructionRa chunk address t * (witness.InstructionRa chunk address t - 1) = 0 := by
  rcases instructionRa_zero_or_one context equations chunk address t with zero | one
  · simp [zero]
  · simp [one]

/-- Every entry of the full 128-bit lookup selector is zero or one. -/
theorem instructionLookupRa_zero_or_one
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (address : Fin (2 ^ 128)) (t : Fin params.traceLength) :
    instructionLookupRa witness address t = 0 ∨ instructionLookupRa witness address t = 1 :=
  boolean_prod_zero_or_one _ (fun chunk =>
    instructionRa_boolean context equations chunk (instructionLookupChunk params address chunk) t)

/-- The full lookup selector selects at most one 128-bit address. -/
theorem instructionLookupRa_at_most_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (a b : Fin (2 ^ 128))
    (selectedA : instructionLookupRa witness a t = 1)
    (selectedB : instructionLookupRa witness b t = 1) : a = b := by
  have chunksA := (boolean_prod_eq_one_iff _ (fun chunk =>
    instructionRa_boolean context equations chunk (instructionLookupChunk params a chunk) t)).mp selectedA
  have chunksB := (boolean_prod_eq_one_iff _ (fun chunk =>
    instructionRa_boolean context equations chunk (instructionLookupChunk params b chunk) t)).mp selectedB
  apply (instructionLookupChunk_bijective params).injective
  funext chunk
  exact instructionRa_at_most_one charAbove2pow127 context equations chunk t _ _
    (chunksA chunk) (chunksB chunk)

/-- Every cycle selects exactly one full lookup address. Selection follows
from the lookup chunks, without requiring `2^128 < ringChar F`. -/
theorem instructionLookupRa_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) : ∃! address, instructionLookupRa witness address t = 1 := by
  classical
  have each : ∀ chunk : Fin params.virtualInstructionChunks,
      ∃ address, witness.InstructionRa chunk address t = 1 :=
    fun chunk => (instructionRa_unique charAbove2pow127 context equations chunk t).exists
  choose chunks selected using each
  obtain ⟨chosen, chosenChunks⟩ := (instructionLookupChunk_bijective params).surjective chunks
  have one : instructionLookupRa witness chosen t = 1 := by
    apply Finset.prod_eq_one
    intro chunk _
    rw [congrFun chosenChunks chunk]
    exact selected chunk
  exact ⟨chosen, one, fun address ha =>
    instructionLookupRa_at_most_one charAbove2pow127 context equations t address chosen ha one⟩

/-- A read weighted by the full lookup selector returns the selected entry.
`instructionLookupRa_unique` supplies the selected address at every cycle. -/
theorem instruction_read_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (value : Fin (2 ^ 128) → F)
    (chosen : Fin (2 ^ 128)) (selected : instructionLookupRa witness chosen t = 1) :
    (∑ address, instructionLookupRa witness address t * value address) = value chosen := by
  have boolean : ∀ address, instructionLookupRa witness address t *
      (instructionLookupRa witness address t - 1) = 0 := by
    intro address
    rcases instructionLookupRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  simpa only [mul_comm] using
    read_eq_selected (fun address => instructionLookupRa witness address t) value boolean
      chosen selected (fun address ha =>
        instructionLookupRa_at_most_one charAbove2pow127 context equations t address chosen ha selected)

/-- The lookup output uses the table entries at the selected full address.
Identifying the active table and proving its operation are Layer 4 obligations. -/
theorem lookupOutput_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ 128))
    (selected : instructionLookupRa witness chosen t = 1) :
    witness.LookupOutput t =
      ∑ table, witness.LookupTableFlag table t * lookupTableEntry table chosen := by
  rw [equations.lookupOutputEqInstructionReadRaf t]
  exact instruction_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- At `InstructionRafFlag = 0`, the left operand packs the selected address's
odd bit positions, counted from the least significant bit. At flag 1 it is zero. -/
theorem leftLookupOperand_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ 128))
    (selected : instructionLookupRa witness chosen t = 1) :
    witness.LeftLookupOperand t =
      (1 - witness.InstructionRafFlag t) * lookupAddressLeft chosen := by
  rw [equations.leftLookupOperandEqInstructionRaf t]
  simpa only [mul_assoc] using
    instruction_read_of_selected charAbove2pow127 context equations t
      (fun address => (1 - witness.InstructionRafFlag t) * lookupAddressLeft address)
      chosen selected

/-- At `InstructionRafFlag = 0`, the right operand packs the selected address's
even bit positions, counted from the least significant bit. At flag 1 it is the
whole 128-bit address cast into the field; injectivity of that cast is a separate
Layer 4 obligation. -/
theorem rightLookupOperand_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ 128))
    (selected : instructionLookupRa witness chosen t = 1) :
    witness.RightLookupOperand t =
      (1 - witness.InstructionRafFlag t) * lookupAddressRight chosen +
        witness.InstructionRafFlag t * (chosen.val : F) := by
  rw [equations.rightLookupOperandEqInstructionRaf t]
  exact instruction_read_of_selected charAbove2pow127 context equations t _ chosen selected

end JoltConstraints.Soundness
