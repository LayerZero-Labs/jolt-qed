import JoltConstraints.theorems.Soundness.Layer1.Chunks
import JoltConstraints.theorems.Soundness.Layer1.Products
import JoltConstraints.translation.witness_helpers.address_chunk

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

private theorem chunk_capacity_ge_width (width bits : Nat) (positive : 0 < bits) :
    width ≤ ((width + bits - 1) / bits) * bits := by
  have remainder := Nat.mod_lt (width + bits - 1) positive
  have quotient : (width + bits - 1) % bits +
      (width + bits - 1) / bits * bits = width + bits - 1 := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (width + bits - 1) bits
  omega

/-- In-domain addresses are equal if all their chunks agree. The number of
chunks is rounded up, so this also covers a partially used first chunk and
the zero-bit address domain, which has one address and no chunks. -/
theorem address_eq_of_chunks_eq (width bits : Nat) (positive : 0 < bits)
    (a b : Fin (2 ^ width))
    (digits : ∀ chunk : Fin ((width + bits - 1) / bits),
      TraceWitness.addressChunk bits chunk a.val =
        TraceWitness.addressChunk bits chunk b.val) : a = b := by
  have capacity := chunk_capacity_ge_width width bits positive
  apply Fin.ext
  exact TraceWitness.addressChunk_injective bits ((width + bits - 1) / bits)
    a.val b.val
    (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) capacity))
    (b.isLt.trans_le (Nat.pow_le_pow_right (by decide) capacity)) digits

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

/-- Every full bytecode selector entry is zero or one. -/
theorem bytecodeRa_zero_or_one
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (address : Fin (2 ^ params.logBytecodeK)) (t : Fin params.traceLength) :
    bytecodeRa witness address t = 0 ∨ bytecodeRa witness address t = 1 :=
  boolean_prod_zero_or_one _ (fun chunk =>
    equations.bytecodeRaChunkBooleanity chunk (bytecodeAddressChunk params address chunk) t)

/-- Two bytecode addresses selected at the same cycle must be equal.
This does not assert that any address is selected. -/
theorem bytecodeRa_at_most_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (a b : Fin (2 ^ params.logBytecodeK))
    (selectedA : bytecodeRa witness a t = 1)
    (selectedB : bytecodeRa witness b t = 1) : a = b := by
  have chunksA := (boolean_prod_eq_one_iff _ (fun chunk =>
    equations.bytecodeRaChunkBooleanity chunk (bytecodeAddressChunk params a chunk) t)).mp selectedA
  have chunksB := (boolean_prod_eq_one_iff _ (fun chunk =>
    equations.bytecodeRaChunkBooleanity chunk (bytecodeAddressChunk params b chunk) t)).mp selectedB
  apply address_eq_of_chunks_eq params.logBytecodeK params.chunkBits params.chunkBits_pos a b
  intro chunk
  obtain ⟨chosen, _, unique⟩ := bytecode_chunk_unique charAbove2pow127 context equations chunk t
  exact congrArg Fin.val ((unique _ (chunksA chunk)).trans (unique _ (chunksB chunk)).symm)

/-- The full bytecode selector is either zero throughout its domain or selects
exactly one address. Ruling out the zero alternative needs further constraints. -/
theorem bytecodeRa_zero_or_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    (∀ address, bytecodeRa witness address t = 0) ∨
      ∃! address, bytecodeRa witness address t = 1 := by
  apply zero_or_existsUnique_of_boolean (fun address => bytecodeRa witness address t)
  · intro address
    rcases bytecodeRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  · exact bytecodeRa_at_most_one charAbove2pow127 context equations t

/-- Once a bytecode address is selected, every read of a fixed bytecode column
returns that address's entry. The selected address hypothesis is discharged by
`bytecodeRa_unique` below. -/
theorem bytecode_read_of_selected (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (value : Fin (2 ^ params.logBytecodeK) → F)
    (chosen : Fin (2 ^ params.logBytecodeK)) (one : bytecodeRa witness chosen t = 1) :
    (∑ address, value address * bytecodeRa witness address t) = value chosen := by
  apply read_eq_selected (fun address => bytecodeRa witness address t) value
  · intro address
    rcases bytecodeRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  · exact one
  · exact fun address selected =>
      bytecodeRa_at_most_one charAbove2pow127 context equations t address chosen selected one

/-- Every full RAM selector entry is zero or one. This also holds when there
are no RAM chunks: the product constraint then makes the entry one. -/
theorem ramRa_zero_or_one
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (address : Fin params.ramSize) (t : Fin params.traceLength) :
    witness.RamRa address t = 0 ∨ witness.RamRa address t = 1 := by
  rw [equations.ramRaEqChunkProduct address t]
  exact boolean_prod_zero_or_one _ (fun chunk =>
    equations.ramRaChunkBooleanity chunk (ramAddressChunk params address chunk) t)

/-- The authenticated memory flags count either zero or one access.
For example, an SD row contributes one and a halt contributes zero.
This does not impose a Hamming weight on individual RAM chunks. -/
theorem ram_access_count_zero_or_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    witness.OpFlags .Load t + witness.OpFlags .Store t = 0 ∨
      witness.OpFlags .Load t + witness.OpFlags .Store t = 1 := by
  rw [equations.opFlagsEqBytecodeRead .Load t, equations.opFlagsEqBytecodeRead .Store t]
  rcases bytecodeRa_zero_or_unique charAbove2pow127 context equations t with zero | selected
  · simp [zero]
  · obtain ⟨chosen, one, _⟩ := selected
    rw [bytecode_read_of_selected charAbove2pow127 context equations t _ chosen one,
      bytecode_read_of_selected charAbove2pow127 context equations t _ chosen one]
    cases hrow : bytecodeRow context.bytecode chosen.val with
    | none => simp [bytecodeCircuitFlag, hrow]
    | some row =>
      by_cases load : JoltMetadata.opcodeFlag row.instruction .Load = true
      · have store := JoltMetadata.opcodeFlag_load_store_disjoint row.instruction load
        simp [bytecodeCircuitFlag, hrow, JoltMetadata.circuitFlag, load, store]
      · have noLoad : JoltMetadata.opcodeFlag row.instruction .Load = false :=
          Bool.eq_false_iff.mpr load
        cases store : JoltMetadata.opcodeFlag row.instruction .Store <;>
          simp [bytecodeCircuitFlag, hrow, JoltMetadata.circuitFlag, noLoad, store]

/-- The full RAM selector is zero throughout its domain or selects one address.
For example, a store selects exactly one word because its access count is one.
Booleanity and the global selector sum replace the old chunk Hamming checks. -/
theorem ramRa_zero_or_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    (∀ address, witness.RamRa address t = 0) ∨
      ∃! address, witness.RamRa address t = 1 := by
  have small : Fintype.card (Fin params.ramSize) < ringChar F := by
    rw [Fintype.card_fin, WitnessParams.ramSize]
    exact lt_of_le_of_lt
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by have h := params.logRamK_lt_usizeBits; omega))
      charAbove2pow127
  have boolean : ∀ address, witness.RamRa address t * (witness.RamRa address t - 1) = 0 := by
    intro address
    rcases ramRa_zero_or_one context equations address t with zero | one <;> simp [*]
  rcases ram_access_count_zero_or_one charAbove2pow127 context equations t with zero | one
  · exact Or.inl (all_zero_of_boolean_sum_zero _ small boolean
      ((equations.ramAccessCount t).symm.trans zero))
  · exact Or.inr (existsUnique_of_boolean_sum_one _ small boolean
      ((equations.ramAccessCount t).symm.trans one))

/-- Two selected RAM addresses coincide, including when the RAM domain has no chunks.
For example, a store cannot select both its own word and a second word. -/
theorem ramRa_at_most_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (a b : Fin params.ramSize)
    (selectedA : witness.RamRa a t = 1) (selectedB : witness.RamRa b t = 1) : a = b := by
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | selected
  · exact False.elim (zero_ne_one ((zero a).symm.trans selectedA))
  · obtain ⟨chosen, _, unique⟩ := selected
    exact (unique a selectedA).trans (unique b selectedB).symm

end JoltConstraints.Soundness
