import JoltConstraints.Soundness.Layer1.Chunks
import JoltConstraints.Soundness.Layer1.Products
import JoltConstraints.witness_helpers.address_chunk

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

/-- Two RAM addresses selected at the same cycle must be equal, without
assuming a positive number of RAM chunks or a RAM weight of one. -/
theorem ramRa_at_most_one (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (a b : Fin params.ramSize)
    (selectedA : witness.RamRa a t = 1) (selectedB : witness.RamRa b t = 1) : a = b := by
  rw [equations.ramRaEqChunkProduct a t] at selectedA
  rw [equations.ramRaEqChunkProduct b t] at selectedB
  have chunksA := (boolean_prod_eq_one_iff _ (fun chunk =>
    equations.ramRaChunkBooleanity chunk (ramAddressChunk params a chunk) t)).mp selectedA
  have chunksB := (boolean_prod_eq_one_iff _ (fun chunk =>
    equations.ramRaChunkBooleanity chunk (ramAddressChunk params b chunk) t)).mp selectedB
  apply address_eq_of_chunks_eq params.logRamK params.chunkBits params.chunkBits_pos a b
  intro chunk
  rcases ram_weight_zero_or_one context equations t with zero | one
  · have unselected := ram_chunk_all_zero charAbove2pow127 context equations t zero chunk
      (ramAddressChunk params a chunk)
    exact False.elim (zero_ne_one (unselected.symm.trans (chunksA chunk)))
  · obtain ⟨chosen, _, unique⟩ := ram_chunk_unique charAbove2pow127 context equations t one chunk
    exact congrArg Fin.val ((unique _ (chunksA chunk)).trans (unique _ (chunksB chunk)).symm)

/-- The full RAM selector is either zero throughout its domain or selects
exactly one address. `Ram.lean` identifies the zero alternative with `RamAddress = 0`. -/
theorem ramRa_zero_or_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    (∀ address, witness.RamRa address t = 0) ∨
      ∃! address, witness.RamRa address t = 1 := by
  apply zero_or_existsUnique_of_boolean (fun address => witness.RamRa address t)
  · intro address
    rcases ramRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · simp [one]
  · exact ramRa_at_most_one charAbove2pow127 context equations t

end JoltConstraints.Soundness
