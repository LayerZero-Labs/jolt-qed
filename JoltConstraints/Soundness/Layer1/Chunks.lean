import JoltConstraints.Soundness.Layer0.Bounds
import JoltConstraints.Soundness.Layer1.OneHot
import JoltConstraints.Constraints.All

/-! An entry is a chunk's digit value, in `Fin (2 ^ params.chunkBits)`. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

/-- Each bytecode one-hot chunk selects one entry, at every witness cycle. -/
theorem bytecode_chunk_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.bytecodeChunks) (t : Fin params.traceLength) :
    ∃! entry, witness.BytecodeRaChunk chunk entry t = 1 := by
  apply existsUnique_of_boolean_sum_one (fun entry => witness.BytecodeRaChunk chunk entry t)
  · exact context.chunk_card_lt_char charAbove2pow127
  · exact fun entry => equations.bytecodeRaChunkBooleanity chunk entry t
  · exact equations.bytecodeRaChunkHammingWeight chunk t

/-- Each instruction-lookup one-hot chunk selects one entry, at every witness cycle. -/
theorem instruction_chunk_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (chunk : Fin params.instructionChunks) (t : Fin params.traceLength) :
    ∃! entry, witness.InstructionRaChunk chunk entry t = 1 := by
  apply existsUnique_of_boolean_sum_one (fun entry => witness.InstructionRaChunk chunk entry t)
  · exact context.chunk_card_lt_char charAbove2pow127
  · exact fun entry => equations.instructionRaChunkBooleanity chunk entry t
  · exact equations.instructionRaChunkHammingWeight chunk t

/-- The RAM weight shared by all RAM chunks decodes to zero or one. -/
theorem ram_weight_zero_or_one
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) :
    witness.RamHammingWeight t = 0 ∨ witness.RamHammingWeight t = 1 :=
  eq_zero_or_one_of_boolean (equations.ramHammingWeightBooleanity t)

/-- A zero RAM weight forces every entry of every RAM chunk to be zero. -/
theorem ram_chunk_all_zero (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (zero : witness.RamHammingWeight t = 0)
    (chunk : Fin params.ramChunks) :
    ∀ entry, witness.RamRaChunk chunk entry t = 0 := by
  apply all_zero_of_boolean_sum_zero (fun entry => witness.RamRaChunk chunk entry t)
  · exact context.chunk_card_lt_char charAbove2pow127
  · exact fun entry => equations.ramRaChunkBooleanity chunk entry t
  · exact (equations.ramRaChunkHammingWeight chunk t).trans zero

/-- A RAM weight of one forces each RAM chunk to select exactly one entry. -/
theorem ram_chunk_unique (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (one : witness.RamHammingWeight t = 1)
    (chunk : Fin params.ramChunks) :
    ∃! entry, witness.RamRaChunk chunk entry t = 1 := by
  apply existsUnique_of_boolean_sum_one (fun entry => witness.RamRaChunk chunk entry t)
  · exact context.chunk_card_lt_char charAbove2pow127
  · exact fun entry => equations.ramRaChunkBooleanity chunk entry t
  · exact (equations.ramRaChunkHammingWeight chunk t).trans one

end JoltConstraints.Soundness
