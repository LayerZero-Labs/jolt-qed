import JoltConstraints.theorems.Soundness.Layer0.Bounds
import JoltConstraints.theorems.Soundness.Layer1.OneHot
import JoltConstraints.translation.Constraints.All

open LeanRV64D

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

end JoltConstraints.Soundness
