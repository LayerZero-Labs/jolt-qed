import JoltConstraints.Soundness.Layer5.RamAgreement
import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.Soundness.Layer5.LookupWrite

/-! FENCE has no destination and no RAM effect. Its selected row therefore
preserves both register and ordinary-RAM agreement.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/fence.rs:20-26 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {live : Fin 128 → Prop} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  (instructionIs : row.instruction = .FENCE)

include charAbove2pow128 context equations selected rowIs instructionIs

/-- A selected FENCE executes without changing state, while both agreement
relations advance through the next or final RAM column.
The live set contains registers already matched to the witness and stays the same.
For example, FENCE preserves agreement on a live architectural register. -/
theorem fence_step {pre : SailJoltState}
    (registers : RegisterAgreementOn live witness t pre)
    (ram : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS pre ∧
    (∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn live witness ⟨t.val + 1, next⟩ pre ∧
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) pre) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal pre) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have noLoad : witness.OpFlags .Load t = 0 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag, Bool.false_eq_true] using
      opFlag_of_selected_bytecode bound context equations .Load t slot selected
  have noStore : witness.OpFlags .Store t = 0 := by
    simpa only [bytecodeCircuitFlag, rowIs, instructionIs, JoltMetadata.circuitFlag,
      JoltMetadata.opcodeFlag, Bool.false_eq_true] using
      opFlag_of_selected_bytecode bound context equations .Store t slot selected
  have memory := ram.noAccess bound context equations rfl noLoad noStore
  refine ⟨?_, ?_, memory.2⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl),
      instructionIs]
    simp only [execWithTapeAnswer, execInstr, pure, EStateM.pure]
  · intro next
    exact ⟨registers.noWrite bound context equations next slot selected rowIs
      (by rw [instructionIs]; rfl), memory.1 next⟩

end JoltConstraints.Soundness
