import JoltConstraints.Soundness.Layer1.BytecodeReads
import JoltConstraints.Soundness.Layer1.InstructionReads

/-! Identify the lookup table from the bytecode slot selected at a cycle.
An instruction with no table, or a padding slot, has lookup output zero.
These facts concern an arbitrary satisfying witness, without an execution trace. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- The selected bytecode slot determines the table; the selected lookup
address determines its entry. Absent tables contribute zero. -/
theorem lookupOutput_of_selected_bytecode (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (bytecodeSelected : bytecodeRa witness slot t = 1)
    (address : Fin (2 ^ 128)) (lookupSelected : instructionLookupRa witness address t = 1) :
    witness.LookupOutput t =
      match (bytecodeRow context.bytecode slot.val).bind
          (fun row => JoltMetadata.lookupTable row.instruction) with
      | some table => lookupTableEntry table address
      | none => 0 := by
  rw [lookupOutput_of_selected charAbove2pow127 context equations t address lookupSelected]
  simp_rw [lookupTableFlag_of_selected_bytecode charAbove2pow127 context equations
    _ t slot bytecodeSelected]
  cases present : bytecodeRow context.bytecode slot.val with
  | none => simp [bytecodeLookupTableFlag, present]
  | some row =>
    cases table : JoltMetadata.lookupTable row.instruction with
    | none => simp [bytecodeLookupTableFlag, present, JoltMetadata.lookupTableFlag, table]
    | some kind => simp [bytecodeLookupTableFlag, present, JoltMetadata.lookupTableFlag, table]

/-- Addition, subtraction and multiplication use the whole lookup address as
the right operand. The RAF flag follows from the same selected bytecode row. -/
theorem instructionRafFlag_one_of_arithmetic (t : Fin params.traceLength)
    (active : witness.OpFlags .AddOperands t = 1 ∨
      witness.OpFlags .SubtractOperands t = 1 ∨ witness.OpFlags .MultiplyOperands t = 1) :
    witness.InstructionRafFlag t = 1 := by
  obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  rw [instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations t slot selected]
  simp_rw [opFlag_of_selected_bytecode charAbove2pow127 context equations _ t slot selected] at active
  cases present : bytecodeRow context.bytecode slot.val with
  | none => simp [bytecodeCircuitFlag, present] at active
  | some row =>
    simp only [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag] at active
    simp only [bytecodeRafFlag, present, JoltMetadata.instructionRafFlag]
    rcases active with add | sub | mul
    · split at add <;> simp_all
    · split at sub <;> simp_all
    · split at mul <;> simp_all

end JoltConstraints.Soundness
