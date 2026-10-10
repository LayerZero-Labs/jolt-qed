import JoltConstraints.Soundness.Layer2.RegisterMap

/-! The two plain rotate tables are not selected by the currently modeled
source programs. Jolt's inline expansion helpers can emit them, but those
additional source instruction kinds are outside this SourceInstruction type.
The XOR-rotate table operations are covered separately in Rotate.lean. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

private theorem table_ne_plainRotate (instruction : JoltISA.Instr)
    (valid : ExpansionFacts.immShiftOk instruction = true) :
    JoltMetadata.lookupTable instruction ≠ some .VirtualROTR ∧
    JoltMetadata.lookupTable instruction ≠ some .VirtualROTRW := by
  cases instruction <;> simp_all [JoltMetadata.lookupTable, ExpansionFacts.immShiftOk]

/-- Expansion never emits the two immediate-rotate instructions, the only
instructions that select VirtualROTR or VirtualROTRW in this model. -/
theorem bytecodeTable_ne_plainRotate
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams}
    (context : ConstraintContext joltInstance privateInputs params) (address : Nat) :
    (bytecodeRow context.bytecode address).bind
        (fun row => JoltMetadata.lookupTable row.instruction) ≠ some .VirtualROTR ∧
    (bytecodeRow context.bytecode address).bind
        (fun row => JoltMetadata.lookupTable row.instruction) ≠ some .VirtualROTRW := by
  cases present : bytecodeRow context.bytecode address with
  | none => simp
  | some row =>
    exact table_ne_plainRotate row.instruction (bytecodeRow_rowOk context present).immShift

end JoltConstraints.Soundness
