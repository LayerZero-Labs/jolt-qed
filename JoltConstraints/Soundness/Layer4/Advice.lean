import JoltConstraints.Soundness.Layer4.Table
import JoltConstraints.Soundness.Layer4.RangeCheckEntry

/-! RangeCheck supplies a word even when advice has no input-determined address.
This proves word range only; correctness of internal runtime advice belongs to
Layer 5. Tape answers follow the separate execution specification in the plan. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- Every RangeCheck output encodes a 64-bit word, including advice rows whose
lookup address is otherwise unconstrained by the instruction inputs. -/
theorem lookupOutput_rangeCheck_word
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck) :
    ∃ value : BitVec 64, witness.LookupOutput t = (value.toNat : F) := by
  obtain ⟨address, lookupSelected, _⟩ :=
    instructionLookupRa_unique charAbove2pow127 context equations t
  refine ⟨(BitVec.ofFin address).setWidth 64, ?_⟩
  rw [lookupOutput_of_selected_bytecode charAbove2pow127 context equations
    t slot selected address lookupSelected, table]
  exact rangeCheck_entry (BitVec.ofFin address)

end JoltConstraints.Soundness
