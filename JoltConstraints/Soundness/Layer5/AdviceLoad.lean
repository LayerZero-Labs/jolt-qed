import JoltConstraints.Soundness.Layer5.Advice

/-! Selected tape loads use the witness's range-check word and advance only
the advice cursor before writing a canonical destination.
See jolt/tracer/src/instruction/virtual_advice_load.rs
(`VirtualAdviceLoad::exec`) at 5def437f. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- An expanded bytecode tape load has byte count 1, 2, 4 or 8.
This lifts the shared advice checker through materialization and program
expansion; for example, AdviceLH's first row has byte count 2.
See jolt/crates/jolt-program/src/expand/memory/shared.rs
(`expand_advice_load`) at 5def437f. -/
theorem expanded_adviceLoad_width (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    {address : Nat} {row : JoltInstructionRow} (present : bytecodeRow bytecode address = some row)
    {destination : Dst} {width : BitVec 64}
    (instructionIs : row.instruction = .VirtualAdviceLoad destination width) :
    width.toNat = 1 ∨ width.toNat = 2 ∨ width.toNat = 4 ∨ width.toNat = 8 := by
  have member : row ∈ bytecode.toList := by
    cases address with
    | zero => simp [bytecodeRow] at present
    | succ index =>
      obtain ⟨bound, rfl⟩ := Array.getElem?_eq_some_iff.mp present
      exact Array.getElem_mem_toList bound
  obtain ⟨source, _, rows, sourceExpanded, inRows⟩ :=
    expand_program_source_of_row image bytecode expanded row member
  have checked := ExpansionFacts.expand_instruction_property
    (fun instructions => ExpansionFacts.advicePairsOk instructions = true)
    ExpansionFacts.nativeRowOk_advicePairsOk ExpansionFacts.sequenceOk_advicePairsOk
    source rows sourceExpanded
  apply ExpansionFacts.advicePairsOk_width _ checked
  exact List.mem_map.mpr ⟨row, inRows, instructionIs⟩

/-- A selected VirtualAdviceLoad writes the witness's 64-bit word to any
canonical destination and advances the tape cursor by the checked byte count.
The old live registers and the destination agree at the next witness cycle;
no old value is required for a destination that was not live.
For example, AdviceLD x1 writes a full word and advances the cursor by eight.
See jolt/crates/jolt-lookup-tables/src/instructions/virt/advice_load.rs
(`LookupQuery::to_lookup_output`) and jolt/tracer/src/instruction/virtual_advice_load.rs
(`VirtualAdviceLoad::exec`) at 5def437f. -/
theorem adviceLoad_register_step {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {destination : Dst} {width : BitVec 64}
    (instructionIs : row.instruction = .VirtualAdviceLoad destination width)
    {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (advice : row.instruction.RuntimeAdvice) :
    ∃ value : BitVec 64, witness.RdWriteValue t = (value.toNat : F) ∧
      let post := afterWriteDst destination value
        { pre with adviceTape := { pre.adviceTape with
            readPosition := pre.adviceTape.readPosition + width.toNat } }
      execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) value pre =
        .ok RETIRE_SUCCESS post ∧
      ∀ next : t.val + 1 < params.traceLength,
        RegisterAgreementOn
          (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
          witness ⟨t.val + 1, next⟩ post := by
  obtain ⟨value, encoded⟩ := rangeCheck_write_value (two_pow_127_lt_char charAbove2pow128)
    context equations selected rowIs (by rw [instructionIs]; rfl) (by rw [instructionIs]; rfl)
  have valid := expanded_adviceLoad_width _ _ context.expands rowIs instructionIs
  have destinationIs : row.instruction.destination? = some destination := by rw [instructionIs]; rfl
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destinationIs
  let prepared := { pre with adviceTape := { pre.adviceTape with
    readPosition := pre.adviceTape.readPosition + width.toNat } }
  have preparedAgrees : RegisterAgreementOn live witness t prepared := by
    refine ⟨agrees.present, ?_⟩
    intro register member
    simpa only [sourceValue] using agrees.values register member
  have written := writeDst_afterWriteDst destination canonical value prepared
  refine ⟨value, encoded, ?_, fun next => preparedAgrees.write charAbove2pow128
    context equations next slot selected rowIs destinationIs value encoded written⟩
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instructionIs]; rfl), instructionIs]
  simp only [execWithTapeAnswer, valid, if_true]
  change (do writeDst destination value; pure RETIRE_SUCCESS) prepared = _
  simp only [bind, EStateM.bind, written, pure, EStateM.pure]
  rfl

end JoltConstraints.Soundness
