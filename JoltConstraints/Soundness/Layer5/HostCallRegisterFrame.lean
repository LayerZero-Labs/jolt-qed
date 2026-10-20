import JoltConstraints.Soundness.Layer5.HostCallRestriction
import JoltConstraints.Soundness.Layer5.HostCallExpansion
import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.expansion_facts

/-! A successful HostIO row preserves Sail state and virtual registers. Its
selected destination table entry can still change, so this file proves
agreement for the other entries. The global induction must account for that
destination until a later write restores agreement. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem sourceValue_of_host_frame (source : Src)
    (pre post : SailJoltState) (sail : post.sail = pre.sail)
    (vregs : post.vregs = pre.vregs) :
    sourceValue source post = sourceValue source pre := by
  cases source <;> simp only [sourceValue, sail, vregs]

/-- The HostIO x0 rewrite uses register 40, the first register checked by
`tempsReadAfterWrite`. -/
theorem host_call_rewrite_register_is_40 :
    rdZeroRewriteVReg = BitVec.ofNat 7 40 := by rfl

/-- A source HostIO with `rd = x0` expands to a row whose destination is
`rdZeroRewriteVReg`. The caller obtains `zero` from the approved restriction. -/
theorem host_call_zero_destination_is_temp (rd rs1 : regidx) (imm : BitVec 12)
    (zero : isX0 rd = true) :
    (SourceInstruction.jolt (.VirtualHostIO rd rs1 imm)).expand =
      some (.native (.VirtualHostIO (.vreg rdZeroRewriteVReg) (.xreg rs1)
        (sign_extend (m := 64) imm))) := by
  simp [SourceInstruction.expand, ExpandedSource.ofNative, Instr.rewriteNative,
    sideEffectingDst, sideEffectingRdZeroDst, zero]

/-- HostIO cannot disturb agreement away from its selected table destination.
The destination entry itself needs the later temporary-liveness argument. -/
theorem RegisterAgreement.host_call_other
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    {destination : Dst} {source : Src} {imm : BitVec 64}
    (instruction : row.instruction = .VirtualHostIO destination source imm)
    {pre post : SailJoltState}
    (agrees : RegisterAgreement witness t pre)
    (sail : post.sail = pre.sail) (vregs : post.vregs = pre.vregs) :
    AllRegistersPresent post.sail ∧
    ∀ register : Fin 128,
      register ≠ TraceWitness.destinationRegisterAddress destination →
      witness.RegistersVal register ⟨t.val + 1, next⟩ =
        ((sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) post).toNat : F) := by
  refine ⟨sail ▸ agrees.present, ?_⟩
  intro register different
  rw [registersVal_succ_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations register t next chosen selected]
  simp only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    instruction, Instr.destination?, Option.map_some]
  rw [if_neg different, agrees.values]
  rw [sourceValue_of_host_frame _ pre post sail vregs]

/-- Register agreement immediately after an x0-destination HostIO row. The
rewritten destination is temporary 40; its witness value is not constrained
to equal the unchanged virtual register. -/
structure RegisterAgreementExceptHostTemp
    {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (t : Fin params.traceLength)
    (state : SailJoltState) : Prop where
  present : AllRegistersPresent state.sail
  values : ∀ register : Fin 128, register ≠ (40 : Fin 128) →
    witness.RegistersVal register t =
      ((sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) state).toNat : F)

/-- An available source operand can be read and matched to its table entry
while the HostIO temporary is excluded. -/
theorem RegisterAgreementExceptHostTemp.read
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {t : Fin params.traceLength} {state : SailJoltState}
    (agrees : RegisterAgreementExceptHostTemp witness t state) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (available : TraceWitness.sourceRegisterAddress source ≠ (40 : Fin 128)) :
    readSrc source state = .ok (sourceValue source state) state ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress source) t =
        ((sourceValue source state).toNat : F) := by
  refine ⟨readSrc_of_present source state agrees.present, ?_⟩
  simpa only [source_decode_encode source canonical] using
    agrees.values (TraceWitness.sourceRegisterAddress source) available

/-- A row without a destination preserves agreement outside the HostIO
temporary. -/
theorem RegisterAgreementExceptHostTemp.noWrite
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    (destinationIs : row.instruction.destination? = none)
    {state : SailJoltState}
    (agrees : RegisterAgreementExceptHostTemp witness t state) :
    RegisterAgreementExceptHostTemp witness ⟨t.val + 1, next⟩ state := by
  refine ⟨agrees.present, ?_⟩
  intro register different
  rw [registersVal_succ_of_selected_bytecode charAbove2pow127
    context equations register t next chosen selected]
  simpa only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    destinationIs, Option.map_none] using agrees.values register different

/-- Once a selected row writes a constrained value to temporary 40, full
register agreement is restored. -/
theorem RegisterAgreementExceptHostTemp.write_temp
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    (destinationIs : row.instruction.destination? = some (.vreg rdZeroRewriteVReg))
    {pre post : SailJoltState}
    (agrees : RegisterAgreementExceptHostTemp witness t pre)
    (value : BitVec 64) (encoded : witness.RdWriteValue t = (value.toNat : F))
    (written : writeDst (.vreg rdZeroRewriteVReg) value pre = .ok () post) :
    RegisterAgreement witness ⟨t.val + 1, next⟩ post := by
  refine ⟨RegistersKept.write_rule _ value pre post () written agrees.present, ?_⟩
  intro register
  by_cases zero : register = 0
  · subst register
    rw [registersVal_x0 charAbove2pow128 context equations]
    change (0 : F) = ((0 : BitVec 64).toNat : F)
    simp
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destinationIs
  rw [registersVal_succ_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations register t next chosen selected]
  simp only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    destinationIs, Option.map_some]
  by_cases same : register =
      TraceWitness.destinationRegisterAddress (.vreg rdZeroRewriteVReg)
  · subst register
    rw [if_pos rfl, encoded, source_of_destination _ canonical,
      sourceValue_writeDst_same _ value pre post (by decide) written]
  · have different : register ≠ (40 : Fin 128) := by
      simpa only [TraceWitness.destinationRegisterAddress,
        host_call_rewrite_register_is_40, BitVec.toFin_ofNat] using same
    rw [if_neg same, agrees.values register different]
    rw [sourceValue_writeDst_other _ _ value pre post
      (by simpa only [source_encode_decode, BitVec.toFin_ofFin] using same)
      agrees.present written]

/-- Any successful constrained destination write preserves agreement outside
temporary 40. A write to temporary 40 also restores full agreement. -/
theorem RegisterAgreementExceptHostTemp.write
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    {destination : Dst} (destinationIs : row.instruction.destination? = some destination)
    {pre post : SailJoltState}
    (agrees : RegisterAgreementExceptHostTemp witness t pre)
    (value : BitVec 64) (encoded : witness.RdWriteValue t = (value.toNat : F))
    (written : writeDst destination value pre = .ok () post) :
    RegisterAgreementExceptHostTemp witness ⟨t.val + 1, next⟩ post := by
  refine ⟨RegistersKept.write_rule destination value pre post () written agrees.present, ?_⟩
  intro register available
  by_cases zero : register = 0
  · subst register
    rw [registersVal_x0 charAbove2pow128 context equations]
    change (0 : F) = ((0 : BitVec 64).toNat : F)
    simp
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destinationIs
  rw [registersVal_succ_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations register t next chosen selected]
  simp only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    destinationIs, Option.map_some]
  by_cases same : register = TraceWitness.destinationRegisterAddress destination
  · subst register
    rw [if_pos rfl, encoded, source_of_destination destination canonical,
      sourceValue_writeDst_same destination value pre post zero written]
  · rw [if_neg same, agrees.values register available]
    rw [sourceValue_writeDst_other destination _ value pre post
      (by simpa only [source_encode_decode, BitVec.toFin_ofFin] using same)
      agrees.present written]

private theorem source_available_of_not_read (row : Instr) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (member : source ∈ ExpansionTempLiveness.readSources row)
    (noRead : ExpansionTempLiveness.reads rdZeroRewriteVReg row = false) :
    TraceWitness.sourceRegisterAddress source ≠ (40 : Fin 128) := by
  intro same
  have tempCanonical :
      JoltRegisterEncoding.sourceIsCanonical (.vreg rdZeroRewriteVReg) = true := by
    decide
  have tempAddress :
      TraceWitness.sourceRegisterAddress (.vreg rdZeroRewriteVReg) =
        (40 : Fin 128) := by rfl
  have equalSource := sourceRegisterAddress_injective canonical tempCanonical
    (same.trans tempAddress.symm)
  subst source
  have reading : ExpansionTempLiveness.reads rdZeroRewriteVReg row = true := by
    simp only [ExpansionTempLiveness.reads, List.any_eq_true]
    exact ⟨.vreg rdZeroRewriteVReg, member, by simp⟩
  rw [noRead] at reading
  cases reading

/-- An operand of the first row of a source expansion remains readable after
HostIO, despite the missing value for temporary 40. -/
theorem RegisterAgreementExceptHostTemp.read_first_row
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {t : Fin params.traceLength} {state : SailJoltState}
    (agrees : RegisterAgreementExceptHostTemp witness t state)
    (sourceInstruction : SourceInstruction) (expanded : ExpandedSource)
    (expands : sourceInstruction.expand = some expanded)
    (row : Instr)
    (first : ExpansionTempLiveness.firstRow? expanded = some row)
    (source : Src) (canonical : JoltRegisterEncoding.sourceIsCanonical source = true)
    (member : source ∈ ExpansionTempLiveness.readSources row) :
    readSrc source state = .ok (sourceValue source state) state ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress source) t =
        ((sourceValue source state).toNat : F) := by
  have noRead := ExpansionTempLiveness.hostTemp_firstRow_noRead expanded
    (ExpansionFacts.expand_temps_ok sourceInstruction expanded expands) row first
  exact agrees.read source canonical
    (source_available_of_not_read row source canonical member noRead)

theorem RegisterAgreement.host_call_except_temp
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    {source : Src} {imm : BitVec 64}
    (instruction : row.instruction =
      .VirtualHostIO (.vreg rdZeroRewriteVReg) source imm)
    {pre post : SailJoltState}
    (agrees : RegisterAgreement witness t pre)
    (sail : post.sail = pre.sail) (vregs : post.vregs = pre.vregs) :
    RegisterAgreementExceptHostTemp witness ⟨t.val + 1, next⟩ post := by
  obtain ⟨present, values⟩ := RegisterAgreement.host_call_other charAbove2pow128
    context equations next chosen selected rowIs instruction agrees sail vregs
  refine ⟨present, ?_⟩
  intro register different
  apply values register
  simpa only [TraceWitness.destinationRegisterAddress,
    host_call_rewrite_register_is_40, BitVec.toFin_ofNat] using different

/-- A selected HostIO row executes and leaves exactly temporary 40 outside
register agreement. The source-level destination restriction is transferred
through program expansion. The slot equation is the execution-prefix link
between the selected witness slot and the next expanded row. -/
theorem host_call_selected_step
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (restricted : joltInstance.HostCallsSucceed)
    (restrictedDestination : joltInstance.program.HostCallRdZero)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (nextRow : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep nextRow pre)
    {t : Fin params.traceLength} (nextCycle : t.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotPosition : slot.val = nextRow.val + 1)
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {destination : Dst} {source : Src} {imm : BitVec 64}
    (instruction : row.instruction =
      .VirtualHostIO destination source imm)
    (agrees : RegisterAgreement witness t pre)
    (advice : run.bytecode[nextRow].instruction.RuntimeAdvice) (answer : BitVec 64) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[nextRow].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧
      RegisterAgreementExceptHostTemp witness ⟨t.val + 1, nextCycle⟩ post := by
  have sameBytecode : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have rowAt : bytecodeRow run.bytecode slot.val = some row := by
    simpa only [sameBytecode] using rowIs
  rw [slotPosition] at rowAt
  have runRow : bytecodeRow run.bytecode (nextRow.val + 1) =
      some run.bytecode[nextRow] := by
    simp only [bytecodeRow, Array.getElem?_eq_getElem nextRow.isLt, Fin.getElem_fin]
  have rowEq : run.bytecode[nextRow] = row :=
    Option.some.inj (runRow.symm.trans rowAt)
  have rowMember : row ∈ context.bytecode.toList := by
    rw [← sameBytecode, ← rowEq]
    apply List.mem_iff_getElem.mpr
    refine ⟨nextRow.val, ?_, ?_⟩
    · simpa only [Array.length_toList] using nextRow.isLt
    · simp only [Array.getElem_toList, Fin.getElem_fin]
  have destinationIs := host_program_destination joltInstance.program
    restrictedDestination context.bytecode context.expands row rowMember
    destination source imm instruction
  subst destination
  have instructionRun : run.bytecode[nextRow].instruction =
      .VirtualHostIO (.vreg rdZeroRewriteVReg) source imm := by
    rw [rowEq]
    exact instruction
  obtain ⟨post, executes, sail, vregs⟩ := host_call_exec_sail_frame
    restricted run nextRow pre ready _ _ _ answer instructionRun advice
  exact ⟨post, executes,
    RegisterAgreement.host_call_except_temp charAbove2pow128 context equations
      nextCycle slot selected rowIs instruction agrees sail vregs⟩

end JoltConstraints.Soundness
