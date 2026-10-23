import JoltConstraints.Soundness.Layer6.MemoryRowExecution

/-! The load and store row extensions, sharing their regional memory contract. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

section
variable {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN inst.program run.rows n)
    (bound : run.rows.size < params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (indexIs : next.val = first.val + done) (entry : RawRowEntry run next pre)
    (registers : RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ pre)

include joltField assumptions restrictions equations state unfinished honestAdvice indexIs entry registers

/-- An LD appends its row with live-register and cut-RAM agreement in either
address region; for example, a live temporary can address RAM or an input word.
See jolt/tracer/src/instruction/ld.rs (`LD::exec`) at 5def437f. -/
theorem append_ld_row {fault : LoadFaultClass} {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have ready : run.NextStep next pre := ⟨honestAdvice, state.noEarlierStop, entry⟩
  have canonical : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical base = true := by
    simpa only [instruction, JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true]
      using (bytecodeRow_rowOk context rowIs).canonical
  have baseLive := expansion_sources_live inst.program context.bytecode context.expands first
    state.starts done unfinished _ atRow base (by rw [instruction]; simp [ExpansionTempLiveness.readSources])
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.2 (by rw [instruction]; rfl) baseLive
  have encoded := ld_address_encoded (two_pow_127_lt_char joltField) context equations assumptions.ramRegionFits
    ⟨run.rows.size, bound⟩ slot selected _ rowIs fault destination base (sourceValue base pre) imm instruction rs1
  have prepared := rawEntry_prepared entry (state.registers bound)
  obtain ⟨ram, device⟩ := state.memoryAt bound entry
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨value, executes, registerNext, memory⟩ := load_row_execution joltField assumptions restrictions witness
    context equations run ⟨run.rows.size, bound⟩ next pre ready slot selected slotIs rowIs registers ram device
    (state.terminationWord bound) prepared.2.2 advice instruction baseLive encoded rfl
  let step : TraceRow run.bytecode := ⟨next, advice, pre, afterWriteDst destination value pre⟩
  have rs2 := rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
    ⟨run.rows.size, bound⟩ slot selected
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs
    (by simpa only [step, instruction, rs1Operand?] using rs1)
    (by simpa only [step, rowIs, Option.bind_some, instruction, rs2Operand?, bytecodeRs2Register] using rs2)
    (by simpa only [step, instruction, TraceWitness.ramAccessAddress] using encoded)
  apply append_memory_row joltField witness context equations run first done state unfinished bound step
    indexIs entry registers.present (by change run.bytecode[next].instruction.adviceValue? = none; rw [instruction]; rfl)
    (by intro dst width same; have impossible := instruction.symm.trans same; cases impossible) executes rows
  · intro nextCycle
    simpa [step, instruction, Instr.destination?, -Fin.getElem_fin] using registerNext nextCycle
  · simpa only [step, instruction, or_false] using memory

/-- An SD appends its row in either address region, preserving live registers
and excluding only the termination word from cut agreement.
For example, an output store and a RAM store use the same append proof.
See jolt/tracer/src/instruction/sd.rs (`SD::exec`) at 5def437f. -/
theorem append_sd_row {base source : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .SD base source imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have ready : run.NextStep next pre := ⟨honestAdvice, state.noEarlierStop, entry⟩
  have canonical := sd_canonical context rowIs instruction
  have live (source : Src) (member : source ∈ ExpansionTempLiveness.readSources run.bytecode[next].instruction) :=
    expansion_sources_live inst.program context.bytecode context.expands first state.starts done unfinished _ atRow source member
  have baseLive := live base (by rw [instruction]; simp [ExpansionTempLiveness.readSources])
  have sourceLive := live source (by rw [instruction]; simp [ExpansionTempLiveness.readSources])
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.1 (by rw [instruction]; rfl) baseLive
  have rs2 := registers.rs2Value (two_pow_127_lt_char joltField) context equations selected rowIs
    source canonical.2 (by rw [instruction]; rfl) sourceLive
  have encoded := sd_address_encoded (two_pow_127_lt_char joltField) context equations assumptions.ramRegionFits
    ⟨run.rows.size, bound⟩ slot selected _ rowIs base source (sourceValue base pre) imm instruction rs1
  have prepared := rawEntry_prepared entry (state.registers bound)
  obtain ⟨ram, device⟩ := state.memoryAt bound entry
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨post, executes, registerNext, memory⟩ := store_row_execution joltField assumptions restrictions witness
    context equations run ⟨run.rows.size, bound⟩ next pre ready slot selected slotIs rowIs registers ram device
    (state.terminationWord bound) prepared.2.2 advice instruction baseLive sourceLive encoded rfl
  let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs
    (by simpa only [step, instruction, rs1Operand?] using rs1)
    (by simpa only [step, instruction, rs2Operand?] using rs2)
    (by simpa only [step, instruction, TraceWitness.ramAccessAddress] using encoded)
  apply append_memory_row joltField witness context equations run first done state unfinished bound step
    indexIs entry registers.present (by change run.bytecode[next].instruction.adviceValue? = none; rw [instruction]; rfl)
    (by intro dst width same; have impossible := instruction.symm.trans same; cases impossible) executes rows
  · intro nextCycle
    simpa only [step, instruction, Instr.destination?, Option.not_mem_none, false_and, exists_false, or_false]
      using registerNext nextCycle
  · simpa only [step, instruction] using memory
end
end JoltInstance
