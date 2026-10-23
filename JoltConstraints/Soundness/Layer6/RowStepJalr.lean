import JoltConstraints.Soundness.Layer6.RowStepCommon
import JoltConstraints.Soundness.Layer5.Jalr

/-! Append an indirect jump using live register agreement. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- An indirect jump appends its successful execution and preserves the expansion
invariant; for example, ECALL's last row jumps through the live mtvec register.
See jolt/tracer/src/instruction/jalr.rs (`JALR::exec`) at 5def437f. -/
theorem append_jalr_row
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (assumptions : inst.SoundnessAssumptions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (indexIs : next.val = first.val + done) (entry : RawRowEntry run next pre)
    (registers : RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ pre)
    (nextPC : pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
      if source_is_compressed run.bytecode next then 2 else 4))
    {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .JALR destination base imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have canonical : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical base = true := by
    simpa only [instruction, JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true]
      using (bytecodeRow_rowOk context rowIs).canonical
  have baseLive := expansion_sources_live inst.program context.bytecode context.expands first
    state.starts done unfinished _ atRow base (by rw [instruction]; simp [ExpansionTempLiveness.readSources])
  have last : run.bytecode[next].virtual_sequence_remaining.getD 0 = 0 := by
    have ends := (bytecodeRow_rowOk context rowIs).ends (by rw [instruction]; rfl)
    simpa [JoltInstructionRow.continues] using ends
  rw [source_compressed_of_last run.bytecode next last] at nextPC
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨written, executes, registerNext⟩ := jalr_step joltField context equations selected rowIs
    instruction (terminal_link_no_wrap inst.program run.bytecode run.expands assumptions.pcNoWrap next last)
    registers baseLive nextPC 0 advice
  let step : TraceRow run.bytecode := ⟨next, advice, pre, afterWriteDst destination
    (run.bytecode[next].address + if run.bytecode[next].is_compressed then 2 else 4)
    { pre with sail := System.setNextPCState pre.sail (jolt_jalr_target64 (sourceValue base pre) imm) }⟩
  have zero : witness.RamAddress ⟨run.rows.size, bound⟩ = 0 := by
    apply ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag,
        instruction, JoltMetadata.opcodeFlag] using opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Load ⟨run.rows.size, bound⟩ slot selected
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag,
        instruction, JoltMetadata.opcodeFlag] using opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Store ⟨run.rows.size, bound⟩ slot selected
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.2 (by rw [instruction]; rfl) baseLive
  have rs2 := rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
    ⟨run.rows.size, bound⟩ slot selected
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs
    (by simpa only [step, instruction, rs1Operand?] using rs1)
    (by simpa only [step, rowIs, Option.bind_some, instruction, rs2Operand?, bytecodeRs2Register] using rs2)
    (by simpa only [step, instruction, TraceWitness.ramAccessAddress] using zero)
  have prepared := rawEntry_prepared entry (state.registers bound)
  have represented := representsPrefix_push joltField witness context equations run.toTrace step
    state.represents bound rows zero
    (by cases destination <;> exact prepared.2.1)
    (by cases destination <;> exact prepared.2.2)
  have after (h : run.rows.size + 1 < params.traceLength) :
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1)) witness
        ⟨run.rows.size + 1, h⟩ step.postState := by
    apply (registerNext h).mono
    intro register live
    rcases expansionLive_after context.bytecode first done _ atRow register live with old | ⟨dst, written, same⟩
    · exact Or.inl old
    · have equal : destination = dst := by simpa only [instruction, Instr.destination?, Option.mem_some_iff] using written
      exact Or.inr (same.trans (congrArg TraceWitness.destinationRegisterAddress equal.symm))
  obtain ⟨candidate, traceEq, answers, extendsRun, size, after⟩ := append_expansion_row joltField
    witness context equations run first done state unfinished bound step 0 indexIs executes entry represented zero after
  refine ⟨step, 0, candidate, indexIs, entry, registers.present, traceEq, executes, ?_, ?_,
    answers, extendsRun, size, after⟩
  · intro value member
    simp only [TraceRow.someTracerAdvice?, step, withRuntimeAdvice_eq_of_noAdvice _ advice
      (by rw [instruction]; rfl), instruction, Instr.adviceValue?] at member
    cases member
  · intro dst width same
    have impossible := instruction.symm.trans same
    cases impossible
end JoltInstance
