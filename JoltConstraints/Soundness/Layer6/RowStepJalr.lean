import JoltConstraints.Soundness.Layer6.PlainRow
import JoltConstraints.Soundness.Layer5.Jalr

/-! Append terminal non-memory rows and direct or indirect jumps using live register agreement. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- Append a row with its selected observations, unchanged memory and device,
and next-column live-register agreement to the represented expansion prefix.
For example, a final JALR row adds its link destination to the live set.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at 5def437f. -/
theorem append_nonmemory_row
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength)
    (step : TraceRow run.bytecode) (answer : BitVec 64)
    (indexIs : step.rowIndex.val = first.val + done)
    (entry : RawRowEntry run step.rowIndex step.preState)
    (registers : RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ step.preState)
    (executes : execWithTapeAnswer
      (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      answer step.preState = .ok RETIRE_SUCCESS step.postState)
    (zero : witness.RamAddress ⟨run.rows.size, bound⟩ = 0)
    (rs1 : witness.Rs1Value ⟨run.rows.size, bound⟩ =
      match rs1Operand? run.bytecode[step.rowIndex].instruction with
      | some src => ((sourceValue src step.preState).toNat : F) | none => 0)
    (rs2 : witness.Rs2Value ⟨run.rows.size, bound⟩ =
      match rs2Operand? run.bytecode[step.rowIndex].instruction with
      | some src => ((sourceValue src step.preState).toNat : F) | none => 0)
    (noAccess : TraceWitness.ramAccessAddress
      run.bytecode[step.rowIndex].instruction step.preState = none)
    (memory : step.postState.sail.mem = step.preState.sail.mem)
    (device : step.postState.jolt_device = step.preState.jolt_device)
    (after : ∀ h : run.rows.size + 1 < params.traceLength,
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1)) witness
        ⟨run.rows.size + 1, h⟩ step.postState)
    (noAdvice : run.bytecode[step.rowIndex].instruction.adviceValue? = none)
    (notAdviceLoad : ∀ dst width,
      run.bytecode[step.rowIndex].instruction ≠ .VirtualAdviceLoad dst width) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨_, slot, selected, slotIs, _⟩ := state.selectedRow unfinished bound step.rowIndex indexIs
  have rows := representsRows_push_operands joltField witness context equations run.toTrace step
    state.represents.toRepresentsRows bound slot selected slotIs rs1 rs2
    (by simpa only [noAccess] using zero)
  have prepared := rawEntry_prepared entry (state.registers bound)
  have represented := representsPrefix_push joltField witness context equations run.toTrace step
    state.represents bound rows zero (memory.trans prepared.2.1) (device.trans prepared.2.2)
  obtain ⟨candidate, traceEq, answers, extendsRun, size, extended⟩ := append_expansion_row
    joltField witness context equations run first done state unfinished bound step answer indexIs
    executes entry represented zero after
  refine ⟨step, answer, candidate, indexIs, entry, registers.present, traceEq, executes,
    ?_, ?_, answers, extendsRun, size, extended⟩
  · intro value member
    simp only [TraceRow.someTracerAdvice?, withRuntimeAdvice_eq_of_noAdvice _
      step.runtimeAdvice noAdvice, noAdvice] at member
    cases member
  · intro dst width same
    exact False.elim (notAdviceLoad dst width same)

private theorem jump_traits (instruction : Instr) (destination : Dst) (pre : SailJoltState)
    (jump : (∃ imm, instruction = .JAL destination imm) ∨
      (∃ base imm, instruction = .JALR destination base imm)) :
    JoltMetadata.opcodeFlag instruction .Load = false ∧
    JoltMetadata.opcodeFlag instruction .Store = false ∧
    rs2Operand? instruction = none ∧
    TraceWitness.ramAccessAddress instruction pre = none ∧
    instruction.adviceValue? = none ∧
    instruction.destination? = some destination ∧
    (∀ dst width, instruction ≠ .VirtualAdviceLoad dst width) := by
  rcases jump with ⟨imm, isJal⟩ | ⟨base, imm, isJalr⟩
  · simp [isJal, JoltMetadata.opcodeFlag, rs2Operand?, TraceWitness.ramAccessAddress,
      Instr.adviceValue?, Instr.destination?]
  · simp [isJalr, JoltMetadata.opcodeFlag, rs2Operand?, TraceWitness.ramAccessAddress,
      Instr.adviceValue?, Instr.destination?]

/-- Append either kind of terminal jump after its local execution has written
the constrained link; for example, JAL and JALR share the selected-row,
observation, memory and live-destination argument.
See jolt/tracer/src/instruction/jal.rs (`JAL::exec`) and
jolt/tracer/src/instruction/jalr.rs (`JALR::exec`) at 5def437f. -/
theorem append_jump_row
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
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
    (destination : Dst)
    (jump : (∃ imm, run.bytecode[next].instruction = .JAL destination imm) ∨
      (∃ base imm, run.bytecode[next].instruction = .JALR destination base imm))
    (post : SailJoltState) (advice : run.bytecode[next].instruction.RuntimeAdvice)
    (executes : execWithTapeAnswer
      (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre = .ok RETIRE_SUCCESS post)
    (registerNext : ∀ h : run.rows.size + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => ExpansionLive context.bytecode first done register ∨
          register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨run.rows.size + 1, h⟩ post)
    (rs1 : witness.Rs1Value ⟨run.rows.size, bound⟩ =
      match rs1Operand? run.bytecode[next].instruction with
      | some src => ((sourceValue src pre).toNat : F) | none => 0)
    (memory : post.sail.mem = pre.sail.mem)
    (device : post.jolt_device = pre.jolt_device) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, _, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  obtain ⟨noLoad, noStore, rs2None, noAccess, noAdvice, destinationIs, notAdviceLoad⟩ :=
    jump_traits run.bytecode[next].instruction destination pre jump
  have zero : witness.RamAddress ⟨run.rows.size, bound⟩ = 0 := by
    apply ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, noLoad,
        Bool.false_eq_true, ↓reduceIte] using opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Load ⟨run.rows.size, bound⟩ slot selected
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, noStore,
        Bool.false_eq_true, ↓reduceIte] using opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Store ⟨run.rows.size, bound⟩ slot selected
  have witnessRs2 : witness.Rs2Value ⟨run.rows.size, bound⟩ = 0 := by
    have selectedRs2 := rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField)
      context equations ⟨run.rows.size, bound⟩ slot selected
    simpa only [rowIs, Option.bind_some, bytecodeRs2Register_eq_rs2Operand,
      rs2None, Option.map_none, Option.bind_none] using selectedRs2
  let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
  have after (h : run.rows.size + 1 < params.traceLength) :
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1)) witness
        ⟨run.rows.size + 1, h⟩ step.postState := by
    apply (registerNext h).mono
    intro register live
    rcases expansionLive_after context.bytecode first done _ atRow register live with old | ⟨dst, written, same⟩
    · exact Or.inl old
    · have equal : destination = dst := by
        simpa only [destinationIs, Option.mem_some_iff] using written
      exact Or.inr (same.trans (congrArg TraceWitness.destinationRegisterAddress equal.symm))
  exact append_nonmemory_row joltField witness context equations run first done state
    unfinished bound step 0 indexIs entry registers executes zero rs1
    (by simpa only [step, rs2None] using witnessRs2) noAccess memory device after
    noAdvice notAdviceLoad

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
  obtain ⟨_, executes, registerNext⟩ := jalr_step joltField context equations selected rowIs
    instruction (terminal_link_no_wrap inst.program run.bytecode run.expands assumptions.pcNoWrap next last)
    registers baseLive nextPC 0 advice
  let post := afterWriteDst destination
    (run.bytecode[next].address + if run.bytecode[next].is_compressed then 2 else 4)
    { pre with sail := System.setNextPCState pre.sail (jolt_jalr_target64 (sourceValue base pre) imm) }
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    base canonical.2 (by rw [instruction]; rfl) baseLive
  exact append_jump_row joltField witness context equations run first done state unfinished bound
    next pre indexIs entry registers destination (Or.inr ⟨base, imm, instruction⟩) post advice
    executes registerNext (by simpa only [instruction, rs1Operand?] using rs1)
    (by cases destination <;> rfl) (by cases destination <;> rfl)
end JoltInstance
