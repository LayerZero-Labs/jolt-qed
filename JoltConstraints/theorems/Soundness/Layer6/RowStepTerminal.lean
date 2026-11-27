import JoltConstraints.theorems.Soundness.Layer6.RowStepJalr
import JoltConstraints.theorems.Soundness.Layer5.Halt
import JoltConstraints.theorems.Soundness.Layer5.HostCallRegisterFrame

open LeanRV64D

/-! The terminal direct jump and host-call row extensions. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- Append a terminal direct jump from its prepared PC and live-register state.
For example, `jal x1, 8` writes its source link into x1 before the next source.
See jolt/tracer/src/instruction/jal.rs (`JAL::exec`) at ff6fc6568. -/
theorem append_jal_row
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
    (pc : pre.sail.regs.get? Register.PC = some run.bytecode[next].address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
      if source_is_compressed run.bytecode next then 2 else 4))
    {destination : Dst} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .JAL destination imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨_, slot, selected, _, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have last : run.bytecode[next].virtual_sequence_remaining.getD 0 = 0 := by
    have ends := (bytecodeRow_rowOk context rowIs).ends (by rw [instruction]; rfl)
    simpa [JoltInstructionRow.continues] using ends
  have compressed := source_compressed_of_last run.bytecode next last
  rw [compressed] at nextPC
  have noWrap := expand_program_next_pc_no_wrap inst.program run.bytecode run.expands
    inst.program.next_pc_no_wrap next
  rw [compressed] at noWrap
  have nextPCLink : pre.sail.regs.get? Register.nextPC =
      some (run.bytecode[next].address +
        BitVec.ofNat 64 (if run.bytecode[next].is_compressed then 2 else 4)) := by
    cases isCompressed : run.bytecode[next].is_compressed <;>
      simpa only [isCompressed, Bool.false_eq_true, ↓reduceIte] using! nextPC
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨_, executes, registerNext⟩ := jal_step joltField context equations selected rowIs
    instruction noWrap registers pc nextPCLink 0 advice
  let post := { afterWriteDst destination
      (run.bytecode[next].address + BitVec.ofNat 64 (if run.bytecode[next].is_compressed then 2 else 4)) pre with
    sail := System.setNextPCState
      (afterWriteDst destination
        (run.bytecode[next].address + BitVec.ofNat 64 (if run.bytecode[next].is_compressed then 2 else 4)) pre).sail
      (run.bytecode[next].address + imm) }
  have rs1 : witness.Rs1Value ⟨run.rows.size, bound⟩ = 0 := by
    simpa only [rowIs, Option.bind_some, instruction, bytecodeRs1Register] using
      rs1Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
        ⟨run.rows.size, bound⟩ slot selected
  exact append_jump_row joltField witness context equations run first done state unfinished bound
    next pre indexIs entry registers destination (by rw [instruction]; rfl) (by rw [instruction]; rfl) post advice
    executes registerNext (by simpa only [instruction, rs1Operand?] using rs1)
    (by cases destination <;> rfl)

/-- Append either explicit halt with its link write and recorded halt kind.
For example, EBREAK's Panic row completes the represented source expansion. -/
theorem append_halt_row
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
    (pc : pre.sail.regs.get? Register.PC = some run.bytecode[next].address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
      if source_is_compressed run.bytecode next then 2 else 4))
    (kind : JoltHaltKind) (destination : Dst) (src : Src) (imm : BitVec 12)
    (instruction : run.bytecode[next].instruction = haltRow kind destination src imm) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, _, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  have canonical : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical src = true := by
    have rowCanonical := (bytecodeRow_rowOk context rowIs).canonical
    cases kind <;>
      simpa only [instruction, haltRow, JoltRegisterEncoding.instructionIsCanonical,
        Bool.and_eq_true] using rowCanonical
  have srcLive := expansion_sources_live inst.program context.bytecode context.expands first
    state.starts done unfinished _ atRow src
    (by rw [instruction]; cases kind <;> simp [haltRow, ExpansionTempLiveness.readSources])
  have halted : run.bytecode[next].instruction.haltKind?.isSome = true := by
    cases kind <;> rw [instruction] <;> rfl
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have last : run.bytecode[next].virtual_sequence_remaining.getD 0 = 0 := by
    apply JoltConstraints.Soundness.ConstraintContext.halt_terminal context _ _ halted
    rw [← bytecodeEq]
    exact Array.getElem_mem next.isLt
  rw [source_compressed_of_last run.bytecode next last] at nextPC
  have noWrap := expand_program_next_pc_no_wrap inst.program run.bytecode run.expands
    inst.program.next_pc_no_wrap next
  rw [source_compressed_of_last run.bytecode next last] at noWrap
  have link : pre.sail.regs.get? Register.nextPC =
      some (run.bytecode[next].address +
        BitVec.ofNat 64 (if run.bytecode[next].is_compressed then 2 else 4)) := by
    cases compressed : run.bytecode[next].is_compressed <;>
      simpa only [compressed, Bool.false_eq_true, ↓reduceIte] using! nextPC
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨executes, registerNext⟩ := halt_step joltField context equations selected rowIs
    kind destination src imm instruction noWrap registers pc link 0 advice
  have rs1 := registers.rs1Value (two_pow_127_lt_char joltField) context equations selected rowIs
    src canonical.2 (by rw [instruction]; cases kind <;> rfl) srcLive
  exact append_jump_row joltField witness context equations run first done state unfinished bound
    next pre indexIs entry registers destination
    (by cases kind <;> rw [instruction] <;> rfl)
    (by cases kind <;> rw [instruction] <;> rfl) _ advice executes registerNext
    (by cases kind <;> simpa only [instruction, haltRow, rs1Operand?] using rs1)
    (by cases destination <;> rfl)

/-- Append a successful terminal HostIO row, preserving live registers and the
memory image while allowing its advice tape to grow.
Every host call retires; for example, an advice-write call can append bytes to the tape.
See jolt/tracer/src/instruction/virtual_host_io.rs (`VirtualHostIO::exec`)
at ff6fc6568. -/
theorem append_host_row
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
    (instruction : run.bytecode[next].instruction = .VirtualHostIO) :
    PlainRowExtension witness context run first done bound := by
  obtain ⟨atRow, slot, selected, slotIs, rowIs⟩ := state.selectedRow unfinished bound next indexIs
  let advice := runtimeAdviceFor run.bytecode[next].instruction 0
  obtain ⟨post, executes, sail, _⟩ := host_call_exec_sail_frame
    run next pre 0 instruction advice
  have zero : witness.RamAddress ⟨run.rows.size, bound⟩ = 0 := by
    apply ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag,
        instruction, JoltMetadata.opcodeFlag] using! opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Load ⟨run.rows.size, bound⟩ slot selected
    · simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag,
        instruction, JoltMetadata.opcodeFlag] using! opFlag_of_selected_bytecode
          (two_pow_127_lt_char joltField) context equations .Store ⟨run.rows.size, bound⟩ slot selected
  have rs1 : witness.Rs1Value ⟨run.rows.size, bound⟩ = 0 := by
    simpa only [rowIs, Option.bind_some, instruction, bytecodeRs1Register] using
      rs1Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
        ⟨run.rows.size, bound⟩ slot selected
  have rs2 : witness.Rs2Value ⟨run.rows.size, bound⟩ = 0 := by
    simpa only [rowIs, Option.bind_some, instruction, bytecodeRs2Register] using
      rs2Value_of_selected_bytecode (two_pow_127_lt_char joltField) context equations
        ⟨run.rows.size, bound⟩ slot selected
  let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
  have after (h : run.rows.size + 1 < params.traceLength) :
      RegisterAgreementOn (ExpansionLive context.bytecode first (done + 1)) witness
        ⟨run.rows.size + 1, h⟩ step.postState := by
    obtain ⟨other, otherExec, otherRegisters⟩ := host_call_selected_step joltField
      context equations run next pre h slot slotIs
      selected rowIs instruction registers advice 0
    have same : other = post := by
      rw [executes] at otherExec
      cases otherExec
      rfl
    subst other
    apply otherRegisters.mono
    intro register live
    rcases expansionLive_after context.bytecode first done _ atRow register live with old | ⟨dst, written, _⟩
    · exact old
    · rw [instruction] at written
      cases written
  exact append_nonmemory_row joltField witness context equations run first done state
    unfinished bound step 0 indexIs entry registers executes zero
    (by simpa only [step, instruction, rs1Operand?] using rs1)
    (by simpa only [step, instruction, rs2Operand?] using rs2)
    (by simp only [step, instruction, TraceWitness.ramAccessAddress])
    (by exact congrArg (·.mem) sail) after
    (by rw [instruction]; rfl)
    (by intro dst width; rw [instruction]; nofun)

end JoltInstance
