import JoltConstraints.Soundness.Layer5.MisaFrame
import JoltConstraints.Soundness.Layer5.Jal
import JoltConstraints.Soundness.Layer6.TerminalNextPC

/-! The execution-state invariant needed to turn witness-derived even branch
targets into successful Sail jumps. Witness register agreement alone does not
constrain Sail's compressed-instruction configuration. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem compressed_enabled_of_misa (state : SailState)
    (misa : state.regs.get? Register.misa = some 0x800000008014312f) :
    currentlyEnabled extension.Ext_Zca state = .ok true state := by
  have read := readReg_eq_of_get? Register.misa state _ misa
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp only [bind, EStateM.bind, read, pure, EStateM.pure]
  congr 1
  simp [hartSupports, _get_Misa_C, LeanRV64D.Functions.not,
    LeanRV64D.Functions.xlen, Sail.BitVec.extractLsb]

/-- The final state of an initialized relaxed run still enables compressed
instructions. The final state is the initial state for an empty run and the
last row's post-state otherwise; relaxed tape answers do not constrain its
instruction-set configuration.
For example, this fact lets an even target `0x80000006` pass Sail's bit-1
alignment check after any executed prefix.
The initial `misa` value has C set and is preserved by successful rows and
PC preparation.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::new`) and
jolt/tracer/src/instruction/beq.rs (`BEQ::exec`) at 5def437f. -/
theorem UntrustedAnswerRun.final_compressed_enabled
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    currentlyEnabled extension.Ext_Zca (TraceWitness.finalTraceState run.toTrace).sail =
      .ok true (TraceWitness.finalTraceState run.toTrace).sail := by
  exact compressed_enabled_of_misa _ run.final_misa

/-- Preparing the next source from a run's final state keeps compressed instructions
enabled; for example, a target ending in binary `10` remains aligned after fetching.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at 5def437f. -/
theorem UntrustedAnswerRun.prepared_compressed_enabled
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) (address : BitVec 64) (compressed : Bool) :
    currentlyEnabled extension.Ext_Zca
      (advance_pc address compressed (TraceWitness.finalTraceState run.toTrace)).sail =
      .ok true (advance_pc address compressed (TraceWitness.finalTraceState run.toTrace)).sail := by
  apply compressed_enabled_of_misa
  rw [advance_pc_misa, run.final_misa]

private theorem branch_shape (instruction : Instr) (lhs rhs : Src) (imm : BitVec 128)
    (shapes : instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm) :
    JoltMetadata.immediate instruction = imm.toInt ∧ instruction.destination? = none ∧
    JoltRegisterEncoding.instructionIsCanonical instruction =
      (JoltRegisterEncoding.sourceIsCanonical lhs && JoltRegisterEncoding.sourceIsCanonical rhs) ∧
    ∀ answer, execWithTapeAnswer instruction answer = (do
      let x ← readSrc lhs
      let y ← readSrc rhs
      if branchDecisionPure instruction x y then
        let pc ← liftSail (Sail.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else pure RETIRE_SUCCESS) := by
  rcases shapes with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

private theorem branch_target_even
    {F : Type} [Field F] (joltField : JoltField F) {params : WitnessParams}
    {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    {lhs rhs : Src} {imm : BitVec 128}
    (shapes : row.instruction = .BEQ lhs rhs imm ∨ row.instruction = .BNE lhs rhs imm ∨
      row.instruction = .BLT lhs rhs imm ∨ row.instruction = .BGE lhs rhs imm ∨
      row.instruction = .BLTU lhs rhs imm ∨ row.instruction = .BGEU lhs rhs imm)
    (taken : witness.ShouldBranch t = 1) :
    (row.address + imm.setWidth 64).toNat % 2 = 0 := by
  obtain ⟨index, _, rowEq⟩ := JoltInstance.real_slot_index context.bytecode slot.val row rowIs
  have valid : row.Valid := by
    rw [rowEq]
    exact (expand_program_rows_valid _ _ context.expands).rowValid index
  have accepted : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, accepted, _⟩ := context.entryIsRust
    unfold preprocess at accepted
    split at accepted
    · assumption
    · cases accepted
  have addressOk : bytecode_address_ok row.address = true := by
    rw [rowEq]
    exact pc_map_ok_addresses _ accepted index.val index.isLt
  have target := JoltInstance.terminal_taken_branch_field joltField joltInstance privateInputs
    witness context equations t slot selected row rowIs taken
  have nonzero := JoltInstance.branch_target_ne_zero joltField row valid addressOk branch
  have next : t.val + 1 < params.traceLength := by
    by_contra last
    have zero := equations.nextUnexpandedPCEqShift t
    rw [dif_neg last, target] at zero
    exact nonzero zero
  have real : witness.InstructionFlags .IsNoop ⟨t.val + 1, next⟩ ≠ 1 := by
    intro padding
    have zero := JoltInstance.unexpanded_zero_of_padding joltField joltInstance privateInputs
      witness context equations _ padding
    have shift := equations.nextUnexpandedPCEqShift t
    rw [dif_pos next] at shift
    exact nonzero (target.symm.trans (shift.trans zero))
  obtain ⟨successor, successorEq, _, even⟩ := JoltInstance.terminal_real_successor_address
    joltField joltInstance privateInputs witness context equations t next real
  obtain ⟨_, offset, offsetEq⟩ := valid.branch shapes
  have ram : RAM_START_ADDRESS ≤ row.address.toNat := by
    simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at addressOk
    exact addressOk.1
  have targetEq := JoltInstance.terminal_branch_real_target joltField row.address
    successor.address offset ram (by
      rw [← successorEq, target, (branch_shape _ _ _ _ shapes).1, offsetEq,
        BitVec.toInt_signExtend_of_le (by decide : 13 ≤ 128)])
  simpa only [targetEq, ← offsetEq] using even

private theorem jump_even (target : BitVec 64) (state : SailState)
    (even : target.toNat % 2 = 0)
    (enabled : currentlyEnabled extension.Ext_Zca state = .ok true state) :
    jump_to target state = .ok RETIRE_SUCCESS (System.setNextPCState state target) := by
  have bit0 : BitVec.access target 0 = 0#1 := by
    simp [Sail.BitVec.access, BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero, even]
  simp [jump_to, ext_control_check_pc, SailME.run, PreSail.PreSailME.run,
    Sail.assert, PreSail.assert, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, monadLift, liftM,
    Functor.map, EStateM.map, bind, EStateM.bind, pure, EStateM.pure,
    enabled, bit0, LeanRV64D.Functions.not, set_next_pc, Sail.writeReg, System.setNextPCState]
  rfl

/-- A selected conditional branch retires and preserves agreement on `live`.
Both compared sources must be live; `pc` supplies the prepared source address,
and `enabled` follows from `UntrustedAnswerRun.final_compressed_enabled` or
`UntrustedAnswerRun.prepared_compressed_enabled` at the execution boundary.
The satisfying witness supplies target alignment when the branch is taken.
For example, an equal BEQ can jump to an even target ending in binary `10`.
See jolt/tracer/src/instruction/beq.rs (`BEQ::exec`) and
jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs at 5def437f. -/
theorem branch_step {F : Type} [Field F] {params : WitnessParams}
    {witness : WitnessType F params} {live : Fin 128 → Prop}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (joltField : JoltField F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    {pre : SailJoltState} (agrees : RegisterAgreementOn live witness t pre)
    (sourcesLive : ∀ source ∈ ExpansionTempLiveness.readSources row.instruction,
      live (TraceWitness.sourceRegisterAddress source))
    (pc : pre.sail.regs.get? Register.PC = some row.address)
    (enabled : currentlyEnabled extension.Ext_Zca pre.sail = .ok true pre.sail)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    ∃ post, execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
      ∀ next : t.val + 1 < params.traceLength,
        RegisterAgreementOn live witness ⟨t.val + 1, next⟩ post := by
  obtain ⟨lhs, rhs, imm, shapes⟩ := JoltInstance.branch_instruction_of_flag _ branch
  have forms := JoltInstance.branch_operand_forms _ lhs rhs imm shapes
  have shape := branch_shape _ lhs rhs imm shapes
  have canonical := (bytecodeRow_rowOk context rowIs).canonical
  rw [shape.2.2.1, Bool.and_eq_true] at canonical
  have leftLive := sourcesLive lhs (by rw [forms.1]; simp)
  have rightLive := sourcesLive rhs (by rw [forms.1]; simp)
  have rs1 := agrees.rs1Value (two_pow_127_lt_char joltField) context equations
    selected rowIs lhs canonical.1 forms.2.1 leftLive
  have rs2 := agrees.rs2Value (two_pow_127_lt_char joltField) context equations
    selected rowIs rhs canonical.2 forms.2.2 rightLive
  have decision := JoltInstance.terminal_branch_decision joltField joltInstance privateInputs
    witness context equations t slot selected row rowIs branch _ _ rs1 rs2
  have readLeft := readSrc_of_present lhs pre agrees.present
  have readRight := readSrc_of_present rhs pre agrees.present
  have preserved := fun next => agrees.noWrite (two_pow_127_lt_char joltField)
    context equations next slot selected rowIs shape.2.1
  rw [withRuntimeAdvice_branch advice shapes, shape.2.2.2 answer]
  simp only [bind, EStateM.bind, readLeft, readRight]
  by_cases taken : branchDecisionPure row.instruction (sourceValue lhs pre) (sourceValue rhs pre) = true
  · have even := branch_target_even joltField context equations selected rowIs branch shapes
      (by simpa only [taken, if_true] using decision)
    have readPC : liftSail (Sail.readReg Register.PC) pre = .ok row.address pre := by
      unfold liftSail
      rw [readReg_eq_of_get? Register.PC pre.sail row.address pc]
    refine ⟨{ pre with sail := System.setNextPCState pre.sail (row.address + imm.setWidth 64) },
      ?_, fun next => (preserved next).setNextPC _⟩
    simp only [taken, if_true, EStateM.bind, readPC]
    simp only [liftSail, jump_even _ _ even enabled]
  · exact ⟨pre, by simp only [taken]; rfl, preserved⟩

end JoltConstraints.Soundness
