import JoltConstraints.theorems.Soundness.Layer5.Jal

open LeanRV64D
set_option autoImplicit false
namespace JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions JoltISA

/-- Executing either halt records its kind after writing the prepared link.
For example, a panic halt records panic even when its destination is virtual.
This bytecode-only calculation is a candidate to move into JoltBytecode. -/
theorem execHalt_afterWriteDst (kind : JoltHaltKind) (dst : Dst)
    (pre : SailJoltState) (link address : BitVec 64)
    (canonical : JoltRegisterEncoding.destinationIsCanonical dst = true)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link) :
    execHalt kind dst pre = .ok RETIRE_SUCCESS
      (recordHalt kind { afterWriteDst dst link pre with
        sail := System.setNextPCState (afterWriteDst dst link pre).sail address }) := by
  have written := writeDst_afterWriteDst dst canonical link pre
  have readNext : liftSail (LeanRV64D.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail _ nextPC]
  have readPC : liftSail (LeanRV64D.readReg Register.PC) pre = .ok address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail _ pc]
  simp only [execHalt, bind, EStateM.bind, readNext, readPC, written]
  rfl

/-- An instruction classified as a halt has precisely the corresponding halt shape.
For example, a success classification supplies a `JoltSuccess` destination. -/
theorem halt_instruction_of_kind (instruction : Instr) (kind : JoltHaltKind)
    (classified : instruction.haltKind? = some kind) :
    ∃ dst, instruction = match kind with | .success => .JoltSuccess dst | .panic => .Panic dst := by
  unfold Instr.haltKind? at classified
  split at classified
  · cases classified
    exact ⟨_, rfl⟩
  · cases classified
    exact ⟨_, rfl⟩
  · cases classified

/-- Tape answers and runtime advice do not alter either explicit halt.
For example, the relaxed panic row executes the same shared halt body. -/
theorem execWithTapeAnswer_halt_eq (kind : JoltHaltKind) (dst : Dst)
    (instruction : Instr)
    (shape : instruction = match kind with | .success => .JoltSuccess dst | .panic => .Panic dst)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice) :
    execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer = execHalt kind dst := by
  cases kind <;> subst instruction <;> rfl

/-- With prepared source and link registers, the relaxed halt writes its destination
and records its kind; for example, a panic halt retains the prepared link value. -/
theorem execWithTapeAnswer_halt (kind : JoltHaltKind) (dst : Dst)
    (instruction : Instr)
    (shape : instruction = match kind with | .success => .JoltSuccess dst | .panic => .Panic dst)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice)
    (pre : SailJoltState) (link address : BitVec 64)
    (canonical : JoltRegisterEncoding.destinationIsCanonical dst = true)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link) :
    execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer pre = .ok RETIRE_SUCCESS
      (recordHalt kind { afterWriteDst dst link pre with
        sail := System.setNextPCState (afterWriteDst dst link pre).sail address }) := by
  rw [execWithTapeAnswer_halt_eq kind dst instruction shape answer advice]
  exact execHalt_afterWriteDst kind dst pre link address canonical pc nextPC

/-- A selected explicit halt writes its constrained link, restores its source PC
as nextPC, and records its kind without changing shared memory.
For example, Panic writes its link and sets the public panic flag to true.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`). -/
theorem halt_step
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (joltField : 2 ^ 128 - 2 ^ 64 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (kind : JoltHaltKind) (dst : Dst)
    (instruction : row.instruction = match kind with | .success => .JoltSuccess dst | .panic => .Panic dst)
    (noWrap : row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (pc : pre.sail.regs.get? Register.PC = some row.address)
    (nextPC : pre.sail.regs.get? Register.nextPC =
      some (row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let link := row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)
    let post := recordHalt kind { afterWriteDst dst link pre with
      sail := System.setNextPCState (afterWriteDst dst link pre).sail row.address }
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn (fun register => live register ∨
        register = TraceWitness.destinationRegisterAddress dst)
        witness ⟨t.val + 1, next⟩ post := by
  dsimp only
  have destination : row.instruction.destination? = some dst := by
    cases kind <;> rw [instruction] <;> rfl
  have jump : JoltMetadata.opcodeFlag row.instruction .Jump = true := by
    cases kind <;> rw [instruction] <;> rfl
  have encoded := jump_write_value joltField context equations selected rowIs jump noWrap
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destination
  constructor
  · exact execWithTapeAnswer_halt kind dst row.instruction instruction answer advice
      pre _ _ canonical pc nextPC
  · intro next
    have written := writeDst_afterWriteDst dst canonical
      (row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)) pre
    have writtenAgreement := (agrees.write joltField context equations next slot selected rowIs
      destination _ encoded written).setNextPC row.address
    exact ⟨writtenAgreement.present, writtenAgreement.values⟩

end JoltConstraints.Soundness
