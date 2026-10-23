import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! A selected JAL row writes the return address and updates Sail's `nextPC`.
The jump constraint supplies the return address, including compressed rows;
the execution-prefix induction must connect the selected row's address to
Sail's PC and its already advanced `nextPC`. The no-wrap fact follows from
the program's approved `NextPCNoWrap` assumption at the source boundary.
At public Rust pin 8bbb2357:
See : jolt/tracer/src/instruction/jal.rs:19-30
See : jolt/crates/jolt-riscv/src/instructions/i/jal.rs -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem jal_write_value
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {dst : Dst} {imm : BitVec 64}
    (instruction : row.instruction = .JAL dst imm)
    (noWrap : row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64) :
    witness.RdWriteValue t =
      ((row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have flags := opFlag_of_selected_bytecode bound context equations
  have jumpFlag : witness.OpFlags .Jump t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag,
      instruction, JoltMetadata.opcodeFlag] using flags .Jump t slot selected
  have compressedFlag : witness.OpFlags .IsCompressed t =
      if row.is_compressed then 1 else 0 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag] using
      flags .IsCompressed t slot selected
  have address : witness.UnexpandedPC t = (row.address.toNat : F) := by
    simpa only [bytecodeAddress, rowIs] using
      unexpandedPC_of_selected_bytecode bound context equations t slot selected
  have relation := equations.rdWriteEqPCPlusConstIfJump t
  rw [jumpFlag, one_mul, address, compressedFlag] at relation
  by_cases compressed : row.is_compressed = true
  · simp only [compressed, ↓reduceIte] at relation ⊢
    have sum : (row.address + BitVec.ofNat 64 2).toNat = row.address.toNat + 2 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa only [compressed, ↓reduceIte] using noWrap)]
    rw [sum, Nat.cast_add]
    linear_combination relation
  · have notCompressed : row.is_compressed = false := Bool.eq_false_iff.mpr compressed
    simp only [notCompressed, Bool.false_eq_true, ↓reduceIte] at relation ⊢
    have sum : (row.address + BitVec.ofNat 64 4).toNat = row.address.toNat + 4 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa only [notCompressed, ↓reduceIte] using noWrap)]
    rw [sum, Nat.cast_add]
    linear_combination relation

end JoltConstraints.Soundness

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem sourceValue_setNextPC (source : Src) (target : BitVec 64)
    (state : SailJoltState) :
    sourceValue source { state with sail := System.setNextPCState state.sail target } =
      sourceValue source state := by
  cases source with
  | vreg r => rfl
  | xreg r =>
    reg_cases r <;>
      simp_all only [sourceValue, System.setNextPCState, Std.ExtDHashMap.get?_insert,
        beq_iff_eq, reduceCtorEq, ↓reduceDIte]

/-- Updating Sail's `nextPC` preserves agreement on every live register.
For example, a JAL updating nextPC keeps the value of a live temporary 40. -/
theorem RegisterAgreementOn.setNextPC
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {t : Fin params.traceLength} {state : SailJoltState} {live : Fin 128 → Prop}
    (agrees : RegisterAgreementOn live witness t state) (target : BitVec 64) :
    RegisterAgreementOn live witness t
      { state with sail := System.setNextPCState state.sail target } := by
  refine ⟨insert_keeps_present _ _ _ agrees.present, ?_⟩
  intro register member
  rw [sourceValue_setNextPC]
  exact agrees.values register member

/-- A selected JAL row writes the constrained return address, executes the
wrapped jump, and extends live-register agreement by its destination.
For example, `jal x1, 8` makes x1 agree with the link after the jump.
The local PC, advanced `nextPC`, and no-wrap facts belong to the global
execution prefix. -/
theorem jal_step
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {dst : Dst} {imm : BitVec 64}
    (instruction : row.instruction = .JAL dst imm)
    (noWrap : row.address.toNat + (if row.is_compressed then 2 else 4) < 2 ^ 64)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (agrees : RegisterAgreementOn live witness t pre)
    (pc : pre.sail.regs.get? Register.PC = some row.address)
    (nextPC : pre.sail.regs.get? Register.nextPC =
      some (row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let link := row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)
    let target := row.address + imm
    let post := { afterWriteDst dst link pre with
      sail := System.setNextPCState (afterWriteDst dst link pre).sail target }
    witness.RdWriteValue t = (link.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress dst)
        witness ⟨t.val + 1, next⟩ post := by
  dsimp only
  have encoded := jal_write_value charAbove2pow128 context equations selected rowIs
    instruction noWrap
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical (by rw [instruction]; rfl)
  have written := writeDst_afterWriteDst dst canonical
    (row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)) pre
  have readNext : liftSail (Sail.readReg Register.nextPC) pre =
      .ok (row.address + BitVec.ofNat 64 (if row.is_compressed then 2 else 4)) pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail _ nextPC]
  have readPC : liftSail (Sail.readReg Register.PC) pre = .ok row.address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail _ pc]
  refine ⟨encoded, ?_, ?_⟩
  · rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instruction]; rfl)]
    rw [instruction]
    simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, readNext,
      readPC, written]
    rfl
  · intro next
    apply RegisterAgreementOn.setNextPC
    exact agrees.write charAbove2pow128 context equations next slot selected rowIs
      (by rw [instruction]; rfl) _ encoded written

end JoltConstraints.Soundness
