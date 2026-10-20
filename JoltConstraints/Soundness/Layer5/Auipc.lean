import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer4.Arithmetic

/-! A selected AUIPC row writes its address plus the decoded immediate. Jolt's
tracer adds the instruction's own address; the Lean interpreter reads Sail's PC.
The execution-prefix invariant must equate that PC with the selected row's
address.
At public pin 8bbb2357:
See : jolt/tracer/src/instruction/auipc.rs:21-28
See : jolt/crates/jolt-riscv/src/instructions/i/auipc.rs:1-8
See : jolt/crates/jolt-lookup-tables/src/instructions/riscv/auipc.rs:1-35 -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {destination : Dst} {imm : BitVec 64}
  (instructionIs : row.instruction = .AUIPC destination imm)

include charAbove2pow128 context equations selected rowIs instructionIs

private theorem auipc_write_value :
    witness.RdWriteValue t = ((row.address + imm).toNat : F) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  have flags := opFlag_of_selected_bytecode bound context equations
  have addFlag : witness.OpFlags .AddOperands t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .AddOperands t slot selected
  have writeFlag : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, instructionIs,
      JoltMetadata.opcodeFlag] using flags .WriteLookupOutputToRD t slot selected
  have address : witness.UnexpandedPC t = (row.address.toNat : F) := by
    simpa only [bytecodeAddress, rowIs] using
      unexpandedPC_of_selected_bytecode bound context equations t slot selected
  have immediate : witness.Imm t = (imm.toNat : F) := by
    simpa only [bytecodeImmediate, rowIs, instructionIs, JoltMetadata.immediate,
      Int.cast_natCast] using imm_of_selected_bytecode bound context equations t slot selected
  have inputs : witness.LeftInstructionInput t = (row.address.toNat : F) ∧
      witness.RightInstructionInput t = (imm.toNat : F) := by
    simpa only [instructionIs, JoltMetadata.instructionFlag, Bool.false_eq_true,
      ↓reduceIte, zero_add, address, immediate] using
      instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t writeFlag]
  exact lookupOutput_rangeCheck_add charAbove2pow128 context equations t slot selected
    (by simp only [rowIs, Option.bind_some, instructionIs, JoltMetadata.lookupTable])
    addFlag row.address imm inputs.1 inputs.2

/-- AUIPC executes with the constrained wrapped sum. The global execution-prefix
proof must connect Sail's PC to the selected row's address. -/
theorem auipc_step {pre : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (pc : pre.sail.regs.get? Register.PC = some row.address)
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let value := row.address + imm
    witness.RdWriteValue t = (value.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS (afterWriteDst destination value pre) ∧
    ∀ next : t.val + 1 < params.traceLength,
      RegisterAgreement witness ⟨t.val + 1, next⟩ (afterWriteDst destination value pre) := by
  dsimp only
  have readPC : liftSail (get_arch_pc ()) pre = .ok row.address pre := by
    unfold liftSail get_arch_pc
    rw [readReg_eq_of_get? Register.PC pre.sail row.address pc]
  apply registerWrite_step context equations selected rowIs charAbove2pow128 agrees
    destination (by rw [instructionIs]; rfl) _
    (auipc_write_value charAbove2pow128 context equations selected rowIs instructionIs)
    answer advice (by rw [instructionIs]; rfl)
  rw [instructionIs]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, readPC, addWide_low]

end JoltConstraints.Soundness
