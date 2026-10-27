import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Completeness.Helpers.RegistersValProofHelpers

/-! Live-register execution of JALR, including virtual bases and aliased operands. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- A selected JALR reads its live base before writing the link, clears target
bit zero, and extends register agreement by its destination.
For example, `jalr x1, 0(x1)` jumps using the old x1 and then replaces x1 by the
prepared link; a virtual mtvec base follows the same rule.
The link does not wrap, while the target addition uses 64-bit wrapping semantics.
See jolt/tracer/src/instruction/jalr.rs (`JALR::exec`) at 5def437f. -/
theorem jalr_step
    {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {params : WitnessParams} {witness : WitnessType F params}
    (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : row.instruction = .JALR destination base imm)
    (noWrap : (row.address + if row.is_compressed then 2 else 4).toNat =
      row.address.toNat + if row.is_compressed then 2 else 4)
    {live : Fin 128 → Prop} {pre : SailJoltState}
    (registers : RegisterAgreementOn live witness t pre)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (nextPC : pre.sail.regs.get? Register.nextPC =
      some (row.address + if row.is_compressed then 2 else 4))
    (answer : BitVec 64) (advice : row.instruction.RuntimeAdvice) :
    let link := row.address + if row.is_compressed then 2 else 4
    let target := jolt_jalr_target64 (sourceValue base pre) imm
    let post := afterWriteDst destination link
      { pre with sail := System.setNextPCState pre.sail target }
    witness.RdWriteValue t = (link.toNat : F) ∧
    execWithTapeAnswer (row.instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post ∧
    (∀ next : t.val + 1 < params.traceLength,
      RegisterAgreementOn
        (fun register => live register ∨ register = TraceWitness.destinationRegisterAddress destination)
        witness ⟨t.val + 1, next⟩ post) := by
  dsimp only
  have canonical : JoltRegisterEncoding.destinationIsCanonical destination = true ∧
      JoltRegisterEncoding.sourceIsCanonical base = true := by
    simpa only [instruction, JoltRegisterEncoding.instructionIsCanonical, Bool.and_eq_true]
      using (bytecodeRow_rowOk context rowIs).canonical
  have baseRead := (registers.read base canonical.2 baseLive).1
  have encoded := JoltInstance.selected_jump_link_write_value joltField inst inputs witness
    context equations t slot selected row rowIs (by rw [instruction]; rfl) noWrap
  let target := jolt_jalr_target64 (sourceValue base pre) imm
  let middle := { pre with sail := System.setNextPCState pre.sail target }
  have prepared : RegisterAgreementOn live witness t middle := by
    refine ⟨insert_keeps_present _ _ _ registers.present, ?_⟩
    intro register isLive
    rw [show sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) middle =
      sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) pre from
        register42_nextPC_preserves_sourceValue _ target pre]
    exact registers.values register isLive
  have written := writeDst_afterWriteDst destination canonical.1
    (row.address + if row.is_compressed then 2 else 4) middle
  have readNext : liftSail (Sail.readReg Register.nextPC) pre =
      .ok (row.address + if row.is_compressed then 2 else 4) pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail _ nextPC]
  refine ⟨encoded, ?_, fun next => prepared.write joltField context equations next slot selected
    rowIs (by rw [instruction]; rfl) _ encoded written⟩
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instruction]; rfl), instruction]
  simp only [execWithTapeAnswer, execInstr, bind, EStateM.bind, readNext, baseRead]
  change (do writeDst destination _; pure RETIRE_SUCCESS) middle = _
  simp only [bind, EStateM.bind, written, pure, EStateM.pure]
  rfl

end JoltConstraints.Soundness
