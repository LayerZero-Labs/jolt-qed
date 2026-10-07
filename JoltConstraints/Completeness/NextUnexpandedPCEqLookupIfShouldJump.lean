import JoltConstraints.Constraints.NextUnexpandedPCEqLookupIfShouldJump
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Constraints.TracePCProofHelpers

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace JoltConstraints

private theorem writeDst_preserves_nextPC (dst : JoltISA.Dst) (value : BitVec 64)
    (pre post : SailJoltState)
    (hwrite : JoltISA.writeDst dst value pre = .ok () post) :
    post.sail.regs.get? Register.nextPC = pre.sail.regs.get? Register.nextPC := by
  cases dst with
  | xreg rd =>
    simp only [JoltISA.writeDst_xreg, liftSail, wX_bits_stateAfterWrite] at hwrite
    cases hwrite
    reg_cases rd <;>
      simp_all only [stateAfterWrite, wX_update_regs, regval_into_reg,
        Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte]
  | vreg vr =>
    by_cases hw : vr.toNat < 32
    · simp only [JoltISA.writeDst, writeVReg, hw, ↓reduceIte, throw, throwThe] at hwrite
      cases hwrite
    · simp only [JoltISA.writeDst, writeVReg, hw, ↓reduceIte] at hwrite
      cases hwrite
      rfl

private theorem jal_target (dst : JoltISA.Dst) (imm address link : BitVec 64)
    (pre post : SailJoltState)
    (hpc : pre.sail.regs.get? Register.PC = some address)
    (hnext : pre.sail.regs.get? Register.nextPC = some link)
    (hexec : JoltISA.execInstr (.JAL dst imm) pre =
      .ok (.Retire_Success ()) post) :
    post.sail.regs.get? Register.nextPC = some (address + imm) := by
  have hreadNext : liftSail (Sail.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link hnext]
  have hreadPC : liftSail (Sail.readReg Register.PC) pre = .ok address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail address hpc]
  simp only [JoltISA.execInstr, bind, EStateM.bind, hreadNext, hreadPC] at hexec
  cases hwrite : JoltISA.writeDst dst link pre with
  | error err state => simp only [hwrite] at hexec; cases hexec
  | ok result mid =>
    cases result
    have hpcWrite : liftSail (Sail.writeReg Register.nextPC (address + imm)) mid =
        .ok () { mid with sail := { mid.sail with
          regs := mid.sail.regs.insert Register.nextPC (address + imm) } } := by rfl
    simp only [hwrite, hpcWrite, pure, EStateM.pure] at hexec
    cases hexec
    simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, ↓reduceDIte, cast_eq]

private theorem jalr_target (dst : JoltISA.Dst) (base : JoltISA.Src)
    (imm link : BitVec 64) (pre post : SailJoltState)
    (hnext : pre.sail.regs.get? Register.nextPC = some link)
    (hexec : JoltISA.execInstr (.JALR dst base imm) pre =
      .ok (.Retire_Success ()) post) :
    post.sail.regs.get? Register.nextPC =
      some (jolt_jalr_target64 (JoltISA.sourceValue base pre) imm) := by
  have hreadNext : liftSail (Sail.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link hnext]
  simp only [JoltISA.execInstr, bind, EStateM.bind, hreadNext] at hexec
  cases hread : JoltISA.readSrc base pre with
  | error err state => simp only [hread] at hexec; cases hexec
  | ok source state =>
    obtain ⟨hstate, hsource⟩ := lookup_readSrc_value base pre state source hread
    subst state
    subst source
    let target := jolt_jalr_target64 (JoltISA.sourceValue base pre) imm
    let afterPC : SailJoltState :=
      { pre with sail := { pre.sail with
        regs := pre.sail.regs.insert Register.nextPC target } }
    have hpcWrite : liftSail (Sail.writeReg Register.nextPC target) pre =
        .ok () afterPC := by rfl
    simp only [hread] at hexec
    rw [hpcWrite] at hexec
    cases hwrite : JoltISA.writeDst dst link afterPC with
    | error err state => simp only [hwrite] at hexec; cases hexec
    | ok result mid =>
      cases result
      simp only [hwrite, pure, EStateM.pure] at hexec
      cases hexec
      have hpres := writeDst_preserves_nextPC dst link _ post hwrite
      simpa [afterPC, target] using hpres

private theorem jump_opcode_cases (instruction : JoltISA.Instr)
    (hjump : JoltMetadata.opcodeFlag instruction .Jump = true) :
    (∃ dst imm, instruction = .JAL dst imm) ∨
      (∃ dst base imm, instruction = .JALR dst base imm) := by
  cases instruction <;> simp_all [JoltMetadata.opcodeFlag]

private theorem withRuntimeAdvice_jump (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice)
    (hjump : JoltMetadata.opcodeFlag instruction .Jump = true) :
    instruction.withRuntimeAdvice advice = instruction := by
  cases instruction <;> simp_all [JoltMetadata.opcodeFlag, JoltISA.Instr.withRuntimeAdvice]

private theorem jump_row_target {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (hn : n < trace.rows.size)
    (hjump : JoltMetadata.circuitFlag
      trace.bytecode[trace.rows[n].rowIndex] .Jump = true) :
    trace.rows[n].postState.sail.regs.get? Register.nextPC =
      some (HonestWitness.rowLookupOutput trace.rows[n]) := by
  let row := trace.rows[n]
  let bc := trace.bytecode[row.rowIndex]
  change JoltMetadata.circuitFlag bc .Jump = true at hjump
  change row.postState.sail.regs.get? Register.nextPC =
    some (HonestWitness.rowLookupOutput row)
  have hpc := lookup_trace_PC trace n hn
  have hnext := jump_trace_nextPC trace n hn
  change row.preState.sail.regs.get? Register.PC = some bc.address at hpc
  change row.preState.sail.regs.get? Register.nextPC = some _ at hnext
  have hop : JoltMetadata.opcodeFlag bc.instruction .Jump = true := by
    simpa only [JoltMetadata.circuitFlag] using hjump
  rcases jump_opcode_cases bc.instruction hop with
    ⟨dst, imm, hinst⟩ | ⟨dst, base, imm, hinst⟩
  · have hexec := row.executes
    change JoltISA.execInstr (bc.instruction.withRuntimeAdvice row.runtimeAdvice)
      row.preState = .ok (.Retire_Success ()) row.postState at hexec
    rw [withRuntimeAdvice_jump bc.instruction row.runtimeAdvice hop, hinst] at hexec
    have htarget := jal_target dst imm bc.address
      (bc.address + BitVec.ofNat 64 (sourceLength trace.bytecode row.rowIndex))
      row.preState row.postState hpc hnext hexec
    simpa only [HonestWitness.rowLookupOutput, show
      trace.bytecode[row.rowIndex.val].instruction = .JAL dst imm from hinst,
      JoltISA.addWide_low] using htarget
  · have hexec := row.executes
    change JoltISA.execInstr (bc.instruction.withRuntimeAdvice row.runtimeAdvice)
      row.preState = .ok (.Retire_Success ()) row.postState at hexec
    rw [withRuntimeAdvice_jump bc.instruction row.runtimeAdvice hop, hinst] at hexec
    have htarget := jalr_target dst base imm
      (bc.address + BitVec.ofNat 64 (sourceLength trace.bytecode row.rowIndex))
      row.preState row.postState hnext hexec
    simpa only [HonestWitness.rowLookupOutput, show
      trace.bytecode[row.rowIndex.val].instruction = .JALR dst base imm from hinst]
      using htarget

private theorem jump_row_ends_source {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (hn : n < trace.rows.size)
    (hjump : JoltMetadata.circuitFlag
      trace.bytecode[trace.rows[n].rowIndex] .Jump = true) :
    trace.bytecode[trace.rows[n].rowIndex].continues = false := by
  let row := trace.rows[n]
  let bc := trace.bytecode[row.rowIndex]
  change JoltMetadata.circuitFlag bc .Jump = true at hjump
  change bc.continues = false
  have hop : JoltMetadata.opcodeFlag bc.instruction .Jump = true := by
    simpa only [JoltMetadata.circuitFlag] using hjump
  rcases jump_opcode_cases bc.instruction hop with
    ⟨dst, imm, hinst⟩ | ⟨dst, base, imm, hinst⟩
  · have h := (trace.rowValid row.rowIndex).jumpAtSourceEnd
    change (match bc.instruction with
      | .JAL .. | .JALR .. => bc.continues = false
      | _ => True) at h
    rw [hinst] at h
    exact h
  · have h := (trace.rowValid row.rowIndex).jumpAtSourceEnd
    change (match bc.instruction with
      | .JAL .. | .JALR .. => bc.continues = false
      | _ => True) at h
    rw [hinst] at h
    exact h

private theorem jump_next_row_address {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (hn : n < trace.rows.size) (hn1 : n + 1 < trace.rows.size)
    (hjump : JoltMetadata.circuitFlag
      trace.bytecode[trace.rows[n].rowIndex] .Jump = true) :
    trace.bytecode[trace.rows[n + 1].rowIndex].address =
      HonestWitness.rowLookupOutput trace.rows[n] := by
  have hend := jump_row_ends_source trace n hn hjump
  have htarget := jump_row_target trace n hn hjump
  have hsucc := trace.successor n hn hn1
  simp only [hend, Bool.false_eq_true, ↓reduceIte] at hsucc
  obtain ⟨haddr, _, _⟩ := hsucc
  rw [htarget] at haddr
  exact Option.some.inj haddr.symm

/-- Completeness target for a complete Rust trace, with its mandatory padding.
There is no jump-only or nonwrapping-arithmetic assumption. -/
theorem honestWitness_nextUnexpandedPCEqLookupIfShouldJump
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    nextUnexpandedPCEqLookupIfShouldJump
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change HonestWitness.ShouldJump params trace t *
    (HonestWitness.NextUnexpandedPC params trace t -
      HonestWitness.LookupOutput params trace t) = 0
  by_cases hreal : t.val < trace.rows.size
  · have hnextWitness : t.val + 1 < params.traceLength := by
      have hpad := tracePadded.2
      omega
    by_cases hnextReal : t.val + 1 < trace.rows.size
    · by_cases hjump : JoltMetadata.circuitFlag
        trace.bytecode[trace.rows[t.val].rowIndex] .Jump = true
      · have haddr := jump_next_row_address trace t.val hreal hnextReal hjump
        have hvalues : HonestWitness.NextUnexpandedPC (F := F) params trace t =
            HonestWitness.LookupOutput (F := F) params trace t := by
          simp only [HonestWitness.NextUnexpandedPC, dif_pos hnextWitness,
            HonestWitness.UnexpandedPC, dif_pos hnextReal,
            HonestWitness.LookupOutput, dif_pos hreal]
          exact congrArg (fun address : BitVec 64 => (address.toNat : F)) haddr
        rw [hvalues]
        simp
      · have hflag : HonestWitness.OpFlags params trace .Jump t = (0 : F) := by
          have hfalse : JoltMetadata.circuitFlag
              trace.bytecode[trace.rows[t.val].rowIndex] .Jump = false := by
            cases h : JoltMetadata.circuitFlag
              trace.bytecode[trace.rows[t.val].rowIndex] .Jump <;> simp_all
          simp only [HonestWitness.OpFlags, dif_pos hreal]
          change (if JoltMetadata.circuitFlag
              trace.bytecode[trace.rows[t.val].rowIndex] .Jump
            then (1 : F) else 0) = 0
          rw [hfalse]
          rfl
        simp [HonestWitness.ShouldJump, hflag]
    · have hnoop : HonestWitness.InstructionFlags params trace .IsNoop
          ⟨t.val + 1, hnextWitness⟩ = (1 : F) := by
        simp [HonestWitness.InstructionFlags, hnextReal]
      simp [HonestWitness.ShouldJump, hnextWitness, hnoop]
  · have hflag : HonestWitness.OpFlags params trace .Jump t = (0 : F) := by
      simp [HonestWitness.OpFlags, hreal]
    simp [HonestWitness.ShouldJump, hflag]

end JoltConstraints
