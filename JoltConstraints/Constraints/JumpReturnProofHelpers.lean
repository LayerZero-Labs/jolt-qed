import JoltConstraints.honest_witness
import JoltConstraints.metadata
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

theorem jump_prepareSource_nextPC (program : JoltProgram)
    (layout : program.SequenceLayout) (i : Fin program.expandedBytecode.size)
    (state : SailJoltState) :
    (program.prepareSource layout i state).sail.regs.get? Register.nextPC =
      some (program.expandedBytecode[i].address +
        BitVec.ofNat 64 (program.sourceLength layout i)) := by
  simp [JoltProgram.prepareSource]

theorem jump_sourceLength_next (program : JoltProgram)
    (layout : program.SequenceLayout)
    (i j : Fin program.expandedBytecode.size)
    (hnext : j.val = i.val + 1)
    (hcont : program.expandedBytecode[i].continues = true) :
    program.sourceLength layout i = program.sourceLength layout j := by
  obtain ⟨_, hrem, _, _⟩ := layout.next i j hnext hcont
  have hpositive : 0 < (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat := by
    have hne : program.expandedBytecode[i].virtualSequenceRemaining.getD 0 ≠ 0 := by
      simpa [JoltProgramRow.continues] using hcont
    exact BitVec.toNat_pos_of_ne_zero hne
  unfold JoltProgram.sourceLength
  have hlast :
      i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat =
      j.val + (program.expandedBytecode[j].virtualSequenceRemaining.getD 0).toNat := by
    rw [hrem]
    simp only [Option.getD_some]
    have hle : (1 : BitVec 16) ≤
        program.expandedBytecode[i].virtualSequenceRemaining.getD 0 := by
      rw [BitVec.le_def]
      simpa using hpositive
    rw [BitVec.toNat_sub_of_le hle]
    change i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat =
      j.val + ((program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat - 1)
    omega
  simp only [hlast]

theorem jump_sourceLength_at_end (program : JoltProgram)
    (layout : program.SequenceLayout) (i : Fin program.expandedBytecode.size)
    (hend : program.expandedBytecode[i].continues = false) :
    program.sourceLength layout i =
      if program.expandedBytecode[i].isCompressed then 2 else 4 := by
  have hzero : program.expandedBytecode[i].virtualSequenceRemaining.getD 0 = 0 := by
    simpa [JoltProgramRow.continues] using hend
  change program.expandedBytecode[i.val].virtualSequenceRemaining.getD (0#16) = 0#16 at hzero
  unfold JoltProgram.sourceLength
  simp [hzero]

theorem jump_trace_nextPC {program : JoltProgram} (trace : JoltTrace program)
    (n : Nat) (hn : n < trace.rows.size) :
    (trace.rows[n].preState.sail.regs.get? Register.nextPC) =
      some (program.expandedBytecode[trace.rows[n].rowIndex].address +
        BitVec.ofNat 64 (program.sourceLength trace.sequenceLayout trace.rows[n].rowIndex)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hstart := trace.startsAtInitial hn
      rw [hstart]
      exact jump_prepareSource_nextPC program trace.sequenceLayout _ _
    | succ m =>
      have hm : m < trace.rows.size := by omega
      have hp := ih m (by omega) hm
      have hlink := trace.linked m hm hn
      let prev := trace.rows[m]
      let curr := trace.rows[m + 1]
      by_cases hc : program.expandedBytecode[prev.rowIndex].continues = true
      · change program.expandedBytecode[trace.rows[m].rowIndex].continues = true at hc
        have hsucc := trace.successor m hm hn
        simp only [hc, ↓reduceIte] at hlink hsucc
        obtain ⟨haddr, _, _, _⟩ :=
          trace.sequenceLayout.next prev.rowIndex curr.rowIndex hsucc hc
        have hlen := jump_sourceLength_next program trace.sequenceLayout
          prev.rowIndex curr.rowIndex hsucc hc
        have hpres := trace.noEarlyNextPCChange prev.rowIndex hc
          prev.runtimeAdvice prev.preState prev.postState prev.executes
        change curr.preState.sail.regs.get? Register.nextPC = _
        rw [hlink, hpres]
        rw [hp, ← haddr, hlen]
      · change ¬ program.expandedBytecode[trace.rows[m].rowIndex].continues = true at hc
        simp only [if_neg hc] at hlink
        change curr.preState.sail.regs.get? Register.nextPC = _
        rw [hlink]
        exact jump_prepareSource_nextPC program trace.sequenceLayout curr.rowIndex _

theorem jump_sourceValue_after_write (rd : regidx) (value : BitVec 64)
    (preState : SailJoltState) (hnotzero : JoltISA.isX0 rd = false) :
    JoltISA.sourceValue (.xreg rd)
      { preState with sail := stateAfterWrite preState.sail rd value } = value := by
  reg_cases rd <;>
    simp_all [JoltISA.sourceValue, JoltISA.isX0, stateAfterWrite,
      wX_update_regs, regval_into_reg]

theorem jump_write_capture (dst : JoltISA.Dst) (imm : BitVec 21)
    (value : BitVec 64) (preState postState : SailJoltState)
    (hwritable : dst.NotX0)
    (hwrite : JoltISA.writeDst dst value preState =
      .ok () postState) :
    HonestWitness.capturedDestinationValue (.JAL dst imm) dst postState = value := by
  cases dst with
  | vreg vr =>
    by_cases hw : vr.toNat < 32
    · simp [JoltISA.writeDst, writeVReg, hw,
        throw, throwThe] at hwrite
      change EStateM.Result.error (Error.Assertion "writeVReg: architectural xreg address")
        preState = .ok () postState at hwrite
      cases hwrite
    · simp [JoltISA.writeDst, writeVReg, hw] at hwrite
      cases hwrite
      simp [HonestWitness.capturedDestinationValue, HonestWitness.capturedDestination,
        JoltISA.sourceValue]
  | xreg rd =>
    simp only [JoltISA.writeDst_xreg, liftSail, wX_bits_stateAfterWrite] at hwrite
    cases hwrite
    simpa only [HonestWitness.capturedDestinationValue,
      HonestWitness.capturedDestination] using
      jump_sourceValue_after_write rd value preState hwritable

theorem jump_capture_after_nextPC (instruction : JoltISA.Instr) (dst : JoltISA.Dst)
    (state : SailJoltState) (target : BitVec 64) :
    HonestWitness.capturedDestinationValue instruction dst
      { state with sail := { state.sail with
        regs := state.sail.regs.insert Register.nextPC target } } =
    HonestWitness.capturedDestinationValue instruction dst state := by
  unfold HonestWitness.capturedDestinationValue
  cases HonestWitness.capturedDestination instruction dst with
  | vreg vr => rfl
  | xreg rd =>
    reg_cases rd <;> simp_all [JoltISA.sourceValue, Std.ExtDHashMap.get?_insert]

theorem jump_jal_link (dst : JoltISA.Dst) (imm : BitVec 64)
    (link : BitVec 64) (preState postState : SailJoltState)
    (hwritable : dst.NotX0)
    (hnext : preState.sail.regs.get? Register.nextPC = some link)
    (hexec : JoltISA.execInstr (.JAL dst imm) preState =
      .ok (.Retire_Success ()) postState) :
    HonestWitness.capturedDestinationValue (.JAL dst imm) dst postState = link := by
  have hread : liftSail (Sail.readReg Register.nextPC) preState =
      .ok link preState := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC preState.sail link hnext]
  simp only [JoltISA.execInstr, bind, EStateM.bind, hread] at hexec
  cases hpc : Sail.readReg Register.PC preState.sail with
  | error err state =>
    have hpcLift : liftSail (Sail.readReg Register.PC) preState =
        .error err { preState with sail := state } := by
      simp [liftSail, hpc]
    simp only [hpcLift] at hexec
    cases hexec
  | ok pc state =>
    have hstate : state = preState.sail :=
      readReg_pure Register.PC preState.sail pc state hpc
    subst state
    have hpcLift : liftSail (Sail.readReg Register.PC) preState =
        .ok pc preState := by
      simp [liftSail, hpc]
    simp only [hpcLift] at hexec
    cases hwrite : JoltISA.writeDst dst link preState with
    | error err state =>
      simp only [hwrite] at hexec
      cases hexec
    | ok result mid =>
      cases result
      have hpcWrite : liftSail (Sail.writeReg Register.nextPC (pc + imm)) mid =
          .ok () { mid with sail := { mid.sail with
            regs := mid.sail.regs.insert Register.nextPC (pc + imm) } } := by
        rfl
      simp only [hwrite, hpcWrite, pure, EStateM.pure] at hexec
      cases hexec
      rw [jump_capture_after_nextPC]
      exact jump_write_capture dst (0#21) link preState mid hwritable hwrite

theorem jump_jalr_link (dst : JoltISA.Dst) (base : JoltISA.Src)
    (imm : BitVec 64) (link : BitVec 64) (preState postState : SailJoltState)
    (hwritable : dst.NotX0)
    (hnext : preState.sail.regs.get? Register.nextPC = some link)
    (hexec : JoltISA.execInstr (.JALR dst base imm) preState =
      .ok (.Retire_Success ()) postState) :
    HonestWitness.capturedDestinationValue (.JALR dst base imm) dst postState = link := by
  have hread : liftSail (Sail.readReg Register.nextPC) preState =
      .ok link preState := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC preState.sail link hnext]
  simp only [JoltISA.execInstr, bind, EStateM.bind, hread] at hexec
  cases hsrc : JoltISA.readSrc base preState with
  | error err state =>
    simp only [hsrc] at hexec
    cases hexec
  | ok source state =>
    simp only [hsrc] at hexec
    let target := jolt_jalr_target64 source imm
    let afterPC : SailJoltState :=
      { state with sail := { state.sail with
        regs := state.sail.regs.insert Register.nextPC target } }
    have hpcWrite : liftSail (Sail.writeReg Register.nextPC target) state =
        .ok () afterPC := by
      rfl
    rw [hpcWrite] at hexec
    cases hwrite : JoltISA.writeDst dst link afterPC with
    | error err final =>
      simp only [hwrite] at hexec
      cases hexec
    | ok writeUnit final =>
      cases writeUnit
      simp only [hwrite, pure, EStateM.pure] at hexec
      cases hexec
      exact jump_write_capture dst (0#21) link afterPC postState hwritable hwrite

theorem jump_jump_field {F : Type} [Field F] (address link : BitVec 64)
    (compressed : Bool)
    (hlink : link = address + BitVec.ofNat 64 (if compressed then 2 else 4))
    (hnoWrap : address.toNat + (if compressed then 2 else 4) < 2 ^ 64) :
    (link.toNat : F) - (address.toNat : F) - 4 +
      2 * (if compressed then (1 : F) else 0) = 0 := by
  have hnat : (BitVec.ofNat 64 (if compressed then 2 else 4)).toNat =
      (if compressed then 2 else 4) := by
    cases compressed <;> decide
  have hsum : link.toNat = address.toNat + (if compressed then 2 else 4) := by
    rw [hlink, BitVec.toNat_add_of_lt (by simpa only [hnat] using hnoWrap), hnat]
  rw [hsum]
  cases compressed <;> simp <;> ring
