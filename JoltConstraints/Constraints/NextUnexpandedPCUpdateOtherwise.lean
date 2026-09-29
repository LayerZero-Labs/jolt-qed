import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Constraints.SailByteReadFrame

set_option autoImplicit false

namespace JoltConstraints

private theorem shouldBranch_eq_branchTaken
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (t : Fin params.traceLength) (ht : t.val < trace.rows.size) :
    HonestWitness.ShouldBranch (F := F) params trace t =
      if JoltNextPCFrame.BranchTaken
          program.expandedBytecode[(trace.rows[t.val]'ht).rowIndex].expandedInstruction
          (trace.rows[t.val]'ht).preState then 1 else 0 := by
  simp only [HonestWitness.ShouldBranch, dif_pos ht]
  generalize hi :
    program.expandedBytecode[(trace.rows[t.val]'ht).rowIndex].expandedInstruction = instr
  cases instr <;> rfl

private theorem branchTaken_withRuntimeAdvice (instr : JoltISA.Instr)
    (advice : instr.RuntimeAdvice) (s : SailJoltState) :
    JoltNextPCFrame.BranchTaken (instr.withRuntimeAdvice advice) s =
      JoltNextPCFrame.BranchTaken instr s := by
  cases instr <;> rfl

private theorem jumpFlag_withRuntimeAdvice (instr : JoltISA.Instr)
    (advice : instr.RuntimeAdvice) :
    JoltMetadata.opcodeFlag (instr.withRuntimeAdvice advice) .Jump =
      JoltMetadata.opcodeFlag instr .Jump := by
  cases instr <;> rfl

private theorem branchTaken_false_of_jump (instr : JoltISA.Instr)
    (s : SailJoltState)
    (hjump : JoltMetadata.opcodeFlag instr .Jump = true) :
    JoltNextPCFrame.BranchTaken instr s = false := by
  cases instr <;> simp_all [JoltMetadata.opcodeFlag, JoltNextPCFrame.BranchTaken]

private theorem sourceEnd_noWrap (program : JoltProgram)
    (layout : program.SequenceLayout)
    (i : Fin program.expandedBytecode.size)
    (hend : program.expandedBytecode[i].continues = false) :
    program.expandedBytecode[i].address.toNat +
      (if program.expandedBytecode[i].isCompressed then 2 else 4) < 2 ^ 64 := by
  have hzero : program.expandedBytecode[i].virtualSequenceRemaining.getD 0 = 0 := by
    simpa [JoltProgramRow.continues] using hend
  have hzeroNat : (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat = 0 := by
    change program.expandedBytecode[i.val].virtualSequenceRemaining.getD (0#16) = 0#16
      at hzero
    change (program.expandedBytecode[i.val].virtualSequenceRemaining.getD (0#16)).toNat = 0
    rw [hzero]
    rfl
  have h := layout.addressAdvanceNoWrap i
  simpa only [hzeroNat, Nat.add_zero] using h

private theorem advance_ne_self (address : BitVec 64) (compressed : Bool) :
    address + BitVec.ofNat 64 (if compressed then 2 else 4) ≠ address := by
  intro h
  have hzero : BitVec.ofNat 64 (if compressed then 2 else 4) = 0 := by
    apply add_left_cancel (a := address)
    simpa using h
  cases compressed
  · exact (by decide : (4#64 : BitVec 64) ≠ 0) hzero
  · exact (by decide : (2#64 : BitVec 64) ≠ 0) hzero

private theorem sourceEnd_has_next_of_frame
    {program : JoltProgram} (trace : JoltTrace program)
    (terminated : trace.Terminated)
    (n : Nat) (hn : n < trace.rows.size)
    (hend : program.expandedBytecode[trace.rows[n].rowIndex].continues = false)
    (hframe : trace.rows[n].postState.sail.regs.get? Register.nextPC =
      trace.rows[n].preState.sail.regs.get? Register.nextPC) :
    n + 1 < trace.rows.size := by
  by_contra hnext
  have hlast : n = trace.rows.size - 1 := by omega
  have hpre := jump_trace_nextPC trace n hn
  rw [jump_sourceLength_at_end program trace.sequenceLayout trace.rows[n].rowIndex hend] at hpre
  have hpost := terminated.repeatedPC
  simp only [← hlast] at hpost
  rw [hframe, hpre] at hpost
  exact advance_ne_self _ _ (Option.some.inj hpost)

private theorem nextUnexpandedPC_eq_current_of_continues
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (t : Fin params.traceLength) (ht : t.val < trace.rows.size)
    (hcont : program.expandedBytecode[(trace.rows[t.val]'ht).rowIndex].continues = true) :
    HonestWitness.NextUnexpandedPC (F := F) params trace t =
      HonestWitness.UnexpandedPC (F := F) params trace t := by
  have hnext : t.val + 1 < trace.rows.size := by
    by_contra hn
    have hlast : t.val = trace.rows.size - 1 := by
      have := terminated.nonempty
      omega
    have hend := terminated.atSourceEnd
    have hend' :
        program.expandedBytecode[(trace.rows[t.val]'ht).rowIndex].continues = false := by
      simpa only [← hlast] using hend
    exact Bool.false_ne_true (hend'.symm.trans hcont)
  have hnextWitness : t.val + 1 < params.traceLength :=
    hnext.trans tracePadded.2
  have hsucc := trace.successor t.val ht hnext
  simp only [hcont, ↓reduceIte] at hsucc
  obtain ⟨haddr, _, _, _⟩ := trace.sequenceLayout.next
    (trace.rows[t.val]'ht).rowIndex
    (trace.rows[t.val + 1]'hnext).rowIndex hsucc hcont
  simp only [HonestWitness.NextUnexpandedPC, dif_pos hnextWitness,
    HonestWitness.UnexpandedPC, dif_pos hnext, dif_pos ht]
  exact congrArg (fun address : BitVec 64 => (address.toNat : F)) haddr

/-- Constraint (17) in `constraints.md` (stage 1):
the remaining rows advance or preserve the unexpanded PC according to their flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCUpdateOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.ShouldBranch t - witness.OpFlags .Jump t) *
      (witness.NextUnexpandedPC t - witness.UnexpandedPC t - 4 +
        4 * witness.OpFlags .DoNotUpdateUnexpandedPC t +
        2 * witness.OpFlags .IsCompressed t) = 0

/-- Completeness target for a complete Rust trace, with its mandatory padding.
`Terminated` includes every opcode allowed by Rust's repeated-PC stopping rule.
There is no jump-only premise. The trace's existing `SequenceLayout` includes
`addressAdvanceNoWrap`, a temporary assumption pending Jolt issue #1949.
The proof derives the final-row nextPC frame from `row.executes` and the
existing assumption bundle, including live HostIO byte reads. -/
theorem honestWitness_nextUnexpandedPCUpdateOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    nextUnexpandedPCUpdateOtherwise
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain) := by
  intro t
  change (1 - HonestWitness.ShouldBranch (F := F) params trace t -
      HonestWitness.OpFlags (F := F) params trace .Jump t) *
    (HonestWitness.NextUnexpandedPC (F := F) params trace t -
      HonestWitness.UnexpandedPC (F := F) params trace t - 4 +
      4 * HonestWitness.OpFlags (F := F) params trace .DoNotUpdateUnexpandedPC t +
      2 * HonestWitness.OpFlags (F := F) params trace .IsCompressed t) = 0
  by_cases ht : t.val < trace.rows.size
  · let row := trace.rows[t.val]
    let bc := program.expandedBytecode[row.rowIndex]
    by_cases hcont : bc.continues = true
    · have hnextEq := nextUnexpandedPC_eq_current_of_continues (F := F)
        params trace terminated tracePadded t ht hcont
      have hpositive : 0 < (bc.virtualSequenceRemaining.getD 0).toNat := by
        have hne : bc.virtualSequenceRemaining.getD 0 ≠ 0 := by
          simpa [JoltProgramRow.continues] using hcont
        exact BitVec.toNat_pos_of_ne_zero hne
      have hnextIndex : row.rowIndex.val + 1 < program.expandedBytecode.size := by
        have hend := trace.sequenceLayout.endInBounds row.rowIndex
        change row.rowIndex.val + (bc.virtualSequenceRemaining.getD 0).toNat <
          program.expandedBytecode.size at hend
        omega
      have hcompressed : bc.isCompressed = false := by
        obtain ⟨_, _, _, h⟩ := trace.sequenceLayout.next row.rowIndex
          ⟨row.rowIndex.val + 1, hnextIndex⟩ rfl hcont
        exact h
      have hstay : HonestWitness.OpFlags (F := F) params trace
          .DoNotUpdateUnexpandedPC t = 1 := by
        simp [HonestWitness.OpFlags, ht, JoltMetadata.circuitFlag,
          JoltProgramRow.continues] at hcont ⊢
        exact hcont
      have hshort : HonestWitness.OpFlags (F := F) params trace
          .IsCompressed t = 0 := by
        change program.expandedBytecode[(trace.rows[t.val]'ht).rowIndex.val].isCompressed = false
          at hcompressed
        simp [HonestWitness.OpFlags, ht, JoltMetadata.circuitFlag, hcompressed]
      rw [hnextEq, hstay, hshort]
      ring
    · have hend : bc.continues = false := by
        cases h : bc.continues <;> simp_all
      have hJumpField : HonestWitness.OpFlags (F := F) params trace .Jump t =
          if JoltMetadata.opcodeFlag bc.expandedInstruction .Jump then 1 else 0 := by
        simp [HonestWitness.OpFlags, ht, JoltMetadata.circuitFlag, row, bc]
      have hShouldField : HonestWitness.ShouldBranch (F := F) params trace t =
          if JoltNextPCFrame.BranchTaken bc.expandedInstruction row.preState
            then 1 else 0 := by
        exact shouldBranch_eq_branchTaken params trace t ht
      have hStayField : HonestWitness.OpFlags (F := F) params trace
          .DoNotUpdateUnexpandedPC t = 0 := by
        simp [HonestWitness.OpFlags, ht, JoltMetadata.circuitFlag,
          JoltProgramRow.continues] at hend ⊢
        exact hend
      have hCompressedField : HonestWitness.OpFlags (F := F) params trace
          .IsCompressed t = if bc.isCompressed then 1 else 0 := by
        simp [HonestWitness.OpFlags, ht, JoltMetadata.circuitFlag, row, bc]
      by_cases hjump : JoltMetadata.opcodeFlag bc.expandedInstruction .Jump = true
      · have hnotBranch := branchTaken_false_of_jump bc.expandedInstruction
          row.preState hjump
        rw [hShouldField, hJumpField]
        simp [hjump, hnotBranch]
      · have hnoJump : JoltMetadata.opcodeFlag bc.expandedInstruction .Jump = false := by
          cases h : JoltMetadata.opcodeFlag bc.expandedInstruction .Jump <;> simp_all
        by_cases hbranch : JoltNextPCFrame.BranchTaken
            bc.expandedInstruction row.preState = true
        · rw [hShouldField, hJumpField]
          simp [hbranch, hnoJump]
        · have hnoBranch : JoltNextPCFrame.BranchTaken
              bc.expandedInstruction row.preState = false := by
            cases h : JoltNextPCFrame.BranchTaken bc.expandedInstruction row.preState <;>
              simp_all
          have hframe : row.postState.sail.regs.get? Register.nextPC =
              row.preState.sail.regs.get? Register.nextPC := by
            apply JoltNextPCFrame.row trace ⟨t.val, ht⟩
            · rw [jumpFlag_withRuntimeAdvice]
              exact hnoJump
            · rw [branchTaken_withRuntimeAdvice]
              exact hnoBranch
          have hnext : t.val + 1 < trace.rows.size :=
            sourceEnd_has_next_of_frame trace terminated t.val ht hend hframe
          have hnextPadded : t.val + 1 < params.traceLength :=
            hnext.trans tracePadded.2
          have hpre := jump_trace_nextPC trace t.val ht
          rw [jump_sourceLength_at_end program trace.sequenceLayout row.rowIndex hend]
            at hpre
          have hsucc := trace.successor t.val ht hnext
          have hc : program.expandedBytecode[trace.rows[t.val].rowIndex].continues = false := by
            simpa [row, bc] using hend
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsucc
          obtain ⟨hsuccPC, _, _⟩ := hsucc
          have hlink : program.expandedBytecode[(trace.rows[t.val + 1]'hnext).rowIndex].address =
              bc.address + BitVec.ofNat 64 (if bc.isCompressed then 2 else 4) := by
            rw [hframe, hpre] at hsuccPC
            exact (Option.some.inj hsuccPC).symm
          have hnoWrap := sourceEnd_noWrap program trace.sequenceLayout row.rowIndex hend
          have hfield := jump_jump_field (F := F) bc.address
            program.expandedBytecode[(trace.rows[t.val + 1]'hnext).rowIndex].address
            bc.isCompressed hlink hnoWrap
          have hCurrent : HonestWitness.UnexpandedPC (F := F) params trace t =
              (bc.address.toNat : F) := by
            simp [HonestWitness.UnexpandedPC, ht, row, bc]
          have hNext : HonestWitness.NextUnexpandedPC (F := F) params trace t =
              (program.expandedBytecode[(trace.rows[t.val + 1]'hnext).rowIndex].address.toNat : F) := by
            simp [HonestWitness.NextUnexpandedPC, HonestWitness.UnexpandedPC,
              hnextPadded, hnext]
          rw [hShouldField, hJumpField, hStayField, hCompressedField,
            hCurrent, hNext]
          simpa [hnoBranch, hnoJump] using hfield
  · have hnextNot : ¬ t.val + 1 < trace.rows.size := by omega
    simp [HonestWitness.ShouldBranch, HonestWitness.OpFlags,
      HonestWitness.NextUnexpandedPC, HonestWitness.UnexpandedPC, ht, hnextNot]

end JoltConstraints
