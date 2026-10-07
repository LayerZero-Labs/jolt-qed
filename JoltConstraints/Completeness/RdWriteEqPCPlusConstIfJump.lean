import JoltConstraints.Constraints.RdWriteEqPCPlusConstIfJump
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Constraints.JumpReturnProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness under the trace and trace conditions, including the
temporary no-early-nextPC-change and jump-at-source-end assumptions. -/
theorem honestWitness_rdWriteEqPCPlusConstIfJump
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (noWrap : joltInstance.program.NextPCNoWrap) :
    rdWriteEqPCPlusConstIfJump
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]
    let bc := trace.bytecode[row.rowIndex]
    have hnext := jump_trace_nextPC trace t.val hb
    change row.preState.sail.regs.get? Register.nextPC =
      some (bc.address + BitVec.ofNat 64
        (sourceLength trace.bytecode row.rowIndex)) at hnext
    by_cases hjump : JoltMetadata.circuitFlag bc .Jump = true
    · have hcases :
          (∃ (dst : JoltISA.Dst) (imm : BitVec 64), bc.instruction = .JAL dst imm) ∨
          (∃ (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64),
            bc.instruction = .JALR dst base imm) := by
        cases hinst : bc.instruction <;>
          simp [JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, hinst] at hjump ⊢
      rcases hcases with ⟨dst, imm, hinst⟩ | ⟨dst, base, imm, hinst⟩
      · have hinstNat : trace.bytecode[row.rowIndex.val].instruction =
            .JAL dst imm := by
          exact hinst
        have hwritable : dst.NotX0 :=
          (trace.rowValid row.rowIndex).jal hinstNat
        have hexec : JoltISA.execInstr (.JAL dst imm) row.preState =
            .ok (.Retire_Success ()) row.postState := by
          simpa [JoltISA.Instr.withRuntimeAdvice, hinstNat] using row.executes
        have hcap : HonestWitness.capturedDestinationValue dst row.postState = bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex) := by
          exact jump_jal_link dst imm _ row.preState row.postState hwritable hnext hexec
        have hend : bc.continues = false := by
          simpa [hinstNat] using (trace.rowValid row.rowIndex).jumpAtSourceEnd
        have hlen := jump_sourceLength_at_end trace
          row.rowIndex hend
        have hnoWrap : bc.address.toNat + (if bc.is_compressed then 2 else 4) < 2 ^ 64 := by
          have h := trace.next_pc_no_wrap noWrap row.rowIndex
          change bc.address.toNat +
            sourceLength trace.bytecode row.rowIndex < 2 ^ 64 at h
          rw [hlen] at h
          exact h
        have hfield := jump_jump_field (F := F) bc.address
          (bc.address + BitVec.ofNat 64
            (sourceLength trace.bytecode row.rowIndex)) bc.is_compressed
          (by rw [hlen]) hnoWrap
        have hcapNat : HonestWitness.capturedDestinationValue dst
            row.postState = bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex) := by
          exact hcap
        have hrd : HonestWitness.RdWriteValue (F := F) params trace t =
            ((bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex)).toNat : F) := by
          unfold HonestWitness.RdWriteValue
          simp only [dif_pos hb]
          change HonestWitness.rdValue (F := F)
            trace.bytecode[row.rowIndex.val].instruction row.postState = _
          rw [hinstNat]
          change ((HonestWitness.capturedDestinationValue dst row.postState).toNat : F) = _
          rw [hcapNat]
        have hpc : HonestWitness.UnexpandedPC (F := F) params trace t =
            (bc.address.toNat : F) := by
          simp [HonestWitness.UnexpandedPC, hb, bc, row]
        have hcomp : HonestWitness.OpFlags (F := F) params trace .IsCompressed t =
            (if bc.is_compressed then (1 : F) else 0) := by
          simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, hb, bc, row]
        have hflag : HonestWitness.OpFlags (F := F) params trace .Jump t = 1 := by
          unfold HonestWitness.OpFlags
          simp only [dif_pos hb]
          have hjumpNat : JoltMetadata.circuitFlag
              trace.bytecode[row.rowIndex.val] .Jump = true := by
            exact hjump
          change (if JoltMetadata.circuitFlag
            trace.bytecode[row.rowIndex.val] .Jump then (1 : F) else 0) = 1
          rw [hjumpNat]
          rfl
        simp only [HonestTrace.honestWitness]
        rw [hflag, hrd, hpc, hcomp]
        simpa using hfield
      · have hinstNat : trace.bytecode[row.rowIndex.val].instruction =
            .JALR dst base imm := by
          exact hinst
        have hwritable : dst.NotX0 :=
          (trace.rowValid row.rowIndex).jalr hinstNat
        have hexec : JoltISA.execInstr (.JALR dst base imm) row.preState =
            .ok (.Retire_Success ()) row.postState := by
          simpa [JoltISA.Instr.withRuntimeAdvice, hinstNat] using row.executes
        have hcap : HonestWitness.capturedDestinationValue dst row.postState =
            bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex) := by
          exact jump_jalr_link dst base imm _ row.preState row.postState hwritable hnext hexec
        have hend : bc.continues = false := by
          simpa [hinstNat] using (trace.rowValid row.rowIndex).jumpAtSourceEnd
        have hlen := jump_sourceLength_at_end trace
          row.rowIndex hend
        have hnoWrap : bc.address.toNat + (if bc.is_compressed then 2 else 4) < 2 ^ 64 := by
          have h := trace.next_pc_no_wrap noWrap row.rowIndex
          change bc.address.toNat +
            sourceLength trace.bytecode row.rowIndex < 2 ^ 64 at h
          rw [hlen] at h
          exact h
        have hfield := jump_jump_field (F := F) bc.address
          (bc.address + BitVec.ofNat 64
            (sourceLength trace.bytecode row.rowIndex)) bc.is_compressed
          (by rw [hlen]) hnoWrap
        have hcapNat : HonestWitness.capturedDestinationValue dst
            row.postState = bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex) := by
          exact hcap
        have hrd : HonestWitness.RdWriteValue (F := F) params trace t =
            ((bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex)).toNat : F) := by
          unfold HonestWitness.RdWriteValue
          simp only [dif_pos hb]
          change HonestWitness.rdValue (F := F)
            trace.bytecode[row.rowIndex.val].instruction row.postState = _
          rw [hinstNat]
          change ((HonestWitness.capturedDestinationValue dst row.postState).toNat : F) = _
          rw [hcapNat]
        have hpc : HonestWitness.UnexpandedPC (F := F) params trace t =
            (bc.address.toNat : F) := by
          simp [HonestWitness.UnexpandedPC, hb, bc, row]
        have hcomp : HonestWitness.OpFlags (F := F) params trace .IsCompressed t =
            (if bc.is_compressed then (1 : F) else 0) := by
          simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, hb, bc, row]
        have hflag : HonestWitness.OpFlags (F := F) params trace .Jump t = 1 := by
          unfold HonestWitness.OpFlags
          simp only [dif_pos hb]
          have hjumpNat : JoltMetadata.circuitFlag
              trace.bytecode[row.rowIndex.val] .Jump = true := by
            exact hjump
          change (if JoltMetadata.circuitFlag
            trace.bytecode[row.rowIndex.val] .Jump then (1 : F) else 0) = 1
          rw [hjumpNat]
          rfl
        simp only [HonestTrace.honestWitness]
        rw [hflag, hrd, hpc, hcomp]
        simpa using hfield
    · change ¬ JoltMetadata.circuitFlag
        trace.bytecode[(trace.rows[t.val]).rowIndex.val] .Jump = true at hjump
      simp [HonestTrace.honestWitness, HonestWitness.OpFlags, hb, hjump]
  · simp [HonestTrace.honestWitness, HonestWitness.OpFlags, hb]

end JoltConstraints
