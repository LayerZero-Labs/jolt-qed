import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Constraints.JumpReturnProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (14) in `constraints.md` (stage 1):
jumps write the return address, accounting for compressed instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqPCPlusConstIfJump {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Jump t *
      (witness.RdWriteValue t - witness.UnexpandedPC t - 4 +
        2 * witness.OpFlags .IsCompressed t) = 0

/-- Completeness under the program and trace conditions, including the
temporary no-early-nextPC-change and jump-at-source-end assumptions. -/
theorem honestWitness_rdWriteEqPCPlusConstIfJump
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rdWriteEqPCPlusConstIfJump
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]
    let bc := program.expandedBytecode[row.rowIndex]
    have hnext := jump_trace_nextPC trace t.val hb
    change row.preState.sail.regs.get? Register.nextPC =
      some (bc.address + BitVec.ofNat 64
        (program.sourceLength trace.sequenceLayout row.rowIndex)) at hnext
    by_cases hjump : JoltMetadata.circuitFlag bc .Jump = true
    · have hcases :
          (∃ (dst : JoltISA.Dst) (imm : BitVec 64), bc.expandedInstruction = .JAL dst imm) ∨
          (∃ (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64),
            bc.expandedInstruction = .JALR dst base imm) := by
        cases hinst : bc.expandedInstruction <;>
          simp [JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, hinst] at hjump ⊢
      rcases hcases with ⟨dst, imm, hinst⟩ | ⟨dst, base, imm, hinst⟩
      · have hinstNat : program.expandedBytecode[row.rowIndex.val].expandedInstruction =
            .JAL dst imm := by
          exact hinst
        have hwritable : dst.NotX0 :=
          row.validProgramRow.jal hinstNat
        have hexec : JoltISA.execInstr (.JAL dst imm) row.preState =
            .ok (.Retire_Success ()) row.postState := by
          simpa [JoltISA.Instr.withRuntimeAdvice, hinstNat] using row.executes
        have hcap : HonestWitness.capturedDestinationValue bc.expandedInstruction dst row.postState =
            bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex) := by
          rw [hinst]
          exact jump_jal_link dst imm _ row.preState row.postState hwritable hnext hexec
        have hend : bc.continues = false := by
          simpa [JoltProgram.JumpAtSourceEnd, hinstNat] using
            trace.jumpAtSourceEnd row.rowIndex
        have hlen := jump_sourceLength_at_end program trace.sequenceLayout
          row.rowIndex hend
        have hnoWrap : bc.address.toNat + (if bc.isCompressed then 2 else 4) < 2 ^ 64 := by
          have h := trace.sequenceLayout.addressAdvanceNoWrap row.rowIndex
          change bc.address.toNat +
            program.sourceLength trace.sequenceLayout row.rowIndex < 2 ^ 64 at h
          rw [hlen] at h
          exact h
        have hfield := jump_jump_field (F := F) bc.address
          (bc.address + BitVec.ofNat 64
            (program.sourceLength trace.sequenceLayout row.rowIndex)) bc.isCompressed
          (by rw [hlen]) hnoWrap
        have hcapNat : HonestWitness.capturedDestinationValue (.JAL dst imm) dst
            row.postState = bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex) := by
          simpa only [hinst] using hcap
        have hrd : HonestWitness.RdWriteValue (F := F) params trace t =
            ((bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex)).toNat : F) := by
          unfold HonestWitness.RdWriteValue
          simp only [dif_pos hb]
          change HonestWitness.rdValue (F := F)
            program.expandedBytecode[row.rowIndex.val].expandedInstruction row.postState = _
          rw [hinstNat]
          change ((HonestWitness.capturedDestinationValue (.JAL dst imm) dst
            row.postState).toNat : F) = _
          rw [hcapNat]
        have hpc : HonestWitness.UnexpandedPC (F := F) params trace t =
            (bc.address.toNat : F) := by
          simp [HonestWitness.UnexpandedPC, hb, bc, row]
        have hcomp : HonestWitness.OpFlags (F := F) params trace .IsCompressed t =
            (if bc.isCompressed then (1 : F) else 0) := by
          simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, hb, bc, row]
        have hflag : HonestWitness.OpFlags (F := F) params trace .Jump t = 1 := by
          unfold HonestWitness.OpFlags
          simp only [dif_pos hb]
          have hjumpNat : JoltMetadata.circuitFlag
              program.expandedBytecode[row.rowIndex.val] .Jump = true := by
            exact hjump
          change (if JoltMetadata.circuitFlag
            program.expandedBytecode[row.rowIndex.val] .Jump then (1 : F) else 0) = 1
          rw [hjumpNat]
          rfl
        simp only [JoltProgram.honestWitness]
        rw [hflag, hrd, hpc, hcomp]
        simpa using hfield
      · have hinstNat : program.expandedBytecode[row.rowIndex.val].expandedInstruction =
            .JALR dst base imm := by
          exact hinst
        have hwritable : dst.NotX0 :=
          row.validProgramRow.jalr hinstNat
        have hexec : JoltISA.execInstr (.JALR dst base imm) row.preState =
            .ok (.Retire_Success ()) row.postState := by
          simpa [JoltISA.Instr.withRuntimeAdvice, hinstNat] using row.executes
        have hcap : HonestWitness.capturedDestinationValue bc.expandedInstruction dst row.postState =
            bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex) := by
          rw [hinst]
          exact jump_jalr_link dst base imm _ row.preState row.postState hwritable hnext hexec
        have hend : bc.continues = false := by
          simpa [JoltProgram.JumpAtSourceEnd, hinstNat] using
            trace.jumpAtSourceEnd row.rowIndex
        have hlen := jump_sourceLength_at_end program trace.sequenceLayout
          row.rowIndex hend
        have hnoWrap : bc.address.toNat + (if bc.isCompressed then 2 else 4) < 2 ^ 64 := by
          have h := trace.sequenceLayout.addressAdvanceNoWrap row.rowIndex
          change bc.address.toNat +
            program.sourceLength trace.sequenceLayout row.rowIndex < 2 ^ 64 at h
          rw [hlen] at h
          exact h
        have hfield := jump_jump_field (F := F) bc.address
          (bc.address + BitVec.ofNat 64
            (program.sourceLength trace.sequenceLayout row.rowIndex)) bc.isCompressed
          (by rw [hlen]) hnoWrap
        have hcapNat : HonestWitness.capturedDestinationValue (.JALR dst base imm) dst
            row.postState = bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex) := by
          simpa only [hinst] using hcap
        have hrd : HonestWitness.RdWriteValue (F := F) params trace t =
            ((bc.address + BitVec.ofNat 64
              (program.sourceLength trace.sequenceLayout row.rowIndex)).toNat : F) := by
          unfold HonestWitness.RdWriteValue
          simp only [dif_pos hb]
          change HonestWitness.rdValue (F := F)
            program.expandedBytecode[row.rowIndex.val].expandedInstruction row.postState = _
          rw [hinstNat]
          change ((HonestWitness.capturedDestinationValue (.JALR dst base imm) dst
            row.postState).toNat : F) = _
          rw [hcapNat]
        have hpc : HonestWitness.UnexpandedPC (F := F) params trace t =
            (bc.address.toNat : F) := by
          simp [HonestWitness.UnexpandedPC, hb, bc, row]
        have hcomp : HonestWitness.OpFlags (F := F) params trace .IsCompressed t =
            (if bc.isCompressed then (1 : F) else 0) := by
          simp [HonestWitness.OpFlags, JoltMetadata.circuitFlag, hb, bc, row]
        have hflag : HonestWitness.OpFlags (F := F) params trace .Jump t = 1 := by
          unfold HonestWitness.OpFlags
          simp only [dif_pos hb]
          have hjumpNat : JoltMetadata.circuitFlag
              program.expandedBytecode[row.rowIndex.val] .Jump = true := by
            exact hjump
          change (if JoltMetadata.circuitFlag
            program.expandedBytecode[row.rowIndex.val] .Jump then (1 : F) else 0) = 1
          rw [hjumpNat]
          rfl
        simp only [JoltProgram.honestWitness]
        rw [hflag, hrd, hpc, hcomp]
        simpa using hfield
    · change ¬ JoltMetadata.circuitFlag
        program.expandedBytecode[(trace.rows[t.val]).rowIndex.val] .Jump = true at hjump
      simp [JoltProgram.honestWitness, HonestWitness.OpFlags, hb, hjump]
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags, hb]

end JoltConstraints
