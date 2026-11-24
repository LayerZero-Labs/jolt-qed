import JoltConstraints.theorems.execution_conditions
import JoltConstraints.theorems.Completeness.Helpers.LookupWriteProofHelpers
import JoltConstraints.translation.Constraints.RdWriteEqPCPlusConstIfJump
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.execution_conditions
import JoltConstraints.theorems.Completeness.Helpers.JumpReturnProofHelpers
import JoltConstraints.theorems.witness_domain
import JoltConstraints.theorems.HaltFlags

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness under the trace and trace conditions, including the
temporary no-early-nextPC-change and jump-at-source-end assumptions. -/
theorem honestWitness_rdWriteEqPCPlusConstIfJump
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (noWrap : joltInstance.program.NextPCNoWrap) :
    rdWriteEqPCPlusConstIfJump
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases hb : t.val < trace.rows.size
  · let row := trace.row t.val (by omega)
    let bc := trace.bytecode[row.rowIndex.val]
    have hnext := jump_trace_nextPC trace t.val hb
    change row.preState.sail.regs.get? Register.nextPC =
      some (bc.address + BitVec.ofNat 64
        (sourceLength trace.bytecode row.rowIndex)) at hnext
    have execution := row.executes
    change JoltISA.execInstr (bc.instruction.withRuntimeAdvice row.runtimeAdvice) row.preState =
      .ok (.Retire_Success ()) row.postState at execution
    have sourceEnd := (trace.rowValid row.rowIndex).jumpAtSourceEnd
    change (match bc.instruction with
      | .JAL _ _ | .JALR _ _ _ => bc.continues = false
      | _ => True) at sourceEnd
    by_cases hjump : JoltMetadata.circuitFlag bc .Jump = true
    · have hcases := JoltMetadata.jumpCases bc.instruction (by
        simpa only [JoltMetadata.circuitFlag] using hjump)
      have linkAndEnd :
          TraceWitness.rdValue (F := F) bc.instruction row.postState =
            ((bc.address + BitVec.ofNat 64
              (sourceLength trace.bytecode row.rowIndex)).toNat : F) ∧
          bc.continues = false := by
        rcases hcases with ⟨dst, imm, hinst⟩ | ⟨dst, base, imm, hinst⟩ |
          ⟨kind, dst, hinst⟩
        · have writable := (trace.rowValid row.rowIndex).jal hinst
          have runs : JoltISA.execInstr (.JAL dst imm) row.preState =
              .ok (.Retire_Success ()) row.postState := by
            simpa [JoltISA.Instr.withRuntimeAdvice, hinst] using execution
          have capture := jump_jal_link dst imm _ row.preState row.postState
            writable hnext runs
          refine ⟨?_, ?_⟩
          · simpa only [hinst, TraceWitness.rdValue] using congrArg
              (fun value : BitVec 64 => (value.toNat : F)) capture
          · simpa [hinst] using sourceEnd
        · have writable := (trace.rowValid row.rowIndex).jalr hinst
          have runs : JoltISA.execInstr (.JALR dst base imm) row.preState =
              .ok (.Retire_Success ()) row.postState := by
            simpa [JoltISA.Instr.withRuntimeAdvice, hinst] using execution
          have capture := jump_jalr_link dst base imm _ row.preState row.postState
            writable hnext runs
          refine ⟨?_, ?_⟩
          · simpa only [hinst, TraceWitness.rdValue] using congrArg
              (fun value : BitVec 64 => (value.toNat : F)) capture
          · simpa [hinst] using sourceEnd
        · have destination : bc.instruction.destination? = some dst := by
            cases kind <;> simp [hinst, JoltISA.Instr.destination?]
          have notNoop : bc.instruction ≠ JoltISA.Instr.canonicalNoOp := by
            cases kind <;> simp [hinst, JoltISA.Instr.canonicalNoOp]
          have writable := lookup_destination_writable bc (trace.rowValid row.rowIndex)
            notNoop dst destination
          have runs : JoltISA.execHalt kind dst row.preState =
              .ok (.Retire_Success ()) row.postState := by
            cases kind <;> simpa [JoltISA.Instr.withRuntimeAdvice, hinst,
              JoltISA.execInstr] using execution
          have capture := jump_halt_link kind dst _ row.preState row.postState
            writable hnext runs
          have halts : (trace.rows[t.val]'hb).Halts := by
            change bc.instruction.haltKind?.isSome = true
            cases kind <;> simp [hinst, JoltISA.Instr.haltKind?]
          have terminal := (trace.halt_row t.val hb halts).1
          refine ⟨?_, ?_⟩
          · cases kind <;> simpa only [hinst, TraceWitness.rdValue] using congrArg
              (fun value : BitVec 64 => (value.toNat : F)) capture
          · simp only [JoltInstructionRow.continues,
              show bc.virtual_sequence_remaining.getD 0 = 0 from terminal]
            rfl
      have hlen := jump_sourceLength_at_end trace row.rowIndex linkAndEnd.2
      change sourceLength trace.bytecode row.rowIndex =
        (if bc.is_compressed then 2 else 4) at hlen
      have hnoWrap : bc.address.toNat + (if bc.is_compressed then 2 else 4) < 2 ^ 64 := by
        have h := trace.next_pc_no_wrap noWrap row.rowIndex
        change bc.address.toNat + sourceLength trace.bytecode row.rowIndex < 2 ^ 64 at h
        rwa [hlen] at h
      have hfield := jump_jump_field (F := F) bc.address
        (bc.address + BitVec.ofNat 64 (sourceLength trace.bytecode row.rowIndex))
        bc.is_compressed (by rw [hlen]) hnoWrap
      have hrd : TraceWitness.RdWriteValue (F := F) params trace t =
          ((bc.address + BitVec.ofNat 64
            (sourceLength trace.bytecode row.rowIndex)).toNat : F) := by
        unfold TraceWitness.RdWriteValue
        simp only [dite_eq_left hb]
        exact linkAndEnd.1
      have hpc : TraceWitness.UnexpandedPC (F := F) params trace t =
          (bc.address.toNat : F) := by
        simp [TraceWitness.UnexpandedPC, hb, bc, row]
      have hcomp : TraceWitness.OpFlags (F := F) params trace .IsCompressed t =
          (if bc.is_compressed then (1 : F) else 0) := by
        simp [TraceWitness.OpFlags, JoltMetadata.circuitFlag, hb, bc, row]; rfl
      have hflag : TraceWitness.OpFlags (F := F) params trace .Jump t = 1 := by
        unfold TraceWitness.OpFlags
        simp only [dite_eq_left hb]
        change (if JoltMetadata.circuitFlag bc .Jump then (1 : F) else 0) = 1
        rw [hjump]
        rfl
      simp only [HonestTrace.honestWitness]
      rw [hflag, hrd, hpc, hcomp]
      simpa using hfield
    · change ¬ JoltMetadata.circuitFlag
        trace.bytecode[(trace.rows[t.val]).rowIndex.val] .Jump = true at hjump
      simp [HonestTrace.honestWitness, TraceWitness.OpFlags, hb, hjump]
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags, hb]

end JoltConstraints
