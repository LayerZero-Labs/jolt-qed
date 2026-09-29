import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

private theorem virtual_flag_eq_last_of_not_continues (row : JoltProgramRow)
    (h : row.continues = false) :
    JoltMetadata.circuitFlag row .VirtualInstruction =
      JoltMetadata.circuitFlag row .IsLastInSequence := by
  cases hs : row.virtualSequenceRemaining with
  | none => simp [JoltMetadata.circuitFlag, hs]
  | some n =>
      have hn : n = 0 := by
        simp [JoltProgramRow.continues, hs] at h
        simpa using h
      subst n
      simp [JoltMetadata.circuitFlag, hs]

/-- Constraint (18) in `constraints.md` (stage 1):
nonterminal virtual-sequence rows advance the expanded PC by one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextPCEqPCPlusOneIfInline {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .VirtualInstruction t - witness.OpFlags .IsLastInSequence t) *
      (witness.NextPC t - witness.PC t - 1) = 0

/-- Completeness target for a complete Rust trace, with its mandatory padding.
`Terminated` includes every opcode allowed by Rust's repeated-PC stopping rule.
There is no jump-only or nonwrapping-arithmetic assumption. -/
theorem honestWitness_nextPCEqPCPlusOneIfInline
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    nextPCEqPCPlusOneIfInline
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain) := by
  intro t
  by_cases ht : t.val < trace.rows.size
  · let row := getElem trace.rows t.val ht
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    by_cases hcont : bytecodeRow.continues = true
    · have hnext : t.val + 1 < trace.rows.size := by
        by_contra hn
        have hlast : t.val = trace.rows.size - 1 := by
          have := terminated.nonempty
          omega
        have hterm := terminated.atSourceEnd
        change (getElem program.expandedBytecode
          (getElem trace.rows (trace.rows.size - 1) (by omega)).rowIndex.val
          (getElem trace.rows (trace.rows.size - 1) (by omega)).rowIndex.isLt).continues = false at hterm
        have hterm' : bytecodeRow.continues = false := by
          simpa only [← hlast, bytecodeRow, row] using hterm
        exact Bool.false_ne_true (hterm'.symm.trans hcont)
      have hsucc := trace.successor t.val ht hnext
      change (if bytecodeRow.continues then
        (getElem trace.rows (t.val + 1) hnext).rowIndex.val = row.rowIndex.val + 1
        else _) at hsucc
      simp only [hcont, ↓reduceIte] at hsucc
      have hnextWitness : t.val + 1 < params.traceLength :=
        hnext.trans tracePadded.2
      have hpc : HonestWitness.NextPC (F := F) params trace t =
          HonestWitness.PC params trace t + 1 := by
        simp only [HonestWitness.NextPC, dif_pos hnextWitness, HonestWitness.PC,
          HonestWitness.bytecodePc, dif_pos ht, dif_pos hnext]
        rw [hsucc]
        push_cast
        ring
      dsimp [nextPCEqPCPlusOneIfInline, JoltProgram.honestWitness]
      rw [hpc]
      ring
    · have hfalse : bytecodeRow.continues = false := Bool.eq_false_iff.mpr hcont
      have hflags := virtual_flag_eq_last_of_not_continues bytecodeRow hfalse
      dsimp [nextPCEqPCPlusOneIfInline, JoltProgram.honestWitness,
        HonestWitness.OpFlags]
      simp only [dif_pos ht]
      rw [hflags]
      ring
  · simp [JoltProgram.honestWitness,
      HonestWitness.OpFlags, ht]

end JoltConstraints
