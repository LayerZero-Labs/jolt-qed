import JoltConstraints.Completeness.Helpers.RegistersValHistoryProofHelpers
import JoltConstraints.Constraints.RdWriteValueEqRegistersReadWrite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Completeness.Helpers.RegistersValHistoryProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_rdWriteValueEqRegistersReadWrite
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0) :
    rdWriteValueEqRegistersReadWrite
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.RdWriteValue params trace t =
    ∑ register : Fin 128,
      TraceWitness.RdWa params trace register t *
        (TraceWitness.RegistersVal params trace register t + TraceWitness.RdInc params trace t)
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]'hb
    let instr := trace.bytecode[row.rowIndex].instruction
    have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
      trace.registerOperandsCanonical row.rowIndex
    have hwa := register42_RdWa_real (F := F) params trace t hb
    change ∀ register, TraceWitness.RdWa (F := F) params trace register t =
      match instr.destination? with
      | some dst => if register = TraceWitness.destinationRegisterAddress dst then 1 else 0
      | none => 0 at hwa
    have hinc : TraceWitness.RdInc (F := F) params trace t =
        TraceWitness.rdValue instr row.postState -
          TraceWitness.rdValue instr row.preState := by
      unfold TraceWitness.RdInc
      simp only [dif_pos hb]
      rfl
    have hwrite : TraceWitness.RdWriteValue (F := F) params trace t =
        TraceWitness.rdValue instr row.postState := by
      unfold TraceWitness.RdWriteValue
      simp only [dif_pos hb]
      rfl
    simp only [hwa]
    rw [hwrite, register42_rdValue_eq_destination]
    cases hd : instr.destination? with
    | none => simp
    | some dst =>
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (TraceWitness.destinationRegisterAddress dst)]
        simp only [Finset.mem_univ, ↓reduceIte]
        have hpre := register42_registersVal_preState (F := F) params trace traceFits
          initialRegistersZero (TraceWitness.destinationRegisterAddress dst) t.val hb
        rw [register42_srcOfDestinationAddress dst
          (register42_instruction_destination_canonical instr dst hcanon hd)] at hpre
        change TraceWitness.RegistersVal (F := F) params trace
          (TraceWitness.destinationRegisterAddress dst) t = _ at hpre
        rw [hpre, hinc, register42_rdValue_eq_destination,
          register42_rdValue_eq_destination, hd]
        ring
  · simp [TraceWitness.RdWriteValue, TraceWitness.RdWa, hb]

end JoltConstraints
