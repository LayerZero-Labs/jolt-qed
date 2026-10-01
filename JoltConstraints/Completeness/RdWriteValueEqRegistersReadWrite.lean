import JoltConstraints.Constraints.RdWriteValueEqRegistersReadWrite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RegistersValHistoryProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_rdWriteValueEqRegistersReadWrite
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0) :
    rdWriteValueEqRegistersReadWrite
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.RdWriteValue params trace t =
    ∑ register : Fin 128,
      HonestWitness.RdWa params trace register t *
        (HonestWitness.RegistersVal params trace register t + HonestWitness.RdInc params trace t)
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]'hb
    let instr := program.expandedBytecode[row.rowIndex].expandedInstruction
    have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
      program.expandedBytecode[row.rowIndex].registerOperandsCanonical
    have hwa := register42_RdWa_real (F := F) params trace t hb
    change ∀ register, HonestWitness.RdWa (F := F) params trace register t =
      match instr.destination? with
      | some dst => if register = HonestWitness.destinationRegisterAddress dst then 1 else 0
      | none => 0 at hwa
    have hinc : HonestWitness.RdInc (F := F) params trace t =
        HonestWitness.rdValue instr row.postState -
          HonestWitness.rdValue instr row.preState := by
      unfold HonestWitness.RdInc
      simp only [dif_pos hb]
      rfl
    have hwrite : HonestWitness.RdWriteValue (F := F) params trace t =
        HonestWitness.rdValue instr row.postState := by
      unfold HonestWitness.RdWriteValue
      simp only [dif_pos hb]
      rfl
    simp only [hwa]
    rw [hwrite, register42_rdValue_eq_destination]
    cases hd : instr.destination? with
    | none => simp
    | some dst =>
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (HonestWitness.destinationRegisterAddress dst)]
        simp only [Finset.mem_univ, ↓reduceIte]
        have hpre := register42_registersVal_preState (F := F) params trace traceFits
          initialRegistersZero (HonestWitness.destinationRegisterAddress dst) t.val hb
        rw [register42_srcOfDestinationAddress dst
          (register42_instruction_destination_canonical instr dst hcanon hd)] at hpre
        change HonestWitness.RegistersVal (F := F) params trace
          (HonestWitness.destinationRegisterAddress dst) t = _ at hpre
        rw [hpre, hinc, register42_rdValue_eq_destination,
          register42_rdValue_eq_destination, hd]
        ring
  · simp [HonestWitness.RdWriteValue, HonestWitness.RdWa, hb]

end JoltConstraints
