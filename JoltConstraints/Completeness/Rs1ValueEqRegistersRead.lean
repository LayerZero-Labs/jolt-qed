import JoltConstraints.Constraints.Rs1ValueEqRegistersRead
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RegistersReadProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_rs1ValueEqRegistersRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0) :
    rs1ValueEqRegistersRead
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.Rs1Value params trace t =
    ∑ register : Fin 128,
      HonestWitness.Rs1Ra params trace register t *
        HonestWitness.RegistersVal params trace register t
  by_cases hb : t.val < trace.rows.size
  · let instr := program.expandedBytecode[(trace.rows[t.val]'hb).rowIndex].expandedInstruction
    have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
      program.expandedBytecode[(trace.rows[t.val]'hb).rowIndex].registerOperandsCanonical
    have hra := rs1Ra_real (F := F) params trace t hb
    rw [rs1Value_real (F := F) params trace t hb]
    change (match rs1Operand? instr with
      | some src => ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F)
      | none => 0) = _
    change ∀ register, HonestWitness.Rs1Ra (F := F) params trace register t =
      match rs1Operand? instr with
      | some src => if register = HonestWitness.sourceRegisterAddress src then 1 else 0
      | none => 0 at hra
    simp only [hra]
    cases hs : rs1Operand? instr with
    | none => simp
    | some src =>
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (HonestWitness.sourceRegisterAddress src)]
        simp only [Finset.mem_univ, ↓reduceIte]
        rw [registersVal_source_eq_preState (F := F) params trace traceFits
          initialRegistersZero t hb src (rs1Operand_canonical instr src hcanon hs)]
  · simp [HonestWitness.Rs1Value, HonestWitness.Rs1Ra, hb]

end JoltConstraints
