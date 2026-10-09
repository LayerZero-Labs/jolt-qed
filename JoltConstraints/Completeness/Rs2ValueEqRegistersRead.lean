import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers
import JoltConstraints.Constraints.Rs2ValueEqRegistersRead
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_rs2ValueEqRegistersRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0) :
    rs2ValueEqRegistersRead
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  change TraceWitness.Rs2Value params trace t =
    ∑ register : Fin 128,
      TraceWitness.Rs2Ra params trace register t *
        TraceWitness.RegistersVal params trace register t
  by_cases hb : t.val < trace.rows.size
  · let instr := trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction
    have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
      trace.registerOperandsCanonical (trace.rows[t.val]'hb).rowIndex
    have hra := rs2Ra_real (F := F) params trace t hb
    rw [rs2Value_real (F := F) params trace t hb]
    change (match rs2Operand? instr with
      | some src => ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F)
      | none => 0) = _
    change ∀ register, TraceWitness.Rs2Ra (F := F) params trace register t =
      match rs2Operand? instr with
      | some src => if register = TraceWitness.sourceRegisterAddress src then 1 else 0
      | none => 0 at hra
    simp only [hra]
    cases hs : rs2Operand? instr with
    | none => simp
    | some src =>
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (TraceWitness.sourceRegisterAddress src)]
        simp only [Finset.mem_univ, ↓reduceIte]
        rw [registersVal_source_eq_preState (F := F) params trace traceFits
          initialRegistersZero t hb src (rs2Operand_canonical instr src hcanon hs)]
  · simp [TraceWitness.Rs2Value, TraceWitness.Rs2Ra, hb]

end JoltConstraints
