import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RegistersReadProofHelpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (36) in `constraints.md` (stage 4):
the second-source selector reads the corresponding register value.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs#L97-L121 -/
def rs2ValueEqRegistersRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.Rs2Value t =
      ∑ register : Fin 128, witness.Rs2Ra register t * witness.RegistersVal register t

/-- Completeness target for the honest witness.
Initial register contents must agree with the zero-initialized Rust witness array.
Each bytecode row certifies that its register operands follow the ISA address map.
The proof must relate the replayed register history to the captured ISA values. -/
theorem honestWitness_rs2ValueEqRegistersRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0) :
    rs2ValueEqRegistersRead
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.Rs2Value params trace t =
    ∑ register : Fin 128,
      HonestWitness.Rs2Ra params trace register t *
        HonestWitness.RegistersVal params trace register t
  by_cases hb : t.val < trace.rows.size
  · let instr := program.expandedBytecode[(trace.rows[t.val]'hb).rowIndex].expandedInstruction
    have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
      program.expandedBytecode[(trace.rows[t.val]'hb).rowIndex].registerOperandsCanonical
    have hra := rs2Ra_real (F := F) params trace t hb
    rw [rs2Value_real (F := F) params trace t hb]
    change (match rs2Operand? instr with
      | some src => ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F)
      | none => 0) = _
    change ∀ register, HonestWitness.Rs2Ra (F := F) params trace register t =
      match rs2Operand? instr with
      | some src => if register = HonestWitness.sourceRegisterAddress src then 1 else 0
      | none => 0 at hra
    simp only [hra]
    cases hs : rs2Operand? instr with
    | none => simp
    | some src =>
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (HonestWitness.sourceRegisterAddress src)]
        simp only [Finset.mem_univ, ↓reduceIte]
        rw [registersVal_source_eq_preState (F := F) params trace traceFits
          initialRegistersZero t hb src (rs2Operand_canonical instr src hcanon hs)]
  · simp [HonestWitness.Rs2Value, HonestWitness.Rs2Ra, hb]

end JoltConstraints
