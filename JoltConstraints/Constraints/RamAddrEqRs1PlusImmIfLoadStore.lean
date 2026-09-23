import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (01) in `constraints.md` (stage 1):
loads and stores use the base register plus the immediate as their RAM address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def ramAddrEqRs1PlusImmIfLoadStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .Load t + witness.OpFlags .Store t) *
      (witness.RamAddress t - witness.Rs1Value t - witness.Imm t) = 0

/-- Completeness target for the honest witness; proof pending.
The statement is provisional until the required validity assumptions are added.
TODO: Relate the wrapping 64-bit address calculation to field addition;
rule out address wraparound in the admissible execution assumptions. -/
theorem honestWitness_ramAddrEqRs1PlusImmIfLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength) :
    ramAddrEqRs1PlusImmIfLoadStore
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
