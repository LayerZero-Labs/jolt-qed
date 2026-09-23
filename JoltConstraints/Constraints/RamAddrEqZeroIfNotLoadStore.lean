import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (02) in `constraints.md` (stage 1):
instructions other than loads and stores have zero RAM address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def ramAddrEqZeroIfNotLoadStore {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.OpFlags .Load t - witness.OpFlags .Store t) * witness.RamAddress t = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_ramAddrEqZeroIfNotLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace) :
    ramAddrEqZeroIfNotLoadStore
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
