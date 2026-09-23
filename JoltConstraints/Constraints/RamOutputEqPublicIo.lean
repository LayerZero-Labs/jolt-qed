import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (26) in `constraints.md`:
On the public I/O interval, the final RAM value equals the supplied public I/O word.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L115-L128 -/
def ramOutputEqPublicIo {F : Type} [Field F] {params : WitnessParams}
    (io : JoltIOState) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    ramPublicIoMask io address.val *
      (witness.RamValFinal address - ((ramPublicIoWord io address.val).toNat : F)) = 0

/-- Completeness target for the honest witness; proof pending.
The honest public output is taken from the final recorded state. TODO: make valid,
nonoverlapping layout and buffer bounds explicit. This statement is provisional
until those admissibility assumptions are supplied. -/
theorem honestWitness_ramOutputEqPublicIo
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength)
    : ramOutputEqPublicIo (HonestWitness.finalTraceState trace).io
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
