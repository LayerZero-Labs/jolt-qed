import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (38) in `constraints.md`:
Each final RAM word equals its initial value plus all write increments.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135-L154 -/
def ramValFinalEqInitialPlusRamInc {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    witness.RamValFinal address = ramInitialValue program address.val +
      ∑ cycle : Fin params.traceLength, witness.RamRa address cycle * witness.RamInc cycle

/-- Completeness target for the honest witness; proof pending.
FIXME (translation boundary): establish Rust's memory-history and terminal
panic/termination write conventions, along with final-image validity. The final
snapshot is not just the last RamVal column. Audit Rust-valid executions before
adding assumptions or attempting this theorem. -/
theorem honestWitness_ramValFinalEqInitialPlusRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : ramValFinalEqInitialPlusRamInc program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
