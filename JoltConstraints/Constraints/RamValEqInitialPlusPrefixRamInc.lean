import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (37) in `constraints.md`:
Before cycle t, each word equals its initial value plus strictly earlier write increments.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135-L154 -/
def ramValEqInitialPlusPrefixRamInc {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
    witness.RamVal address t = ramInitialValue program address.val +
      ∑ cycle : Fin params.traceLength,
        if cycle.val < t.val then witness.RamRa address cycle * witness.RamInc cycle else 0

/-- Completeness target for the honest witness; proof pending.
FIXME (translation boundary): relate captured read values to the initialized
memory and preceding stores, including Rust's device I/O readback. Linked
successful ISA rows alone do not provide this memory-history invariant. Check
whether Rust-valid device reads satisfy the equation before strengthening the
Lean trace model or attempting this theorem. -/
theorem honestWitness_ramValEqInitialPlusPrefixRamInc
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramValEqInitialPlusPrefixRamInc program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
