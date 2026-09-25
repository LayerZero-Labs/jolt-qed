import JoltConstraints.Constraints.RamReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (23) in `constraints.md`:
The RAM address selector selects the value for this cycle.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L89-L106 -/
def ramReadValueEqRamRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamReadValue t =
      ∑ address : Fin params.ramSize, witness.RamRa address t * witness.RamVal address t

/-- Completeness target for the honest witness.
Nonzero accessed addresses and RamFits exclude cold selectors on real memory accesses. -/
theorem honestWitness_ramReadValueEqRamRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (validAccesses : ramAccessesValid trace)
    : ramReadValueEqRamRead
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  change HonestWitness.RamReadValue (F := F) params trace t =
    ∑ address : Fin params.ramSize,
      HonestWitness.RamRa params trace ramFits address t *
        HonestWitness.RamVal params trace ramFits address t
  cases hr : HonestWitness.remappedRamAddress trace t.val with
  | none =>
      rw [ramRa_sum_none params trace ramFits t hr]
      exact ramReadValue_zero_of_remapped_none params trace ramFits validAccesses t hr
  | some b =>
      rw [ramRa_sum_some params trace ramFits t b hr]
      dsimp [HonestWitness.RamVal]
      simp [HonestWitness.RamRa, hr]

end JoltConstraints
