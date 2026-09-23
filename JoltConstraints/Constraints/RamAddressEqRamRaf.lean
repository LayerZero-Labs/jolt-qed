import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (25) in `constraints.md`:
Recover the raw byte address from the selected remapped word address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs#L133-L151 -/
def ramAddressEqRamRaf {F : Type} [Field F] {params : WitnessParams}
    (layout : JoltIOLayout) (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RamAddress t =
      ∑ address : Fin params.ramSize,
        ((ramLowestAddress layout + 8 * address.val : Nat) : F) * witness.RamRa address t

/-- Completeness target for the honest witness; proof pending.
Alignment is required because Rust remaps byte addresses by integer division by eight. -/
theorem honestWitness_ramAddressEqRamRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (validAccesses : ramAccessesValid trace)
    : ramAddressEqRamRaf program.initialState.io.layout
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
