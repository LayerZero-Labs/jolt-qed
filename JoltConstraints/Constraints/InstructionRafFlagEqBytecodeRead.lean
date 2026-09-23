import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (52) in `constraints.md`:
The flag agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L603-L609 -/
def instructionRafFlagEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.InstructionRafFlag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRafFlag program address.val * bytecodeRa witness address t

/-- Completeness target for the honest witness; proof pending.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_instructionRafFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (bytecodeFits : program.expandedBytecode.size + 1 ≤ 2 ^ params.logBytecodeK)
    : instructionRafFlagEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
