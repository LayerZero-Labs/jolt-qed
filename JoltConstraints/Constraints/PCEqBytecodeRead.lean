import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (43) in `constraints.md` (stages 6a–6b):
the expanded PC is the selected bytecode slot.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L358-L378 -/
def pcEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.PC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        (address.val : F) * bytecodeRa witness address t

/-- The honest witness satisfies constraint (43); proof pending.
The bytecode domain must contain every program row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_pcEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (bytecodeFits : program.expandedBytecode.size + 1 ≤ 2 ^ params.logBytecodeK) :
    pcEqBytecodeRead
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
