import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (45) in `constraints.md` (stages 6a–6b):
the immediate is the selected row's normalized immediate.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L551-L574 -/
def immEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.Imm t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeImmediate program address.val * bytecodeRa witness address t

end JoltConstraints
