import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (46) in `constraints.md` (stages 6a–6b):
each circuit flag is selected from the fixed bytecode table.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L545-L557 -/
def opFlagsEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (witness : WitnessType F params) : Prop :=
  ∀ (flag : CircuitFlags) (t : Fin params.traceLength),
    witness.OpFlags flag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeCircuitFlag trace flag address.val * bytecodeRa witness address t

end JoltConstraints
