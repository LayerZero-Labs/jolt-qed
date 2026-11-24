import JoltConstraints.translation.Constraints.BytecodeReadData
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (47) in `constraints.md` (stages 6a–6b):
each instruction flag is selected from the fixed bytecode table.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L728-L867 -/
def instructionFlagsEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (flag : InstructionFlags) (t : Fin params.traceLength),
    witness.InstructionFlags flag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeInstructionFlag bytecode flag address.val * bytecodeRa witness address t

end JoltConstraints
