import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (14) in `constraints.md` (stage 1):
jumps write the return address, accounting for compressed instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqPCPlusConstIfJump {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Jump t *
      (witness.RdWriteValue t - witness.UnexpandedPC t - 4 +
        2 * witness.OpFlags .IsCompressed t) = 0

/-- Completeness target for the Rust witness extraction; proof pending.
No destination, opcode, or nonwrapping-arithmetic restriction is imposed to make
the equation hold. Any required input condition must be justified from Rust. -/
theorem honestWitness_rdWriteEqPCPlusConstIfJump
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace) :
    rdWriteEqPCPlusConstIfJump
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
