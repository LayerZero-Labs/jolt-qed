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
FIXME (translation boundary): Lean's `JoltProgram` does not yet certify that
each final row came from Rust's source-instruction expander. Rust's trace path
routes a guest `JAL x0` through the same one-row destination rewrite as
bytecode expansion; both execute and capture the temporary destination. A raw
final `JAL x0` is still representable in Lean, but is not Rust's output for
that guest instruction. Model this provenance before proving the unrestricted
statement, without excluding any final row Rust actually produces. -/
theorem honestWitness_rdWriteEqPCPlusConstIfJump
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rdWriteEqPCPlusConstIfJump
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
