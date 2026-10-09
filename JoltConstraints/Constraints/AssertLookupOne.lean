import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- The equality assertions in this trace have equal operands. For an immediate
of zero, successful execution already enforces this. For a nonzero immediate,
this excludes the failing spoil execution that Rust permits to retire but whose
proof is deliberately unsatisfiable.
Rust: tracer/src/instruction/virtual_assert_eq.rs and
crates/jolt-lookup-tables/src/instructions/virt/assert_eq.rs. -/
def assertEqPasses (trace : Trace) : Prop :=
  ∀ t : Fin trace.rows.size,
    let row := trace.rows[t]
    match (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction with
    | .VirtualAssertEQ lhs rhs _ =>
        JoltISA.sourceValue lhs row.preState = JoltISA.sourceValue rhs row.preState
    | _ => True

/-- Constraint (12) in `constraints.md` (stage 1):
assertion rows require lookup output one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def assertLookupOne {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Assert t * (witness.LookupOutput t - 1) = 0

end JoltConstraints
