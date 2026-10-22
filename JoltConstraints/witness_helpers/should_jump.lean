import JoltConstraints.witness_helpers.op_flags
import JoltConstraints.witness_helpers.instruction_flags

set_option autoImplicit false

namespace TraceWitness

-- Rust: [ShouldJump](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs).
-- A jump followed by an explicit padding row gives zero. At the final witness
-- position Rust's missing successor does NOT count as a no-op, so the Jump bit
-- is retained there. This differs from NextIsNoop's missing-successor rule.
-- Padding itself has Jump = 0, including the final row of a padded trace.
noncomputable def ShouldJump {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    OpFlags p trace .Jump t *
      (if nextInBounds : t.val + 1 < p.traceLength then
        1 - InstructionFlags p trace .IsNoop ⟨t.val + 1, nextInBounds⟩
      else 1)

end TraceWitness
