import JoltConstraints.witness_helpers.unexpanded_pc

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [NextUnexpandedPc](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/pc.rs).
-- Source instruction address of the next execution row, taken from UnexpandedPC.
-- The value is zero for a padding successor and at the final witness position.
-- Rust: [successor window](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/cycle.rs#L99-L118).
noncomputable def NextUnexpandedPC [Field F] (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      UnexpandedPC p trace ⟨t.val + 1, nextInBounds⟩
    else 0

end TraceWitness
