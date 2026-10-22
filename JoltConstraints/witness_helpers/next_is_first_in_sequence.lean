import JoltConstraints.witness_helpers.op_flags

set_option autoImplicit false

namespace TraceWitness

-- Rust: [NextIsFirstInSequence](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs).
-- Read the next execution row's IsFirstInSequence flag. Padding contributes
-- zero, as does the missing successor at the final witness position.
-- Rust: [successor window](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/cycle.rs#L99-L118).
noncomputable def NextIsFirstInSequence {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      OpFlags p trace .IsFirstInSequence ⟨t.val + 1, nextInBounds⟩
    else 0

end TraceWitness
