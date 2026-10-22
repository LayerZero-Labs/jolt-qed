import JoltConstraints.witness_helpers.op_flags

set_option autoImplicit false

namespace TraceWitness

-- Rust: [NextIsVirtual](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs).
-- Read the next execution row's VirtualInstruction flag. OpFlags supplies zero
-- for padding; the final witness position has no successor and also gives zero.
-- Rust: [successor window](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/cycle.rs#L99-L118).
noncomputable def NextIsVirtual {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      OpFlags p trace .VirtualInstruction ⟨t.val + 1, nextInBounds⟩
    else 0

end TraceWitness
