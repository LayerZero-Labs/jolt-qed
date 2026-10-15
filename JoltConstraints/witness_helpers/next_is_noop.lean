import JoltConstraints.witness_helpers.instruction_flags

set_option autoImplicit false

namespace TraceWitness

-- Rust: [NextIsNoop](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs).
-- Read the next execution row's IsNoop flag. InstructionFlags marks padding
-- as a no-op. Rust also counts the missing successor at the final witness
-- position as a no-op, so both cases give one.
-- Rust: [successor window](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/cycle.rs#L99-L118).
noncomputable def NextIsNoop {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      InstructionFlags p trace .IsNoop ⟨t.val + 1, nextInBounds⟩
    else 1

end TraceWitness
