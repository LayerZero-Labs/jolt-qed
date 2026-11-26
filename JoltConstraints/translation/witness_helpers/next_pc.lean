import JoltConstraints.translation.witness_helpers.pc

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [NextPc](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-witness/src/witnesses/pc.rs).
-- Expanded PC of the next execution row, which can revisit or skip bytecode slots.
-- PC supplies zero for padding; the final witness position also has successor value zero.
-- Rust: [successor window](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-witness/src/backend/trace/cycle.rs#L69-L88).
noncomputable def NextPC [Field F] (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      PC p trace ⟨t.val + 1, nextInBounds⟩
    else 0

end TraceWitness
