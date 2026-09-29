import JoltConstraints.witness_helpers.pc

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [NextPc](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/pc.rs:40).
-- Expanded PC of the next execution row, which can revisit or skip bytecode slots.
-- PC supplies zero for padding; the final witness position also has successor value zero.
-- Rust: [successor window](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:111).
noncomputable def NextPC [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      PC p trace ⟨t.val + 1, nextInBounds⟩
    else 0

end HonestWitness
