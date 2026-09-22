import JoltConstraints.witness_helpers.op_flags

set_option autoImplicit false

namespace HonestWitness

-- Rust: [NextIsFirstInSequence](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/flags.rs:108).
-- Read the next execution row's IsFirstInSequence flag. Padding contributes
-- zero, as does the missing successor at the final witness position.
-- Rust: [successor window](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:111).
noncomputable def NextIsFirstInSequence {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      OpFlags p trace .IsFirstInSequence ⟨t.val + 1, nextInBounds⟩
    else 0

end HonestWitness
