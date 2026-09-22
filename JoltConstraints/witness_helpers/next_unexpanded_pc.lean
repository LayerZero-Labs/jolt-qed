import JoltConstraints.witness_helpers.unexpanded_pc

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [NextUnexpandedPc](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/pc.rs:44).
-- Source instruction address of the next execution row, taken from UnexpandedPC.
-- The value is zero for a padding successor and at the final witness position.
-- Rust: [successor window](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:111).
noncomputable def NextUnexpandedPC [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      UnexpandedPC p trace ⟨t.val + 1, nextInBounds⟩
    else 0

end HonestWitness
