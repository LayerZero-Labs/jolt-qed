import JoltConstraints.witness_helpers.op_flags

set_option autoImplicit false

namespace HonestWitness

-- Rust: [NextIsVirtual](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/flags.rs:95).
-- Read the next execution row's VirtualInstruction flag. OpFlags supplies zero
-- for padding; the final witness position has no successor and also gives zero.
-- Rust: [successor window](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:111).
noncomputable def NextIsVirtual {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      OpFlags p trace .VirtualInstruction ⟨t.val + 1, nextInBounds⟩
    else 0

end HonestWitness
