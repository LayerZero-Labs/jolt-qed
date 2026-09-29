import JoltConstraints.witness_helpers.instruction_flags

set_option autoImplicit false

namespace HonestWitness

-- Rust: [NextIsNoop](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/flags.rs:84).
-- Read the next execution row's IsNoop flag. InstructionFlags marks padding
-- as a no-op. Rust also counts the missing successor at the final witness
-- position as a no-op, so both cases give one.
-- Rust: [successor window](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:111).
noncomputable def NextIsNoop {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      InstructionFlags p trace .IsNoop ⟨t.val + 1, nextInBounds⟩
    else 1

end HonestWitness
