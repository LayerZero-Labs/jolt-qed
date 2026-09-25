import JoltConstraints.witness_helpers.left_instruction_input
import JoltConstraints.witness_helpers.right_instruction_input

set_option autoImplicit false

namespace HonestWitness

-- Rust: [Product](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:131).
-- For the RV64 instructions modeled here, both selected inputs are in [0, 2^64).
-- Signed branch/store immediates are not selected as instruction inputs, and
-- I/U/J immediates have already been wrapped to u64. Their product fits Rust's
-- unsigned 128-bit magnitude, even above i128::MAX, so field multiplication is
-- exactly the cast of Rust's S128 product. No 64-bit truncation; padding is zero.
noncomputable def Product {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t => LeftInstructionInput p trace t * RightInstructionInput p trace t

end HonestWitness
