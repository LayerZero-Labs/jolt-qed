import JoltConstraints.translation.witness_helpers.left_instruction_input
import JoltConstraints.translation.witness_helpers.right_instruction_input

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- Rust: `crates/jolt-witness/src/witnesses/operands.rs` (`Product`).
-- Rust multiplies the left input (a u64) by the right input (an i128) as signed
-- integers and keeps a 128-bit magnitude with its sign (`S64::mul_trunc`).
-- The left input is the unexpanded PC or rs1, in [0, 2^64). The right input is
-- signed. I/U/J immediates are wrapped to u64, but the floor-addressed loads and
-- stores (VirtualLoadB/H/W, VirtualStoreB/H/W) select rs1 and the signed
-- immediate, and ShiftDataB/H/W add the signed immediate to rs2
-- (`crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs` and
-- `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs`).
-- For example, a floor store at `sp - 8` has product `sp * (-8)`, which is
-- negative. This definition multiplies in the field without truncation. It equals
-- Rust's value whenever the exact product's magnitude is below 2^128, for example
-- when the right input's magnitude is below 2^64. Padding is zero.
noncomputable def Product {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t => LeftInstructionInput p trace t * RightInstructionInput p trace t

end TraceWitness
