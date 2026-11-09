import JoltConstraints.Constraints.RamAddrEqRs1PlusImmMinusLookupIfLoadStore
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (01) has the form
`(Load t + Store t) · (RamAddress t - Rs1Value t - Imm t + LookupOutput t) = 0`.
On a memory row, that is when the instruction at cycle `t` is LD, SD,
`VirtualLoadB/H/W` or `VirtualStoreB/H/W`, `Load t + Store t = 1`.
So (01) needs `RamAddress t = Rs1Value t + Imm t - LookupOutput t`.
Each cell is a trace value cast into the field: `RamAddress t`, `Rs1Value t`
and `LookupOutput t` are 64-bit values, and `Imm t` is the signed offset.
The equation adds them in the field, but Jolt's tracer computed
`RamAddress t` with 64-bit addition, which wraps.
So the equation holds only when `rs1 + imm` does not wrap. For example,
`ld x1, -16(x0)` gives `RamAddress t = 2^64 - 16`, but the right side is
`0 + (-16) - 0 = -16`; they differ by `2^64`, and the constraint is not
satisfied.
Left as `sorry` until a16z/jolt#1949 is fixed.

Rust, at `c6703570`:
- (01): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
  (`RamAddrEqRs1PlusImmMinusLookupIfLoadStore`, row 0).
- 64-bit address addition: `tracer/src/instruction/ld.rs` (`LD::exec`),
  `tracer/src/instruction/sd.rs` (`SD::exec`) and
  `tracer/src/instruction/floor_access.rs` (`addresses`), all `wrapping_add`.
- The cells: `crates/jolt-witness/src/witnesses/ram.rs` (`RamAddress`),
  `registers.rs` (`Rs1Value`), `operands.rs` (`Imm`) and `lookups.rs` (`LookupOutput`). -/
theorem honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramAddrEqRs1PlusImmMinusLookupIfLoadStore
      (HonestTrace.honestWitness (F := F) params trace) := by
  sorry

end JoltConstraints
