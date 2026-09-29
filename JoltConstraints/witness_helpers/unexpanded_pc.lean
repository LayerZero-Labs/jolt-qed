import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [UnexpandedPc](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/pc.rs:36).
-- The source instruction's memory address, taken from the selected bytecode row.
-- Rows in one virtual sequence share this address, even though their expanded PCs differ.
-- Padding contributes zero, as in Rust's default trace row.
noncomputable def UnexpandedPC [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
      (bytecodeRow.address.toNat : F)
    else 0

end HonestWitness
