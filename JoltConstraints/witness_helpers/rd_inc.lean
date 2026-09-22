import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.rd_value

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RdInc::extract](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/increments.rs:24).
-- New destination value minus old destination value. Convert each unsigned word
-- into F before subtracting: a decrease must give a negative field value, without
-- Nat subtraction truncation or 64-bit wraparound. No destination or padding gives zero.
noncomputable def RdInc [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      rdValue instruction row.postState - rdValue instruction row.preState
    else 0

end HonestWitness
