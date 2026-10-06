import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_trace
import JoltConstraints.witness_helpers.rd_value

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RdWriteValue](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/registers.rs:15).
-- Capture rd from the post-state; instructions without rd and padding give zero.
noncomputable def RdWriteValue [Field F] {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      rdValue instruction row.postState
    else 0

end HonestWitness
