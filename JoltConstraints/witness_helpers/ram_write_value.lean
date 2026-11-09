import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.rd_value

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

/-- The post-access doubleword, cast to the field; non-memory rows and padding
contribute zero.
Loads preserve the captured word, and stores use their pre-state value source.
For example, a floor byte store writes the complete merged doubleword.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`);
Jolt's prover: `crates/jolt-witness/src/witnesses/ram.rs` (`RamWriteValue`)
at `c6703570`. -/
noncomputable def RamWriteValue [Field F] (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match instruction with
      | .LD _ _ _ _ | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW .. => rdValue instruction row.postState
      | .SD _ value _ | .VirtualStoreB _ value _ _
      | .VirtualStoreH _ value _ _ | .VirtualStoreW _ value _ _ => ((JoltISA.sourceValue value row.preState).toNat : F)
      | _ => 0
    else 0

end TraceWitness
