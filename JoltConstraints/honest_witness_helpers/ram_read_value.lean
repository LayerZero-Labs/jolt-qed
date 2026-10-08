import JoltConstraints.memory_presence
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.rd_value

set_option autoImplicit false

namespace HonestWitness

open TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RamReadValue](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/ram.rs).
-- Rust: [trace_store](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:609).
-- A load supplies its captured destination value. A store supplies the old word
-- from the full pre-state. HonestTrace.store_word_present proves its presence
-- from initialization and the preceding steps of this trace.
-- Other instructions and padding contribute zero.
noncomputable def RamReadValue [Field F] {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := trace.row t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match hInstr : instruction with
      | .LD _ _ _ _ => rdValue instruction row.postState
      | .SD base value imm =>
          let address := ((JoltISA.sourceValue base row.preState) + imm)
          let word := (JoltISA.trace_doubleword? row.preState address).get
            (trace.store_word_present t.val inBounds base value imm hInstr)
          (word.toNat : F)
      | _ => 0
    else 0

end HonestWitness
