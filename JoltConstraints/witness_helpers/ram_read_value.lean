import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_trace
import JoltConstraints.execution_facts
import JoltConstraints.witness_helpers.rd_value

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RamReadValue](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/ram.rs).
-- Rust: [trace_store](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:609).
-- A load supplies its captured destination value. A store supplies the old word
-- from the full pre-state, including memory-mapped device data. The row's presence
-- proof lets us read that word without substituting zero for missing RAM bytes.
-- Other instructions and padding contribute zero.
noncomputable def RamReadValue [Field F] {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match hInstr : instruction with
      | .LD _ _ _ _ => rdValue instruction row.postState
      | .SD base value imm =>
          let address := ((JoltISA.sourceValue base row.preState) + imm)
          let word := (JoltISA.trace_doubleword? row.preState address).get
             -- The old word is present before the store (store_word_present);
             -- Rust also reads the old word when recording a store.
            (row.store_word_present base value imm hInstr)
          (word.toNat : F)
      | _ => 0
    else 0

end HonestWitness
