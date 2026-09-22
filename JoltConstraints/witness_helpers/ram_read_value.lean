import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
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
noncomputable def RamReadValue [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match h : instruction with
      | .LD _ _ _ _ => rdValue instruction row.postState
      | .SD base value imm =>
          let address := Memory.effectiveAddr12 (JoltISA.sourceValue base row.preState) imm
          let word := (JoltISA.memoryWord? row.preState address).get
            (by
              have stored : program.expandedBytecode[row.rowIndex].instruction =
                  .SD base value imm := h
              simpa only [stored] using row.storeMemoryPresent)
          (word.toNat : F)
      | _ => 0
    else 0

end HonestWitness
