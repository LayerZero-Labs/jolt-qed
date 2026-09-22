import JoltConstraints.witness_helpers.ram_address

set_option autoImplicit false

namespace HonestWitness

-- Rust: [RamHammingWeight](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/ram.rs:89).
-- A single 0/1 flag: a load or store at a nonzero raw byte address contributes
-- one, including device I/O. Test the address before field conversion and
-- independently of whether RAM word remapping accepts it.
-- Accesses at address zero, other instructions, and padding contribute zero.
noncomputable def RamHammingWeight {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match ramAccessAddress instruction row.preState with
      | some address => if address = 0 then 0 else 1
      | none => 0
    else 0

end HonestWitness
