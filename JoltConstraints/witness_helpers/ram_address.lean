import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace HonestWitness

-- Rust: [ram_access_address](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/ram.rs:7).
-- This is the effective byte address captured by the tracer, including device
-- I/O. Use the same address calculation as ISA load/store execution.
noncomputable def ramAccessAddress (instruction : JoltISA.Instr)
    (preState : SailJoltState) : Option (BitVec 64) :=
  match instruction with
  | .LD _ _ base imm | .SD base _ imm =>
      some (Memory.effectiveAddr12 (JoltISA.sourceValue base preState) imm)
  | _ => none

-- Rust: [RamAddress](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/ram.rs:41).
-- Encode the raw byte address before RAM word remapping. Read the base from
-- the pre-state, including when a load overwrites that same register.
-- Instructions without a memory access and padding positions contribute zero.
noncomputable def RamAddress {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match ramAccessAddress instruction row.preState with
      | some address => (address.toNat : F)
      | none => 0
    else 0

end HonestWitness
