import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace TraceWitness

/-- The byte address recorded by Jolt's tracer, including device accesses.
LD/SD record the wrapping effective address `ea = base + imm`; floor rows
record `ea - (ea &&& mask)`, with B/H/W masks 7/6/4.
For example, a halfword floor row at `ea = 10` records 8.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`);
Jolt's prover: `crates/jolt-witness/src/witnesses/ram.rs` (`ram_access_address`)
at `c6703570`. -/
noncomputable def ramAccessAddress (instruction : JoltISA.Instr)
    (preState : SailJoltState) : Option (BitVec 64) :=
  match instruction with
  | .LD _ _ base imm | .SD base _ imm =>
      some (((JoltISA.sourceValue base preState) + imm))
  | .VirtualLoadB _ _ base imm _ | .VirtualStoreB base _ imm _ =>
      let ea := JoltISA.sourceValue base preState + imm
      some (ea - (ea &&& 7))
  | .VirtualLoadH _ _ base imm _ | .VirtualStoreH base _ imm _ =>
      let ea := JoltISA.sourceValue base preState + imm
      some (ea - (ea &&& 6))
  | .VirtualLoadW _ _ base imm _ | .VirtualStoreW base _ imm _ =>
      let ea := JoltISA.sourceValue base preState + imm
      some (ea - (ea &&& 4))
  | _ => none

-- Rust: [RamAddress](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/ram.rs).
-- Encode the raw byte address before RAM word remapping. Read the base from
-- the pre-state, including when a load overwrites that same register.
-- Instructions without a memory access and padding positions contribute zero.
noncomputable def RamAddress {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match ramAccessAddress instruction row.preState with
      | some address => (address.toNat : F)
      | none => 0
    else 0

end TraceWitness
