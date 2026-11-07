import JoltConstraints.memory_presence
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.rd_value

open LeanRV64D

set_option autoImplicit false

namespace HonestWitness

open TraceWitness

variable {F : Type} (p : WitnessParams)

/-- The pre-access doubleword, cast to the field, with zero for other rows
and padding.
Loads use their captured destination; stores read the old word whose presence
follows from this honest trace's initialization and execution.
For example, a floor store at effective address 11 reads the old doubleword at 8.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`);
Jolt's prover: `crates/jolt-witness/src/witnesses/ram.rs` (`RamReadValue`)
at `c6703570`. -/
noncomputable def RamReadValue [Field F] {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := trace.row t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      let oldWord (address : BitVec 64)
          (isStore : match instruction with
            | .SD base _ imm => address = JoltISA.sourceValue base row.preState + imm
            | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
            | .VirtualStoreW base _ imm _ =>
                address = (JoltISA.sourceValue base row.preState + imm) &&& ~~~7
            | _ => False) : F :=
        let word := (JoltISA.trace_doubleword? row.preState address).get
          (trace.store_word_present t.val inBounds address isStore)
        (word.toNat : F)
      match hInstr : instruction with
      | .LD _ _ _ _ | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW .. =>
          rdValue instruction row.postState
      | .SD base _ imm =>
          oldWord (JoltISA.sourceValue base row.preState + imm) (by simp only [hInstr])
      | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
      | .VirtualStoreW base _ imm _ =>
          oldWord ((JoltISA.sourceValue base row.preState + imm) &&& ~~~7)
            (by simp only [hInstr])
      | _ => 0
    else 0

end HonestWitness
