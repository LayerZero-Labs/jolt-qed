import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Keep the bytecode slot as a natural number for address decomposition, before
-- casting into the witness field. Slot 0 is reserved for padding.
def bytecodePc {program : JoltProgram} (trace : JoltTrace program) (t : Nat) : Nat :=
  if inBounds : t < trace.rows.size then
    (getElem trace.rows t inBounds).rowIndex.val + 1
  else 0

-- Rust: [Pc](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/pc.rs:31).
-- The expanded bytecode slot of the instruction executed at this trace position.
-- Rust's preprocessing prepends a no-op at slot 0 to program.expandedBytecode,
-- so a represented instruction at array index k occupies slot k + 1.
-- This is a bytecode index, not a memory address or an execution-step number.
-- Rust: [preprocess](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/preprocess/bytecode.rs:34).
noncomputable def PC [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t => (bytecodePc trace t.val : F)

end HonestWitness
