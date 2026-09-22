import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltBytecode.JoltISA.semantic_helpers

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch::{extract, to_field}.
-- Branch-taken bit for each padded witness position; padding contributes zero.
noncomputable def ShouldBranch [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    -- A witness index may point past the execution rows, into padding.
    if inBounds : t.val < trace.rows.size then
      let row : JoltTraceRow program := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match instruction with
      | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _
      | .BGE lhs rhs _ | .BLTU lhs rhs _ | .BGEU lhs rhs _ =>
          let rs1val := JoltISA.sourceValue lhs row.preState
          let rs2val := JoltISA.sourceValue rhs row.preState
          if JoltISA.branchDecisionPure instruction rs1val rs2val then 1 else 0
      | _ => 0
    else 0

end HonestWitness
