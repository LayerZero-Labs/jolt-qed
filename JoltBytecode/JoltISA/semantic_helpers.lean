import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

open LeanRV64D.Functions

namespace JoltISA

-- Rust: tracer/src/instruction/{beq,bne,blt,bge,bltu,bgeu}.rs::exec.
-- Rust: crates/jolt-lookup-tables/src/instructions/riscv/{beq,bne,blt,bge,bltu,bgeu}.rs::to_lookup_output.
/-- Evaluate a branch condition on operand values. Non-branch instructions return `false`. -/
def branchDecisionPure (instruction : Instr) (lhs rhs : BitVec 64) : Bool :=
  match instruction with
  | .BEQ _ _ _ => lhs == rhs
  | .BNE _ _ _ => lhs != rhs
  | .BLT _ _ _ => zopz0zI_s lhs rhs
  | .BGE _ _ _ => zopz0zKzJ_s lhs rhs
  | .BLTU _ _ _ => zopz0zI_u lhs rhs
  | .BGEU _ _ _ => zopz0zKzJ_u lhs rhs
  | _ => false

end JoltISA
