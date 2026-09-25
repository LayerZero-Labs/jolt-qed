import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

open LeanRV64D.Functions

namespace JoltISA

-- Keep the full arithmetic value until the caller chooses its output width.
-- Execution keeps the low 64 bits (or a sign-extended low word); instruction
-- lookup addresses retain the carry or the full 128-bit product.
-- Rust: [ADD](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/add.rs:9).
def addWide (lhs rhs : BitVec 64) : Nat := lhs.toNat + rhs.toNat

-- The extra 2^64 makes subtraction nonnegative and is part of Rust's lookup
-- address, including when rhs = 0. Truncating to 64 bits gives lhs - rhs.
-- Rust: [SUB](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/sub.rs:9).
def subWide (lhs rhs : BitVec 64) : Nat := (2 ^ 64 - rhs.toNat) + lhs.toNat

-- Rust: [MUL](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/mul.rs:9).
def mulWide (lhs rhs : BitVec 64) : Nat := lhs.toNat * rhs.toNat

-- These are definitional equalities: sharing the full calculation preserves
-- the previous ISA operations without adding assumptions to any proof.
@[simp] theorem addWide_low (lhs rhs : BitVec 64) :
    BitVec.ofNat 64 (addWide lhs rhs) = lhs + rhs := rfl

@[simp] theorem subWide_low (lhs rhs : BitVec 64) :
    BitVec.ofNat 64 (subWide lhs rhs) = lhs - rhs := rfl

@[simp] theorem mulWide_low (lhs rhs : BitVec 64) :
    BitVec.ofNat 64 (mulWide lhs rhs) = lhs * rhs := rfl

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
