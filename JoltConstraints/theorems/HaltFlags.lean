import JoltConstraints.translation.metadata

set_option autoImplicit false

namespace JoltMetadata

/-- The halt columns are exactly the instruction's explicit halt-kind metadata.
For example, Panic sets both columns, while JoltSuccess sets only Halt.
Jolt at `ff6fc6568`: `crates/jolt-riscv/src/instructions/virt/halt.rs`
(`jolt_instruction!`). -/
theorem haltFlags (instruction : JoltISA.Instr) :
    opcodeFlag instruction .Halt = instruction.haltKind?.isSome ∧
      opcodeFlag instruction .HaltPanic = (instruction.haltKind? == some JoltHaltKind.panic) := by
  unfold JoltISA.Instr.haltKind?
  split <;> simp_all [opcodeFlag]

/-- A jump column selects JAL, JALR or one of the two explicit halt kinds.
For example, JoltSuccess is a jump for its link write as well as a halt.
Jolt at `ff6fc6568`: `crates/jolt-riscv/src/instructions/virt/halt.rs`
(`jolt_instruction!`) and `instructions/i/{jal,jalr}.rs`. -/
theorem jumpCases (instruction : JoltISA.Instr)
    (jump : opcodeFlag instruction .Jump = true) :
    (∃ (dst : JoltISA.Dst) (imm : BitVec 64), instruction = .JAL dst imm) ∨
    (∃ (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64),
      instruction = .JALR dst base imm) ∨
    (∃ (kind : JoltHaltKind) (dst : JoltISA.Dst), instruction =
      match kind with | .success => .JoltSuccess dst | .panic => .Panic dst) := by
  simp only [opcodeFlag] at jump
  split at jump <;> simp_all
  · exact ⟨.success, _, rfl⟩
  · exact ⟨.panic, _, rfl⟩

end JoltMetadata
