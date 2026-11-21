import LeanRV64D

/-!
# Ordering bits of atomic memory operations

Sail's AMO semantics passes the `aq` and `rl` bits to the memory interface only
as the `access_kind` of the read and write requests, which the sequential
memory model ignores. So every AMO behaves as its `aq = rl = false` form. This
file proves that.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

namespace Step

theorem read_ram_reserved_acquire (a : physaddr) (w : Nat) (m : Bool) :
    read_ram read_kind.Read_RISCV_reserved_acquire a w m =
      read_ram read_kind.Read_RISCV_reserved a w m := by
  rfl

theorem read_ram_reserved_strong_acquire (a : physaddr) (w : Nat) (m : Bool) :
    read_ram read_kind.Read_RISCV_reserved_strong_acquire a w m =
      read_ram read_kind.Read_RISCV_reserved a w m := by
  rfl

theorem write_ram_conditional_release (a : physaddr) (w : Nat) (d : BitVec (8 * w)) (m : Unit) :
    write_ram write_kind.Write_RISCV_conditional_release a w d m =
      write_ram write_kind.Write_RISCV_conditional a w d m := by
  rfl

theorem write_ram_conditional_strong_release (a : physaddr) (w : Nat) (d : BitVec (8 * w)) (m : Unit) :
    write_ram write_kind.Write_RISCV_conditional_strong_release a w d m =
      write_ram write_kind.Write_RISCV_conditional a w d m := by
  rfl

theorem mem_write_ea_amo (a : physaddr) (w : Nat) (aq rl : Bool) :
    mem_write_ea a w (aq && rl) rl true = mem_write_ea a w false false true := by
  cases aq <;> cases rl <;> rfl

theorem mem_read_amo (acc : MemoryAccessType mem_payload) (a : physaddr) (w : Nat) (aq rl : Bool) :
    mem_read acc a w aq (aq && rl) true = mem_read acc a w false false true := by
  cases aq <;> cases rl
  · rfl
  · rfl
  · unfold mem_read mem_read_priv mem_read_priv_meta checked_mem_read read_kind_of_flags
    simp only [pure_bind, Bool.true_or, Bool.false_or, Bool.and_false, read_ram_reserved_acquire]
  · unfold mem_read mem_read_priv mem_read_priv_meta checked_mem_read read_kind_of_flags
    simp only [pure_bind, Bool.true_or, Bool.false_or, Bool.and_true, read_ram_reserved_strong_acquire]

theorem mem_write_value_amo (a : physaddr) (w : Nat) (v : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (aq rl : Bool) :
    mem_write_value a w v acc (aq && rl) rl true = mem_write_value a w v acc false false true := by
  cases aq <;> cases rl
  · rfl
  · unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta checked_mem_write
      write_kind_of_flags
    simp only [pure_bind, Bool.or_true, Bool.false_and, write_ram_conditional_release]
  · rfl
  · unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta checked_mem_write
      write_kind_of_flags
    simp only [pure_bind, Bool.or_true, Bool.and_true, write_ram_conditional_strong_release]

/-- An AMO's `aq` and `rl` bits do not change its semantics. -/
theorem execute_AMO_flags (op : amoop) (aq rl : Bool) (rs2 rs1 : regidx) (width : Nat)
    (rd : regidx) :
    execute_AMO op aq rl rs2 rs1 width rd = execute_AMO op false false rs2 rs1 width rd := by
  unfold execute_AMO
  simp only [mem_write_ea_amo, mem_read_amo, mem_write_value_amo, Bool.false_and]

end Step
