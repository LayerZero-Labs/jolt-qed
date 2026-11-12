import JoltConstraints.WholeRun.Basic
import JoltConstraints.WholeRun.Io
import JoltConstraints.prover_config_facts

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- Jolt's load expansion records the effective address minus a mask below 8.
For example, an LH at address 10 records `10 - (10 &&& 6) = 8`. -/
private theorem load_first_mask {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) (source : SourceInstructionRow SourceInstruction)
    (i : RiscvInstruction) (hi : source.instruction = .riscv i)
    (width : Nat) (ea : BitVec 64)
    (access : i.memAccess row.preState = some (false, width, ea))
    (rows : List JoltInstructionRow) (emits : expand_instruction source = some rows)
    (head : rows.head? = some bytecode[row.rowIndex]) :
    ∃ mask : BitVec 64, mask.toNat < 8 ∧
      row.ram_address = some (ea - (ea &&& mask)).toNat := by
  cases i <;> simp only [RiscvInstruction.memAccess, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, false_and, true_and] at access
  all_goals obtain ⟨rfl, rfl⟩ := access
  case' LB => refine ⟨7, by decide, ?_⟩
  case' LBU => refine ⟨7, by decide, ?_⟩
  case' LH => refine ⟨6, by decide, ?_⟩
  case' LHU => refine ⟨6, by decide, ?_⟩
  case' LW => refine ⟨4, by decide, ?_⟩
  case' LWU => refine ⟨4, by decide, ?_⟩
  case' LD => refine ⟨0, by decide, ?_⟩
  all_goals
    simp only [expand_instruction, hi, SourceInstruction.expand, lbProgramAuto, lbuProgramAuto,
      lhProgramAuto, lhuProgramAuto, lwProgramAuto, lwuProgramAuto] at emits
    (try split_ifs at emits) <;>
      simp [ExpandedSource.ofProgram, ExpandedSource.ofNative, JoltISA.Program.instrs,
        SourceInstruction.rowCapacity, MAX_FINAL_ROWS_PER_SOURCE, stamp_sequence] at emits <;>
      subst rows <;>
      simp only [List.head?_cons, Option.some.injEq] at head <;>
      simp [TraceRow.ram_address, ← head, JoltISA.Instr.rewriteNative,
        load_effective_address]

/-- Jolt's tracer records a load's first-row RAM address within eight bytes below its effective
address, including loads into x0.
For example, an LB at address 15 records address 8. -/
theorem Block.FirstRowAt.load_address {trace : Trace} {b : Block} {k : Nat}
    (first : b.FirstRowAt trace k) {i : RiscvInstruction}
    (hi : b.row.instruction = .riscv i) {width : Nat} {ea : BitVec 64}
    (access : i.memAccess b.start = some (false, width, ea)) :
    ∃ (hk : k < trace.rows.size) (r : Nat),
      (trace.rows[k]'hk).ram_address = some r ∧ r ≤ ea.toNat ∧ ea.toNat < r + 8 := by
  obtain ⟨hk, start, rows, emits, head⟩ := first
  rw [start] at access
  obtain ⟨mask, small, recorded⟩ :=
    load_first_mask (trace.rows[k]'hk) b.row i hi width ea access rows emits head
  have le : ea &&& mask ≤ ea := by
    rw [BitVec.le_def, BitVec.toNat_and]
    exact Nat.and_le_left
  rw [BitVec.toNat_sub_of_le le, BitVec.toNat_and] at recorded
  have offset_le := Nat.and_le_left (n := ea.toNat) (m := mask.toNat)
  have offset_small := Nat.lt_of_le_of_lt
    (Nat.and_le_right (n := ea.toNat) (m := mask.toNat)) small
  exact ⟨hk, _, recorded, by omega, by omega⟩

/-- Jolt's prover accepts a recorded row address only when it is zero or at least the
initial layout's lowest address.
For example, the prover rejects recorded address 8 when the lowest address is 16. -/
theorem HonestTrace.prover_config_row_address_ok
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (hcfg : (trace.prover_config joltInstance).isSome)
    (row : TraceRow trace.bytecode) (member : row ∈ trace.rows)
    {r : Nat} (recorded : row.ram_address = some r) :
    r = 0 ∨ trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat ≤ r := by
  obtain ⟨config, accepted⟩ := Option.isSome_iff_exists.mp hcfg
  exact (trace.prover_config_ram_fits config accepted row member r recorded).imp_right And.left

/-- Jolt's prover address check and the exclusion of loads below 8 imply `NoLowLoad` for a
traced block whose layout is the initial layout.
For example, an LB at address 15 records 8, and acceptance forces the lowest address to be at
most 8 and hence at most 15. -/
theorem Block.FirstRowAt.noLowLoad {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {b : Block} {k : Nat} (first : b.FirstRowAt trace.toTrace k)
    (hcfg : (trace.prover_config joltInstance).isSome) {i : RiscvInstruction}
    (hi : b.row.instruction = .riscv i)
    (layout : b.pre.jolt_device.memory_layout = trace.initialState.jolt_device.memory_layout)
    (nonzero : i.NoZeroDoublewordLoad b.start) : i.NoLowLoad b.start := by
  intro width ea access
  obtain ⟨hk, r, recorded, below, above⟩ := first.load_address hi access
  have bounded := HonestTrace.prover_config_row_address_ok trace hcfg
    (trace.rows[k]'hk) (by simp) recorded
  have positive : r ≠ 0 := by
    have := nonzero width ea access
    omega
  have low := bounded.resolve_left positive
  change b.pre.jolt_device.memory_layout.get_lowest_address.toNat ≤ ea.toNat
  rw [layout]
  exact low.trans below

end WholeRun
