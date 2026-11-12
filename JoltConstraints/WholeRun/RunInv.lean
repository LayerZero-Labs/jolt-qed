import JoltConstraints.WholeRun.SystemInv
import JoltConstraints.WholeRun.Io
import JoltConstraints.WholeRun.IoAmo
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

/-!
# Run invariants for the block theorems

The block theorems of the whole-run proof (`block_simulates`,
`block_simulates_io`) take premises about the Jolt state a block starts from.
`RunInv` bundles the ones that hold along the whole run: each holds in an honest
trace's initial state, and every block that runs preserves it.

Each fact below is classified as an **invariant** (proved from the model), a
**platform premise** (a fact about the ELF or the platform that the model does
not derive) or a **documented deviation** (a place where Jolt and Sail differ;
`docs/riscv-alignment.md`, section 2).

| Fact | Class | Where |
| --- | --- | --- |
| legal system values | invariant | `SystemInv` |
| even PC | platform premise `RowsAligned`, then invariant | `Block.Runs.pc_even` |
| heap end below `2^64 - 8` | platform premise `HeapNoWrap`, then invariant | `RunInv.heap_no_wrap` |
| LR/SC address in RAM | invariant | `access_classified` |
| AMO address in RAM or the I/O window | invariant | `access_classified` |
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

/-- Platform premise: every instruction row of the image is at an even address.
For example, a text section starting at `0x80000000` gives rows at `0x80000000`,
`0x80000004` (after a 4-byte instruction) and `0x80000006` (after a 2-byte one),
while a text section starting at `0x80000001` would give odd rows.
Jolt's loader does not enforce this: `decode_elf` in
`jolt/crates/jolt-program/src/image/elf.rs` takes each executable section
(`SectionKind::Text`, at or above `RAM_START_ADDRESS`), merges overlapping ranges
(`merge_ranges`) and calls `decode_text_section` at the range's start, where an
instruction's address is the start plus its offset. That offset advances by 2
after a compressed parcel and by 4 after a 32-bit word, so every row's address
has the parity of its range's start, and the start is a section address that no
code checks. Linkers align `.text` to at least two bytes, so real ELFs satisfy
the premise. It can be discharged later by rejecting a text section at an odd
address in `decode_elf`, or by making it a field of `Rv64ProgramImage`. -/
def Rv64ProgramImage.RowsAligned {Source : Type} (image : Rv64ProgramImage Source) : Prop :=
  ∀ row ∈ image.instructions, row.address.getLsbD 0 = false

/-- Platform premise: the heap of the layout `MemoryLayout.new` builds for the
instance ends at least eight bytes below `2^64`.
For example, a program image ending at `0x80010000` with stack size `0x10000` and
heap size `0x100000` gives `heap_end = 0x80120080`, far below the bound.
`MemoryLayout.new` only checks that `heap_end` fits in 64 bits, and the program
size is the image's `program_end - RAM_START_ADDRESS`, which need not be a multiple
of eight: a `program_end` of `2^64 - 129` with all configured sizes zero gives
`heap_end = 2^64 - 1`. Real ELFs end far below that, as Jolt's tracer allocates
`heap_end - RAM_START_ADDRESS` bytes of RAM when it starts
(`ram_backing_end` in `JoltISA/DeviceMemory.lean`). -/
def JoltInstance.HeapNoWrap {Source : Type} (joltInstance : JoltInstance Source) : Prop :=
  ∀ layout, joltInstance.memory_layout = some layout → layout.heap_end.toNat ≤ 2 ^ 64 - 8

namespace WholeRun

open JoltISA

-- Reuse the rounding lemma of `Io.lean` without changing that module.
local macro "ioHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Io
    (`WholeRun ++ n.getId)))

/-! ### Even program counter -/

/-- **Run invariant**, given the platform premise `RowsAligned`: a running block's
instruction is at an even address.
For example, with all rows aligned, a block at `0x80000006` has bit zero clear. -/
theorem Block.Runs.pc_even {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (h : program.RowsAligned) (hruns : b.Runs program) :
    b.row.address.getLsbD 0 = false :=
  h b.row (Array.mem_of_find?_eq_some hruns.at_row)

/-! ### Which memory an instruction touches -/

/-- Rounding an address down to eight bytes keeps it in RAM, because
`RAM_START_ADDRESS` is a multiple of eight. For example,
`0x80000007 &&& -8 = 0x80000000`. -/
private theorem aligned_or_below (ea : BitVec 64) :
    RAM_START_ADDRESS ≤ (ea &&& (-8 : BitVec 64)).toNat ∨ ea.toNat < RAM_START_ADDRESS := by
  have h : (ea &&& (-8 : BitVec 64)).toNat = ea.toNat / 8 * 8 := (ioHelper% toNat_and_neg8) ea
  unfold RAM_START_ADDRESS at *
  omega

/-- A word atomic's rounded address is in RAM whenever its source address is. -/
private theorem amoWordBase_ram (v : BitVec 64) (h : RAM_START_ADDRESS ≤ v.toNat) :
    RAM_START_ADDRESS ≤ (amoWordBase v).toNat := by
  rcases aligned_or_below v with h' | h'
  · exact h'
  · exact absurd h (Nat.not_le.mpr h')

/-- A successful `VirtualAssertLTE` leaves the state unchanged and says its first
operand is at most its second. For example, asserting `2^31 ≤ x5` retires only when
`x5 ≥ 2^31`. -/
private theorem assertLTE_ok {a b : Src} {imm : BitVec 128} {s t : SailJoltState}
    {r : ExecutionResult} (h : execInstr (.VirtualAssertLTE a b imm) s = .ok r t) :
    t = s ∧ (sourceValue a s).toNat ≤ (sourceValue b s).toNat := by
  simp only [execInstr] at h
  cases ha : readSrc a s with
  | error e u => simp [bind, EStateM.bind, ha] at h
  | ok x u =>
    obtain ⟨hu, hx⟩ := lookup_readSrc_value _ _ _ _ ha
    subst u
    cases hb : readSrc b s with
    | error e u => simp [bind, EStateM.bind, ha, hb] at h
    | ok y w =>
      obtain ⟨hw, hy⟩ := lookup_readSrc_value _ _ _ _ hb
      subst w
      by_cases hxy : x.toNat ≤ y.toNat
      · simp only [bind, EStateM.bind, ha, hb, hxy, ite_true, pure, EStateM.pure] at h
        cases h
        exact ⟨rfl, hx ▸ hy ▸ hxy⟩
      · simp only [bind, EStateM.bind, ha, hb, hxy, ↓reduceIte] at h
        cases h

/-- The opening rows of every LR and SC expansion, `LUI v 0x80000000` then
`VirtualAssertLTE v rs1`, retire only when `rs1 ≥ RAM_START_ADDRESS`. For example,
`LR.W` at `rs1 = 0x40000000` fails its assertion. -/
private theorem assert_prefix {v : JoltISA.VReg} (hv : ¬ v.toNat < 32) {rs1 : regidx}
    {rest : Program} {s t : SailJoltState}
    (h : execProgram (.instr (.LUI (.vreg v) (2147483648 : BitVec 64))
      (.instr (.VirtualAssertLTE (.vreg v) (.xreg rs1) 0) rest)) s = .ok RETIRE_SUCCESS t) :
    RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) s).toNat := by
  let s1 : SailJoltState := { s with vregs := fun r => if r = v then 2147483648 else s.vregs r }
  have h1 : execInstr (.LUI (.vreg v) (2147483648 : BitVec 64)) s = .ok RETIRE_SUCCESS s1 := by
    simp only [execInstr, writeDst, writeVReg, hv, ite_false, modify, modifyGet,
      MonadStateOf.modifyGet, bind, EStateM.bind, pure, EStateM.pure, s1]
    rfl
  cases h2 : execInstr (.VirtualAssertLTE (.vreg v) (.xreg rs1) 0) s1 with
  | error e u =>
    simp only [execProgram, bind, EStateM.bind, h1, h2, RETIRE_SUCCESS, reduceCtorEq] at h
  | ok r u =>
    obtain ⟨-, hle⟩ := assertLTE_ok h2
    have hx : sourceValue (.vreg v) s1 = 2147483648 := by simp [sourceValue, s1]
    have hy : sourceValue (.xreg rs1) s1 = sourceValue (.xreg rs1) s := by cases rs1; rfl
    rw [hx, hy] at hle
    simpa [RAM_START_ADDRESS] using hle

/-- A block whose source is LR.W, LR.D, SC.W or SC.D retires only with `rs1` in RAM:
the generated expansions (`lrwProgramAuto`, `lrdProgramAuto`, `scwProgramAuto`,
`scdProgramAuto`) open with `LUI v 0x80000000; VirtualAssertLTE v rs1`, as Rust's
`expand_lrw`, `expand_lrd` and `expand_sc_success` do.
For example, `SC.D` at `rs1 = 0x40000000` cannot retire. -/
private theorem lrsc_ram {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) {i : RiscvInstruction} (hrow : b.row.instruction = .riscv i)
    (rd rs1 rs2 : regidx) (p : Program)
    (hexpand : b.row.instruction.expand = some (ExpandedSource.ofProgram p))
    (hp : p = lrwProgramAuto rd rs1 rs2 ∨ p = lrdProgramAuto rd rs1 rs2 ∨
      p = scwProgramAuto rd rs1 rs2 ∨ p = scdProgramAuto rd rs1 rs2)
    (hadvice : b.row.instruction.honestTracerAdvice b.start = []) :
    RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) b.start).toNat := by
  have hseq : Program.seq p.instrs = p := by
    rcases hp with rfl | rfl | rfl | rfl
    all_goals
      simp only [lrwProgramAuto, lrdProgramAuto, scwProgramAuto, scdProgramAuto]
      split <;> rfl
  have hrun := block_program_run b.row b.start b.post p hexpand hadvice hseq
    (hruns.executes_riscv hrow)
  rcases hp with rfl | rfl | rfl | rfl
  all_goals
    simp only [lrwProgramAuto, lrdProgramAuto, scwProgramAuto, scdProgramAuto] at hrun
    split at hrun
    all_goals exact assert_prefix (by decide) hrun

/-- **Access classification, with atomics on the I/O window.** A block that runs and is a
RISC-V instruction accesses RAM, accesses the I/O window with a load or store, or is an
atomic on the I/O window, so `block_simulates`, `block_simulates_io` or
`block_simulates_io_amo` applies to it.
Loads and stores are classified by their effective address: below `RAM_START_ADDRESS` it is an
`IoAccess`, and from there on the doubleword base is in RAM because `RAM_START_ADDRESS` is a
multiple of eight. LR and SC are in RAM because their expansions assert
`rs1 ≥ RAM_START_ADDRESS`. An AMO's accessed doubleword is either at or above
`RAM_START_ADDRESS`, a `RamAccess`, or below it, an `IoAmoAccess`. Every other instruction has
no access.
For example, `AMOADD.D` through `0x40000010` is an `IoAmoAccess`, and through
`0x80000010` a `RamAccess`. -/
theorem access_classified (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i) :
    RamAccess i b.start ∨ i.IoAccess b.start ∨ IoAmoAccess i b.start := by
  have hlr : ∀ (rd rs1 rs2 : regidx) (p : Program),
      b.row.instruction.expand = some (ExpandedSource.ofProgram p) →
      b.row.instruction.honestTracerAdvice b.start = [] →
      (p = lrwProgramAuto rd rs1 rs2 ∨ p = lrdProgramAuto rd rs1 rs2 ∨
        p = scwProgramAuto rd rs1 rs2 ∨ p = scdProgramAuto rd rs1 rs2) →
      RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) b.start).toNat := fun rd rs1 rs2 p he hadv hp =>
    lrsc_ram hruns hrow rd rs1 rs2 p he hp hadv
  cases i
  case LR_W rd rs1 aq rl =>
    exact Or.inl (amoWordBase_ram _ (hlr rd rs1 (regidx.Regidx 0) _ (by rw [hrow]; rfl)
      (by rw [hrow]; rfl) (Or.inl rfl)))
  case LR_D rd rs1 aq rl =>
    exact Or.inl (hlr rd rs1 (regidx.Regidx 0) _ (by rw [hrow]; rfl) (by rw [hrow]; rfl)
      (Or.inr (Or.inl rfl)))
  case SC_W rd rs1 rs2 aq rl =>
    exact Or.inl (amoWordBase_ram _ (hlr rd rs1 rs2 _ (by rw [hrow]; rfl)
      (by rw [hrow]; rfl) (Or.inr (Or.inr (Or.inl rfl)))))
  case SC_D rd rs1 rs2 aq rl =>
    exact Or.inl (hlr rd rs1 rs2 _ (by rw [hrow]; rfl) (by rw [hrow]; rfl)
      (Or.inr (Or.inr (Or.inr rfl))))
  case AMOSWAP_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOADD_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOXOR_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOAND_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOOR_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMIN_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMAX_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMINU_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMAXU_W rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (amoWordBase (sourceValue (.xreg rs1) b.start)).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOSWAP_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOADD_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOXOR_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOAND_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOOR_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMIN_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMAX_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMINU_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  case AMOMAXU_D rd rs1 rs2 aq rl =>
    exact (Nat.lt_or_ge (sourceValue (.xreg rs1) b.start).toNat RAM_START_ADDRESS).symm.imp id
      (fun h => Or.inr ⟨_, rfl, h⟩)
  all_goals
    first
    | exact Or.inl trivial
    | (rename_i rs1 imm
       rcases aligned_or_below (load_effective_address (sourceValue (.xreg rs1) b.start) imm)
         with h | h
       · exact Or.inl h
       · refine Or.inr (Or.inl ⟨_, _, _, rfl, ?_⟩)
         exact h)

/-! ### The bundle -/

/-- The Jolt-side facts the block theorems need that hold along the whole run:
the legal system values (`SystemInv`, an invariant) and the heap bound
(`heap_no_wrap`, an invariant given the platform premise `JoltInstance.HeapNoWrap`).
The PC parity and the access class are properties of the block being run, derived
from `RowsAligned` (`Block.Runs.pc_even`) and from the instruction (`access_classified`).
`program` is the image the run executes, which later invariants about its code
depend on.
For example, a state with all virtual registers zero and the layout of a small
program satisfies it. -/
structure RunInv (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState) : Prop where
  system : SystemInv jt
  heap_no_wrap : jt.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8

/-- An honest trace begins with the run invariants, given the heap premise.
For example, the layout of the instance's own memory configuration is the one
`HeapNoWrap` speaks about. -/
theorem RunInv.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (hheap : joltInstance.HeapNoWrap) : RunInv joltInstance.program trace.initialState :=
  ⟨SystemInv.initialState trace,
    hheap _ (initial_state_device joltInstance privateInputs trace.initialState
      trace.initialized).1⟩

/-- Running a block keeps the memory layout: no Jolt row and no `advance_pc` changes
it. For example, a store to the output region changes `outputs` and `panic` only. -/
theorem Block.Runs.layout_eq {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) :
    b.post.jolt_device.memory_layout = b.pre.jolt_device.memory_layout := by
  obtain ⟨-, instrs, -, -, hrun⟩ := hruns.executes
  exact (JoltIOSetupFrame.execProgram_rule (Program.seq instrs) b.start b.post _ hrun).1

/-- Every block that runs preserves the run invariants, given aligned rows.
For example, an ECALL block keeps the system values legal and the heap bound. -/
theorem RunInv.of_block {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) (hrows : program.RowsAligned) (h : RunInv program b.pre) :
    RunInv program b.post :=
  ⟨SystemInv.of_block hruns (hruns.pc_even hrows) h.system,
    by rw [hruns.layout_eq]; exact h.heap_no_wrap⟩

end WholeRun
