import JoltBytecode.Decode.Configuration

/-!
# The Jolt–Sail relation of the whole run

`Run.lean` chains per-block simulations for any relation. This file fixes the
relation the whole-run theorem uses, the Sail platform it runs on, the Sail
state a run starts from, and how a Sail state reports its outputs.

## The platform

Sail's memory regions are the two regions of `sail-import/rv64d_jolt.json`
(`memory.regions`): the I/O window `[0x4000_0000, 0x8000_0000)`, readable and
writable, and RAM `[0x8000_0000, 2^64)`. The Sail configuration file is read by
Sail's C++ emulator only; in the Lean model `pma_regions` is an ordinary
register, so the whole-run theorem sets it to `platformPma` in its initial
state, and no instruction writes it afterwards.

Sail's `misa` is likewise Sail's own: the relation sets it to `Decode.resetMisa`,
the value `reset_misa` gives (RV64 with I, M, A and C), whatever Jolt's embedded
copy holds. Jolt accepts only six CSRs (`mstatus`, `mtvec`, `mscratch`, `mepc`,
`mcause`, `mtval`), and `misa` is not one of them. Jolt's rows look at its C bit
only to test a branch target's alignment, and a run that retires never fails that
test (`execProgram_withMisa`).

## Memory

Jolt and Sail keep inputs, advice, outputs, the I/O gap and ordinary RAM in the
same byte map.
The relation compares their zero-default bytes directly at every address.
Sail's map also contains every byte from the lowest I/O address to the end of
the padded RAM backing, which the tracer's RAM guards enforce.
Initialization uses Jolt's initialized shared map without reconstructing I/O.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

open JoltISA

/-- The I/O window, `memory.regions[0]` of `sail-import/rv64d_jolt.json`. -/
def ioRegion : PMA_Region :=
  { base := 0x40000000#64
    size := 0x40000000#64
    attributes :=
      { cacheable := false
        coherent := true
        executable := false
        readable := true
        writable := true
        read_idempotent := true
        write_idempotent := true
        misaligned_fault := .AlignmentFault
        atomic_support := .AMOArithmetic
        reservability := .RsrvNone
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false }
    include_in_device_tree := false }

/-- RAM, `memory.regions[1]` of `sail-import/rv64d_jolt.json`. -/
def ramRegion : PMA_Region :=
  { base := 0x80000000#64
    size := 0xFFFFFFFF80000000#64
    attributes :=
      { cacheable := true
        coherent := true
        executable := true
        readable := true
        writable := true
        read_idempotent := true
        write_idempotent := true
        misaligned_fault := .NoFault
        atomic_support := .AMOArithmetic
        reservability := .RsrvEventual
        supports_cbo_zero := false
        supports_pte_read := false
        supports_pte_write := false }
    include_in_device_tree := true }

/-- Sail's memory regions, in the order of the configuration file. -/
def platformPma : List PMA_Region := [ioRegion, ramRegion]

/-- The lowest address Jolt's tracer and prover accept: the start of the advice
regions. -/
def memLow (device : JoltDevice) : Nat :=
  device.memory_layout.get_lowest_address.toNat

/-- The end of the tracer's padded RAM backing.
For example, a complete doubleword must end no later than this address. -/
def memHigh (device : JoltDevice) : Nat :=
  Mmu.ram_backing_end device

/-- Sail's reset `misa` enables compressed instructions. -/
theorem resetMisa_c : _get_Misa_C Decode.resetMisa = 1#1 := by decide

/-- Sail's registers for the Jolt state `jt`: the CSR and reservation overlay of
`System.systemProject`, `PC` at Jolt's next PC, any instruction-retired counter,
the platform's memory regions, and Sail's reset `misa`. -/
def sailRegs (jt : SailJoltState) (pc m : BitVec 64) (inc : Bool) : SailState :=
  Step.setReg (Step.setReg (Step.setReg (Step.setReg (Step.setReg (System.systemProject jt)
    Register.PC pc) Register.minstret m) Register.minstret_increment inc)
    Register.pma_regions platformPma) Register.misa Decode.resetMisa

/-- **The relation of the whole run** between a Jolt state `jt` and a Sail
state `s`. -/
structure Related (jt : SailJoltState) (s : SailState) : Prop where
  /-- Registers: Sail's registers are Jolt's, through the overlay. -/
  regs : ∃ (pc m : BitVec 64) (inc : Bool),
    jt.sail.regs.get? Register.nextPC = some pc ∧ s.regs = (sailRegs jt pc m inc).regs
  /-- Sail's state satisfies the facts that make `try_step` a plain
  fetch-decode-execute step. -/
  inv : Step.StepInvariant s
  /-- Sail's HTIF device is off: no `tohost` address is configured. -/
  htif : s.regs.get? Register.htif_tohost_base = some none
  /-- Every shared byte agrees, with zero for a missing byte on either side.
  For example, this compares input bytes and ordinary RAM by the same rule. -/
  ram : ∀ a, Mmu.ram_byte s.mem a = Mmu.ram_byte jt.sail.mem a
  /-- Sail's memory holds every byte from `memLow` to `memHigh`. -/
  present : ∀ a, memLow jt.jolt_device ≤ a → a < memHigh jt.jolt_device →
    ∃ b, s.mem.get? a = some b
  /-- Jolt's memory layout is one `MemoryLayout.new` builds; no row changes it. -/
  layout : ∃ config, MemoryLayout.new config = some jt.jolt_device.memory_layout

/-- **Sail's `misa` is its reset value.** Whatever Jolt's embedded copy holds, a Sail
state related to `jt` has `Decode.resetMisa` there, so fetch and decode see the
configuration `reset_misa` gives. -/
theorem Related.misa {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    s.regs.get? Register.misa = some Decode.resetMisa := by
  obtain ⟨pc, m, inc, _, hregs⟩ := h.regs
  rw [hregs]
  exact Std.ExtDHashMap.get?_insert_self

/-- Sail starts from Jolt's initialized shared memory and the platform register
overlay.
For example, input bytes installed by `JoltDevice.initialMem` are used directly. -/
def sailInit (jt : SailJoltState) : SailState :=
  sailRegs jt ((jt.sail.regs.get? Register.nextPC).getD 0) 0 false

end WholeRun
