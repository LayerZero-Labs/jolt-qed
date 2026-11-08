import JoltConstraints.WholeRun.Run

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

## Memory

Jolt keeps RAM in `js.sail.mem` and the I/O window in `js.jolt_device`; Sail
keeps both in one byte map. Sail's byte at a RAM address is Jolt's
(`Mmu.ram_byte`, zero where Jolt has written nothing), and at an I/O address it
is what Jolt's device reads there (`JoltDevice.load?`, zero where the device
has no byte). Sail's memory holds a byte at every address from the lowest I/O
address to the end of Jolt's heap; Jolt's tracer rejects every access outside
that range.

The panic and termination words are where the two platforms differ
(`docs/riscv-alignment.md`, section 2): Jolt's device turns a store to the
panic byte into a flag and ignores stores to the rest of both words, while Sail
stores the bytes. The relation therefore does not equate those 16 bytes; it
requires only that they are present, and that Jolt's panic flag is set exactly
when Sail's panic word is nonzero.
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
        atomic_support := .AMONone
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

/-- One past the highest address Jolt's tracer accepts: the end of the heap. -/
def memHigh (device : JoltDevice) : Nat :=
  device.memory_layout.heap_end.toNat

/-- The panic and termination words, where Jolt's device is not memory. -/
def IsFlagWord (device : JoltDevice) (a : Nat) : Bool :=
  device.memory_layout.panic.toNat ≤ a && a < device.memory_layout.io_end.toNat

/-- Sail's byte at `a` for the Jolt state `jt`: Jolt's RAM byte at and above
`RAM_START_ADDRESS`, Jolt's device byte below it. -/
def sailByte (jt : SailJoltState) (a : Nat) : BitVec 8 :=
  if RAM_START_ADDRESS ≤ a then Mmu.ram_byte jt.sail.mem a
  else (jt.jolt_device.load? a).getD 0

/-- The 64-bit panic word in Sail's memory, or 0 if a byte is missing. -/
def sailPanicWord (device : JoltDevice) (s : SailState) : BitVec 64 :=
  (read_doubleword? s.mem.get? device.memory_layout.panic.toNat).getD 0

/-- Sail's registers for the Jolt state `jt`: the CSR and reservation overlay of
`System.systemProject`, `PC` at Jolt's next PC, any instruction-retired counter,
and the platform's memory regions. -/
def sailRegs (jt : SailJoltState) (pc m : BitVec 64) (inc : Bool) : SailState :=
  Step.setReg (Step.setReg (Step.setReg (Step.setReg (System.systemProject jt)
    Register.PC pc) Register.minstret m) Register.minstret_increment inc)
    Register.pma_regions platformPma

/-- **The relation of the whole run** between a Jolt state `jt` and a Sail
state `s`. -/
structure Related (jt : SailJoltState) (s : SailState) : Prop where
  /-- Registers: Sail's registers are Jolt's, through the overlay. -/
  regs : ∃ (pc m : BitVec 64) (inc : Bool),
    jt.sail.regs.get? Register.nextPC = some pc ∧ s.regs = (sailRegs jt pc m inc).regs
  /-- Memory outside the flag words: Sail's byte is Jolt's. -/
  mem : ∀ a, memLow jt.jolt_device ≤ a → a < memHigh jt.jolt_device →
    ¬ IsFlagWord jt.jolt_device a → s.mem.get? a = some (sailByte jt a)
  /-- The flag words are present in Sail's memory. -/
  flags_present : ∀ a, IsFlagWord jt.jolt_device a → ∃ b, s.mem.get? a = some b
  /-- Jolt's panic flag is set exactly when Sail's panic word is nonzero. -/
  panic : jt.jolt_device.panic = true ↔ sailPanicWord jt.jolt_device s ≠ 0
  /-- Jolt's output buffer stays inside the output region. -/
  outputs_size : jt.jolt_device.outputs.size ≤
    jt.jolt_device.memory_layout.max_output_size.toNat

/-- The output bytes in Sail's memory: the output region up to the panic word,
zero where a byte is missing. -/
def sailOutputs (device : JoltDevice) (s : SailState) : Array (BitVec 8) :=
  ((List.range device.memory_layout.max_output_size.toNat).map fun k =>
    (s.mem.get? (device.memory_layout.output_start.toNat + k)).getD 0).toArray

/-- Sail's memory at the start of a run: every byte from `memLow` to `memHigh`,
with the value `sailByte` gives, and Sail's panic and termination words zero. -/
def sailInitMem (jt : SailJoltState) : Std.ExtHashMap Nat (BitVec 8) :=
  (List.range (memHigh jt.jolt_device - memLow jt.jolt_device)).foldl
    (fun mem k =>
      let a := memLow jt.jolt_device + k
      mem.insert a (if IsFlagWord jt.jolt_device a then 0 else sailByte jt a))
    jt.sail.mem

/-- The Sail state a run starts from, given Jolt's initial state. -/
def sailInit (jt : SailJoltState) : SailState :=
  { sailRegs jt ((jt.sail.regs.get? Register.nextPC).getD 0) 0 false with
    mem := sailInitMem jt }

end WholeRun
