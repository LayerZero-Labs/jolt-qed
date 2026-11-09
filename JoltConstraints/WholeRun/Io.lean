import JoltConstraints.WholeRun.SystemBlocks
import JoltConstraints.Soundness.Layer5.DeviceMemory
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.StoreExec
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.FloorLoad
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LB_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LBU_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LH_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LHU_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LW_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LWU_main
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sb_main
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sh_main
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sw_main
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualWindowMask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualPext

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace RiscvInstruction

/-- The load or store a source instruction performs on state `js`: whether it
stores, its width in bytes, and its effective address `rs1 + imm`.
For example, `LH` with `rs1 = 0x40000010` and `imm = 2` is a load of two bytes at
`0x40000012`. Other instructions have no such access. -/
def memAccess : RiscvInstruction → SailJoltState → Option (Bool × Nat × BitVec 64)
  | .LB _ rs1 imm, js | .LBU _ rs1 imm, js =>
      some (false, 1, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LH _ rs1 imm, js | .LHU _ rs1 imm, js =>
      some (false, 2, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LW _ rs1 imm, js | .LWU _ rs1 imm, js =>
      some (false, 4, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LD _ rs1 imm, js =>
      some (false, 8, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SB _ rs1 imm, js =>
      some (true, 1, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SH _ rs1 imm, js =>
      some (true, 2, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SW _ rs1 imm, js =>
      some (true, 4, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SD _ rs1 imm, js =>
      some (true, 8, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | _, _ => none

/-- The register value a store writes to memory; stores keep their low bytes.
For example, `SB x5, 0(x6)` stores the low byte of `x5`. Other instructions give 0. -/
def storeData : RiscvInstruction → SailJoltState → BitVec 64
  | .SB rs2 _ _, js | .SH rs2 _ _, js | .SW rs2 _ _, js | .SD rs2 _ _, js =>
      JoltISA.sourceValue (.xreg rs2) js
  | _, _ => 0

/-- Platform premise: the instruction is one of the loads LB, LH, LW, LD, LBU, LHU, LWU
or stores SB, SH, SW, SD, and its effective address `rs1 + imm` on `js` lies below
`RAM_START_ADDRESS`, in Sail's I/O window and Jolt's device.
For example, `LW` from `0x40000010` satisfies it and `LW` from `0x80000010` does not. -/
def IoAccess (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∃ store width ea, i.memAccess js = some (store, width, ea) ∧
    ea.toNat < JoltISA.RAM_START_ADDRESS

/-- Documented deviation (`docs/riscv-alignment.md`, section 2): a load reads no byte of
the panic and termination words.
Jolt's device returns the panic flag and the termination word through one load, while
Sail returns the stored bytes, which the whole-run relation does not equate.
For example, a `LW` at the panic address violates it. -/
def NoFlagWordLoad (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∀ width ea, i.memAccess js = some (false, width, ea) →
    ∀ k < width, WholeRun.IsFlagWord js.jolt_device (ea.toNat + k) = false

/-- Documented deviation (`docs/riscv-alignment.md`, section 2): a load does not read below
`memLow`, the lowest address Jolt's tracer and prover accept.
Jolt's tracer accepts a read at any address up to `RAM_START_ADDRESS - 8` and returns
zero there, while Sail faults on an address with no memory.
For example, a `LB` from address `0x40000000` violates it whenever `memLow` is higher. -/
def NoLowLoad (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∀ width ea, i.memAccess js = some (false, width, ea) →
    WholeRun.memLow js.jolt_device ≤ ea.toNat

/-- Documented deviation (`docs/riscv-alignment.md`, section 2): a store that writes the
panic doubleword leaves Sail's panic word nonzero.
Jolt's narrow stores rewrite the whole doubleword, so any store touching the panic
doubleword sets Jolt's panic flag, even when the stored value is zero; Sail stores
only the bytes written.
Stated for every old word `old` that is nonzero exactly when Jolt's flag is set and
every word `new` that is `old` with the stored bytes spliced in at the access offset.
For example, `SB` of 1 at the panic address satisfies it, while `SB` of 0 over a word
whose only nonzero byte is that byte does not. -/
def PanicStoreNonzero (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∀ width ea, i.memAccess js = some (true, width, ea) →
    ea.toNat / 8 * 8 = js.jolt_device.memory_layout.panic.toNat →
    ∀ old new : BitVec 64, (old ≠ 0 ↔ js.jolt_device.panic = true) →
      (∀ k < 8, new.extractLsb' (8 * k) 8 =
        if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + width then
          (i.storeData js).extractLsb' (8 * (k - ea.toNat % 8)) 8
        else old.extractLsb' (8 * k) 8) →
      new ≠ 0

end RiscvInstruction

namespace WholeRun

attribute [local instance] Classical.propDecidable

local macro "bridgeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Bridge
    (`WholeRun ++ n.getId)))
local macro "blockHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.BlockStep
    (`WholeRun ++ n.getId)))
local macro "bundleHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Bundles
    (`WholeRun ++ n.getId)))
local macro "storeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
    (`StoreProgramBlocks ++ n.getId)))
local macro "deviceHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.Soundness.Layer5.DeviceMemory
    (`JoltConstraints.Soundness ++ n.getId)))

/-- The memory part of `Related`, for any device and Sail state. -/
structure MemRel (d : JoltDevice) (s : SailState) : Prop where
  present : ∀ a, memLow d ≤ a → a < memHigh d → ∃ b, s.mem.get? a = some b
  io : ∀ a, memLow d ≤ a → a < RAM_START_ADDRESS → IsFlagWord d a = false →
    s.mem.get? a = some ((d.load? a).getD 0)
  panic : d.panic = true ↔ sailPanicWord d s ≠ 0
  layout : ∃ config, MemoryLayout.new config = some d.memory_layout
  outputs_size : d.outputs.size ≤ d.memory_layout.max_output_size.toNat

/-- The memory relation depends on a Sail state only through its memory.
For example, a state with only different registers satisfies it too. -/
theorem MemRel.of_mem_eq {d : JoltDevice} {s t : SailState} (h : MemRel d s)
    (hm : t.mem = s.mem) : MemRel d t := by
  refine ⟨?_, ?_, ?_, h.layout, h.outputs_size⟩
  · simpa only [hm] using h.present
  · simpa only [hm] using h.io
  · simpa only [sailPanicWord, hm] using h.panic

theorem Related.memRel {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    MemRel jt.jolt_device s :=
  ⟨h.present, h.io, h.panic, h.layout, h.outputs_size⟩


/-- The geometry of Jolt's I/O window that a generated layout fixes.
For example, the panic word starts right after the output buffer, and the
termination word is the next eight bytes. -/
structure IoGeo (d : JoltDevice) : Prop where
  low : 0x40000000 ≤ memLow d
  lowAligned : memLow d % 8 = 0
  lowOut : memLow d ≤ d.memory_layout.output_start.toNat
  outAligned : d.memory_layout.output_start.toNat % 8 = 0
  panicEq : d.memory_layout.panic.toNat =
    d.memory_layout.output_start.toNat + d.memory_layout.max_output_size.toNat
  maxAligned : d.memory_layout.max_output_size.toNat % 8 = 0
  termEq : d.memory_layout.termination.toNat = d.memory_layout.panic.toNat + 8
  endEq : d.memory_layout.io_end.toNat = d.memory_layout.termination.toNat + 8
  endBound : d.memory_layout.io_end.toNat ≤ RAM_START_ADDRESS
  inputEnd : d.memory_layout.input_end.toNat = d.memory_layout.output_start.toNat
  trustedEnd : d.memory_layout.trusted_advice_end.toNat ≤ d.memory_layout.output_start.toNat
  untrustedEnd : d.memory_layout.untrusted_advice_end.toNat ≤ d.memory_layout.output_start.toNat
  heapBound : RAM_START_ADDRESS ≤ d.memory_layout.heap_end.toNat

/-- The heap ends at or above the start of RAM.
For example, a layout with an empty program, stack and heap ends its heap at the stack
canary above `RAM_START_ADDRESS`. -/
private theorem new_heap_end_bound (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    RAM_START_ADDRESS ≤ layout.heap_end.toNat := by
  unfold MemoryLayout.new at built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨stackEnd, stackEndAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨stackStart, stackStartAdded, built⟩ := built
  rw [bind_some_iff] at built
  obtain ⟨heapEnd, heapEndAdded, built⟩ := built
  have layoutEq := Option.some.inj built
  rw [bind_some_iff] at stackStartAdded
  obtain ⟨withCanary, canaryAdded, stackStartAdded⟩ := stackStartAdded
  have e1 := checkedAdd_some stackEndAdded
  have e2 := checkedAdd_some canaryAdded
  have e3 := checkedAdd_some stackStartAdded
  have e4 := checkedAdd_some heapEndAdded
  rw [← layoutEq]
  dsimp only
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := heapEnd) (by omega)]
  omega

theorem IoGeo.of_layout (d : JoltDevice)
    (h : ∃ config, MemoryLayout.new config = some d.memory_layout) : IoGeo d := by
  obtain ⟨config, hb⟩ := h
  have hlow := (deviceHelper% layout_above_peripherals) config _ hb
  have hal := new_lowest_address_aligned config _ hb
  have hord := new_io_ordered config _ hb
  have hin := new_input_word_aligned config _ hb
  have hout := new_outputs_after_inputs config _ hb
  have hgeo := new_io_geometry config _ hb
  have hadv := new_advice_regions config _ hb
  have hie := congrArg BitVec.toNat ((deviceHelper% input_end_eq_output) config _ hb)
  have hheap := new_heap_end_bound config _ hb
  have hm : memLow d = d.memory_layout.get_lowest_address.toNat := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega


/-! ### Alignment -/

/-- A mask `2 ^ k - 1` clearing an address gives divisibility by `2 ^ k`.
For example, `addr &&& 3 = 0` gives `addr.toNat % 4 = 0`. -/
private theorem mod_of_and (addr : BitVec 64) (k : Nat) (hk : k < 64)
    (h : addr &&& BitVec.ofNat 64 (2 ^ k - 1) = 0) : addr.toNat % 2 ^ k = 0 := by
  have h' := congrArg BitVec.toNat h
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod] at h'
  simpa using h'

private theorem mod_of_and1 (addr : BitVec 64) (h : addr &&& (1 : BitVec 64) = 0) :
    addr.toNat % 2 = 0 := by
  simpa using mod_of_and addr 1 (by norm_num) (by simpa using h)

private theorem mod_of_and3 (addr : BitVec 64) (h : addr &&& (3 : BitVec 64) = 0) :
    addr.toNat % 4 = 0 := by
  simpa using mod_of_and addr 2 (by norm_num) (by simpa using h)

private theorem mod_of_and7 (addr : BitVec 64) (h : addr &&& (7 : BitVec 64) = 0) :
    addr.toNat % 8 = 0 := by
  simpa using mod_of_and addr 3 (by norm_num) (by simpa using h)

/-- A naturally aligned physical address satisfies Sail's aligned-address test.
For example, address 0x40000002 is aligned for a halfword. -/
private theorem aligned_paddr (addr : BitVec 64) (n : Nat) (h : addr.toNat % n = 0) :
    is_aligned_paddr (.Physaddr addr) n = true := by
  unfold is_aligned_paddr Sail.BitVec.toNatInt
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % n)) == (0 : Int)) = true
  rw [h]
  rfl

/-! ### Sail's I/O window is plain memory -/

private theorem io_matching (addr : BitVec 64) (n : Nat)
    (hlo : 0x40000000 ≤ addr.toNat) (hn : 0 < n) (hwidth : n ≤ 8)
    (hhi : addr.toNat + n ≤ JoltISA.RAM_START_ADDRESS) :
    matching_pma platformPma (.Physaddr addr) n = some ioRegion := by
  have haddr := addr.isLt
  simp only [JoltISA.RAM_START_ADDRESS] at hhi
  have hio := (bundleHelper% range_subset_nat) addr 0x40000000 0x40000000 n
    (by simpa using hlo) (by omega) (by change addr.toNat - 0x40000000 + n < 2 ^ 64; omega)
  have hyes : addr.toNat - 0x40000000 + n ≤ 0x40000000 := by omega
  simp only [show (0x40000000 : BitVec 64).toNat = 0x40000000 by rfl, hyes,
    decide_true] at hio
  change range_subset addr (BitVec.ofNat 64 n) 0x40000000#64 0x40000000#64 = true at hio
  have hzero : zero_extend (m := 64) addr = addr := by
    simpa only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
      using BitVec.setWidth_eq addr
  have hbits : to_bits (l := 64) n = BitVec.ofNat 64 n := by
    change (BitVec.ofInt 65 (n : Int)).extractLsb' 0 64 = _
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
    simp
  simp only [platformPma, matching_pma, matching_pma_bits_range, bits_of_physaddr,
    hzero, hbits, ioRegion, ramRegion]
  rw [hio]
  rfl

/-- Sail's PMP and PMA checks accept an aligned load or store inside the I/O window.
For example, a word at 0x40000010 is readable and writable. -/
private theorem io_checks (s : SailState) (addr : BitVec 64) (n : Nat)
    (hpma : s.regs.get? Register.pma_regions = some platformPma)
    (hlo : 0x40000000 ≤ addr.toNat) (hn : 0 < n) (hwidth : n ≤ 8)
    (hhi : addr.toNat + n ≤ JoltISA.RAM_START_ADDRESS)
    (halign : addr.toNat % n = 0) :
    Assumptions.LoadPmpOk addr n s ∧ Assumptions.StorePmpOk addr n s := by
  have hread := readReg_eq_of_get? Register.pma_regions s _ hpma
  have hmatch := io_matching addr n hlo hn hwidth hhi
  have hal := aligned_paddr addr n halign
  simp [Assumptions.LoadPmpOk, Assumptions.StorePmpOk,
    phys_access_check, HartConfig.pmpCheck_run, pmaCheck, hread, hmatch, ioRegion, hal,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    LeanRV64D.Functions.not, bind, EStateM.bind, pure, EStateM.pure]

/-- Neither the CLINT nor HTIF covers an address of the I/O window, so Sail treats it
as ordinary memory.
For example, a halfword at 0x40000010 is outside the CLINT at 0x2000000. -/
private theorem not_mmio_io (s : SailState) (addr : BitVec 64) (n : Nat)
    (hio : 0x40000000 ≤ addr.toNat)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none) :
    within_mmio_readable (.Physaddr addr) n s = .ok false s ∧
      within_mmio_writable (.Physaddr addr) n s = .ok false s := by
  have hread := readReg_eq_of_get? Register.htif_tohost_base s _ hhtif
  have hclint : within_clint (.Physaddr addr) n s = .ok false s := by
    have hb : plat_clint_base = (0x2000000 : BitVec 64) := by rfl
    have hs : plat_clint_size = (0xc0000 : BitVec 64) := by rfl
    simp [within_clint, hb, hs, Sail.BitVec.toNatInt, pure, EStateM.pure]
    omega
  simp [within_mmio_readable, within_mmio_writable, get_config_rvfi, hclint,
    within_htif_readable, within_htif_writable, hread, orM, toBool,
    bind, EStateM.bind, pure, EStateM.pure]

/-! ### Sail's plain memory access pipeline -/

open virtaddr MemoryAccessType mem_payload in
/-- A load of `n` bytes that passes the PMP check, avoids readable MMIO and reads plain
memory returns the bytes read.
For example, a four-byte read of the I/O window returns the word `read_ram` gives. -/
private theorem mem_read_of_plain {n : Nat} (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s) (hmprv : Assumptions.MstatusMprvZero s)
    (value : BitVec (8 * n)) (hpmp : Assumptions.LoadPmpOk addr n s)
    (hmmio : within_mmio_readable (physaddr.Physaddr addr) n s = .ok false s)
    (hram : read_ram read_kind.Read_plain (physaddr.Physaddr addr) n false s =
      .ok (value, default_meta) s) :
    mem_read (Load Data) (physaddr.Physaddr addr) n false false false s =
      .ok (Ok value) s := by
  have hchecked : checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) n
      false false false false s = .ok (Ok (value, default_meta)) s := by
    unfold checked_mem_read
    simp only [bind, EStateM.bind, pure, EStateM.pure, hpmp, hmmio,
      Bool.false_eq_true, ite_false]
    unfold read_kind_of_flags
    simp only [pure, EStateM.pure]
    rw [hram]
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [hchecked]

open virtaddr MemoryAccessType mem_payload in
/-- A store of `n` bytes that passes the PMP check, avoids writable MMIO and writes plain
memory leaves the state the write gives.
For example, a one-byte write to the I/O window leaves `write_ram`'s state. -/
private theorem mem_write_value_of_plain {n : Nat} (addr : BitVec 64) (data : BitVec (8 * n))
    (s s' : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s) (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp : phys_access_check (Store Data) Privilege.Machine (physaddr.Physaddr addr) n false s =
      .ok none s)
    (hmmio : within_mmio_writable (physaddr.Physaddr addr) n s = .ok false s)
    (hram : write_ram write_kind.Write_plain (physaddr.Physaddr addr) n data default_meta s =
      .ok true s') :
    mem_write_value (physaddr.Physaddr addr) n data (Store Data) false false false s =
      .ok (Ok true) s' := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine (physaddr.Physaddr addr) n false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) n)
                (fun isMmio =>
                  if isMmio = true then mmio_write (physaddr.Physaddr addr) n data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (write_ram wk (physaddr.Physaddr addr) n data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s = .ok (Ok true) s'
  simp only [EStateM.bind, hpmp]
  simp only [hmmio]
  simp only [Bool.false_eq_true, ite_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [hram]

/-! ### Byte and doubleword arithmetic -/

/-- Cutting the byte `k` out of a doubleword with `extractLsb'` is `byte_of_dword`.
For example, byte 1 of `0xAABB` is `0xAA`. -/
private theorem byte_of_dword_eq (D : BitVec 64) (k : Nat) :
    byte_of_dword D k = D.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [byte_of_dword, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- A doubleword is its eight bytes, high byte first.
For example, `0x0102030405060708` is the append of bytes `01, 02, ..., 08`. -/
private theorem append_bytes (D : BitVec 64) :
    (D.extractLsb' 56 8 ++ D.extractLsb' 48 8 ++ D.extractLsb' 40 8 ++ D.extractLsb' 32 8 ++
      D.extractLsb' 24 8 ++ D.extractLsb' 16 8 ++ D.extractLsb' 8 8 ++ D.extractLsb' 0 8 :
        BitVec 64) = D := by
  have h1 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 48) (start₂ := 56) (len₁ := 8) (len₂ := 8) (by omega)
  have h2 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 40) (start₂ := 48) (len₁ := 8) (len₂ := 8+8) (by omega)
  have h3 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 32) (start₂ := 40) (len₁ := 8) (len₂ := 8+8+8) (by omega)
  have h4 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 24) (start₂ := 32) (len₁ := 8) (len₂ := 8+8+8+8) (by omega)
  have h5 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 16) (start₂ := 24) (len₁ := 8) (len₂ := 8+8+8+8+8) (by omega)
  have h6 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 8) (start₂ := 16) (len₁ := 8) (len₂ := 8+8+8+8+8+8) (by omega)
  have h7 := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := D) (start₁ := 0) (start₂ := 8) (len₁ := 8) (len₂ := 8+8+8+8+8+8+8) (by omega)
  rw [h1, h2, h3, h4, h5, h6, h7]
  show D.extractLsb' 0 64 = D
  simp

/-! ### Sail's load pipeline, for any width -/

open virtaddr MemoryAccessType mem_payload in
/-- The virtual-memory read of an aligned address returns what the physical read returns.
For example, a two-byte read of 0x40000002 returns the physical halfword. -/
private theorem vmem_read_addr_of_mem_read (addr offset : BitVec 64) (n : Nat) (s : SailState)
    (hn : 0 < n)
    (hpriv : Assumptions.CurPrivilegeMachine s) (hmprv : Assumptions.MstatusMprvZero s)
    (ha : AlignedAccess addr n) (value : BitVec (8 * n))
    (h_mem : mem_read (Load Data) (physaddr.Physaddr addr) n false false false s =
      .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) offset n (Load Data) false false false s =
      .ok (Ok value) s := by
  have h1 : (8 * (n : Int)).toNat = 8 * n := by omega
  have h2 : ((8 * (n : Int) - 1).toNat - (0 * (n : Int)).toNat + 1) = 8 * n := by omega
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, ite_false]
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  have htranslate :=
    translateAddr_load_data_of_machine_mprv_zero addr s hpriv hmprv
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, SailME.throw, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
        MonadExceptOf.throw,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem, h1]
  rw [h2]
  simp

open virtaddr MemoryAccessType mem_payload in
/-- A load of `rs1 + imm` that reads aligned plain memory returns the bytes read.
For example, `LHU x5, 2(x6)` reads the halfword that the physical read returns. -/
private theorem vmem_read_of_mem_read (imm : BitVec 12) (rs1 : regidx) (n : Nat)
    (s : SailState) (hn : 0 < n)
    (hpriv : Assumptions.CurPrivilegeMachine s) (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) n) (value : BitVec (8 * n))
    (h_mem : mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) n
      false false false s = .ok (Ok value) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) n (Load Data) false false false s =
      .ok (Ok value) s := by
  unfold vmem_read
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_read_addr_of_mem_read _ _ n s hn hpriv hmprv ha value h_mem]

open virtaddr MemoryAccessType mem_payload in
/-- A load instruction whose memory read succeeds writes the extended value to `rd`.
For example, `LB x5, 0(x6)` of byte `0x80` writes `0xFFFFFFFFFFFFFF80`. -/
private theorem execute_LOAD_of_mem_read (imm : BitVec 12) (rs1 rd : regidx) (u : Bool)
    (n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s) (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) n) (value : BitVec (8 * n))
    (h_mem : mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) n
      false false false s = .ok (Ok value) s) :
    (execute_LOAD imm rs1 rd u n).run s =
      .ok RETIRE_SUCCESS (stateAfterWrite s rd (extend_value u value)) := by
  have hle : (n ≤b LeanRV64D.Functions.xlen_bytes) = true := by
    apply decide_eq_true
    unfold LeanRV64D.Functions.xlen_bytes
    omega
  unfold execute_LOAD
  simp only [bind, pure]
  unfold LeanRV64D.sail_assert
  simp only [hle, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, ite_true]
  rw [vmem_read_of_mem_read imm rs1 n s hn hpriv hmprv v hrx ha value h_mem]
  simp only [EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd (extend_value u value) s
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ s s' hw

/-! ### Transport of the access premises along the prelude -/

private theorem memAccess_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s) :
    i.memAccess t = i.memAccess s := by
  cases i <;> simp only [RiscvInstruction.memAccess, h]

private theorem storeData_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s) :
    i.storeData t = i.storeData s := by
  cases i <;> simp only [RiscvInstruction.storeData, h]

/-- The access premises of a state hold in any state with the same source registers and
device.
For example, the prelude only changes the program counter, so the premises carry over. -/
private theorem access_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s)
    (hd : t.jolt_device = s.jolt_device) :
    (i.IoAccess s → i.IoAccess t) ∧ (i.NoFlagWordLoad s → i.NoFlagWordLoad t) ∧
      (i.NoLowLoad s → i.NoLowLoad t) ∧ (i.PanicStoreNonzero s → i.PanicStoreNonzero t) := by
  have hm := memAccess_congr i s t h
  have hs := storeData_congr i s t h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [RiscvInstruction.IoAccess, hm] using id
  · simpa only [RiscvInstruction.NoFlagWordLoad, hm, hd] using id
  · simpa only [RiscvInstruction.NoLowLoad, hm, hd] using id
  · simpa only [RiscvInstruction.PanicStoreNonzero, hm, hs, hd] using id

/-! ### Jolt's device reads -/

/-- Clearing the low three bits of an address rounds it down to a multiple of eight.
For example, `0x1007 &&& -8 = 0x1000`. -/
private theorem toNat_and_neg8 (ea : BitVec 64) :
    (ea &&& (-8 : BitVec 64)).toNat = ea.toNat / 8 * 8 := by
  have h : ea &&& (-8 : BitVec 64) = (ea >>> 3) <<< 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    interval_cases i <;> simp
  rw [h, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hlt : ea.toNat / 8 * 8 ≤ ea.toNat := by
    simpa [Nat.mul_comm] using Nat.mul_div_le ea.toNat 8
  exact lt_of_le_of_lt hlt ea.isLt

/-- Cutting byte `k` out of an eight-byte append gives that byte.
For example, byte 1 of `b7 ++ ... ++ b0` is `b1`. -/
private theorem extract_append8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 0 8 = b0 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 8 8 = b1 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 16 8 = b2 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 24 8 = b3 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 32 8 = b4 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 40 8 = b5 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 48 8 = b6 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 56 8 = b7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi_bool : (i <b 8) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
    simp (disch := omega) only [hi_bool, Bool.true_and, BitVec.getLsbD_extractLsb',
      Nat.reduceAdd]
    repeat rw [BitVec.getLsbD_append]
    split_ifs <;> first | (exfalso; omega) | (congr 1; omega)

/-- A successful doubleword read gives each of the eight bytes it read.
For example, byte 2 of the result is the byte read at `address + 2`. -/
private theorem read_doubleword_bytes {f : Nat → Option (BitVec 8)} {a : Nat} {D : BitVec 64}
    (h : JoltISA.read_doubleword? f a = some D) :
    ∀ k < 8, f (a + k) = some (D.extractLsb' (8 * k) 8) := by
  unfold JoltISA.read_doubleword? at h
  split at h
  · rename_i b0 b1 b2 b3 b4 b5 b6 b7 e0 e1 e2 e3 e4 e5 e6 e7
    cases h
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := extract_append8 b0 b1 b2 b3 b4 b5 b6 b7
    intro k hk
    interval_cases k
    · simpa [x0] using e0
    · simpa [x1] using e1
    · simpa [x2] using e2
    · simpa [x3] using e3
    · simpa [x4] using e4
    · simpa [x5] using e5
    · simpa [x6] using e6
    · simpa [x7] using e7
  · simp at h

/-- A byte that Jolt's checked read returns below RAM is the device's byte there.
For example, if `load_raw?` gives `0x07` at an output address, so does `JoltDevice.load?`. -/
private theorem load_raw_load (js : SailJoltState) (a : Nat) (x : BitVec 8)
    (hlt : a < JoltISA.RAM_START_ADDRESS) (h : JoltISA.Mmu.load_raw? js a = some x) :
    js.jolt_device.load? a = some x := by
  unfold JoltISA.Mmu.load_raw? at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ a := by omega
  simp only [hnle, ite_false, Bool.not_eq_true'] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · exact h
      · simp at h

/-- A retiring `load_doubleword` below RAM is aligned and reads eight device bytes.
For example, a successful load at the aligned address `0x40000008` has read `0x40000008` to
`0x4000000f` through `load_raw?`, and leaves the state unchanged. -/
private theorem load_doubleword_inv (A : BitVec 64) (js js' : SailJoltState)
    (r : Result (BitVec 64) ExecutionResult) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.load_doubleword A js = .ok r js') :
    A.toNat % 8 = 0 ∧ ∃ D, r = .Ok D ∧ js' = js ∧
      JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D := by
  unfold JoltISA.Mmu.load_doubleword at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ A.toNat := by omega
  by_cases hal : A.toNat % 8 = 0
  · simp only [hal, ne_eq, not_true_eq_false, ite_false, hnle] at h
    split at h
    · rename_i D hD
      cases h
      exact ⟨hal, D, rfl, rfl, hD⟩
    · simp at h
  · simp [hal] at h

/-- A doubleword whose eight bytes are in Sail's memory is `loaded_dword_at`.
For example, memory holding `0x08 0x07 ... 0x01` at `a, a + 1, ..., a + 7` loads
`0x0102030405060708`. -/
private theorem loaded_dword_eq_of_bytes (s : SailState) (A : BitVec 64)
    (hb : MemBytesPresentAt s A 8) (no : A.toNat + 7 < 2 ^ 64) (D : BitVec 64)
    (h : ∀ k < 8, s.mem.get? (A.toNat + k) = some (D.extractLsb' (8 * k) 8)) :
    loaded_dword_at s A hb no = D := by
  have hbyte : ∀ (a : BitVec 64) (p : MemBytePresentAt s a.toNat) (b : BitVec 8),
      s.mem.get? a.toNat = some b → loaded_byte_at s a p = b := by
    intro a p b hab
    unfold loaded_byte_at loaded_byte_at_nat
    simp only [hab, Option.get_some]
  have hn : ∀ c : Nat, c < 8 → (A + BitVec.ofNat 64 c).toNat = A.toNat + c := by
    intro c hc
    rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  unfold loaded_dword_at
  rw [hbyte (A + 7) _ (D.extractLsb' 56 8) (by simpa [hn 7 (by omega)] using h 7 (by omega)),
    hbyte (A + 6) _ (D.extractLsb' 48 8) (by simpa [hn 6 (by omega)] using h 6 (by omega)),
    hbyte (A + 5) _ (D.extractLsb' 40 8) (by simpa [hn 5 (by omega)] using h 5 (by omega)),
    hbyte (A + 4) _ (D.extractLsb' 32 8) (by simpa [hn 4 (by omega)] using h 4 (by omega)),
    hbyte (A + 3) _ (D.extractLsb' 24 8) (by simpa [hn 3 (by omega)] using h 3 (by omega)),
    hbyte (A + 2) _ (D.extractLsb' 16 8) (by simpa [hn 2 (by omega)] using h 2 (by omega)),
    hbyte (A + 1) _ (D.extractLsb' 8 8) (by simpa [hn 1 (by omega)] using h 1 (by omega)),
    hbyte A _ (D.extractLsb' 0 8) (by simpa using h 0 (by omega))]
  exact append_bytes D

/-- A doubleword that Jolt's device read gives at an aligned I/O address is the one Sail's
memory holds there, when none of its bytes is a flag byte.
For example, if `load_raw?` reads `D` at `0x40000008`, then `loaded_dword_at` of Sail's
memory at `0x40000008` is `D`. -/
private theorem io_dword_eq (js : SailJoltState) (A D : BitVec 64)
    (hmem : MemRel js.jolt_device js.sail)
    (hal : A.toNat % 8 = 0) (hlow : memLow js.jolt_device ≤ A.toNat)
    (hlt : A.toNat < RAM_START_ADDRESS)
    (hflag : ∀ k < 8, IsFlagWord js.jolt_device (A.toNat + k) = false)
    (hread : JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D) :
    ∃ (hb : MemBytesPresentAt js.sail A 8) (no : A.toNat + 7 < 2 ^ 64),
      loaded_dword_at js.sail A hb no = D := by
  have hbytes := read_doubleword_bytes hread
  have hget : ∀ k < 8, js.sail.mem.get? (A.toNat + k) = some (D.extractLsb' (8 * k) 8) := by
    intro k hk
    have hr := load_raw_load js _ _ (by simp only [JoltISA.RAM_START_ADDRESS] at hlt ⊢; omega)
      (hbytes k hk)
    rw [hmem.io (A.toNat + k) (by omega) (by simp only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] at hlt ⊢; omega)
      (hflag k hk), hr]
    rfl
  have no : A.toNat + 7 < 2 ^ 64 := by simp only [JoltISA.RAM_START_ADDRESS] at hlt; omega
  have hb : MemBytesPresentAt js.sail A 8 := fun k hk => ⟨_, hget k hk⟩
  exact ⟨hb, no, loaded_dword_eq_of_bytes js.sail A hb no D hget⟩

/-! ### Jolt's load rows -/

/-- A retiring first load row is aligned and read a doubleword.
For example, if `VirtualLoadW` retires, the effective address is 4-aligned and
`load_doubleword` of its containing doubleword succeeded. -/
private theorem floorLoad_inv (w : JoltISA.AccessWidth) (vd : JoltISA.VReg) (rs1 : regidx)
    (imm base : BitVec 64) (fc : JoltISA.LoadFaultClass) (f : ExceptionType)
    (js js1 : SailJoltState) (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + imm) &&& ~~~(7 : BitVec 64)).toNat < JoltISA.RAM_START_ADDRESS)
    (h : (JoltISA.execInstr (LoadFamily.floorLoadRow w (.vreg vd) (.xreg rs1) imm fc f)).run js =
      .ok RETIRE_SUCCESS js1) :
    (base + imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) js =
        .ok (.Ok D) js := by
  by_cases halign : (base + imm) &&& LoadFamily.alignmentMask w = 0
  · refine ⟨halign, ?_⟩
    cases hl : JoltISA.Mmu.load_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) js with
    | ok r s' =>
      obtain ⟨_, D, hr, hs, _⟩ := load_doubleword_inv _ js s' r hlt hl
      subst hr
      subst hs
      exact ⟨D, rfl⟩
    | error e s' =>
      exfalso
      cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
        simp only [LoadFamily.floorLoadRow, JoltISA.laneWindowOpen, JoltISA.execInstr,
          JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hread, halign,
          ↓reduceIte, hl] at h <;>
        simp at h
  · exfalso
    have := LoadFamily.floorLoad_misaligned w (.vreg vd) rs1 imm base fc f js hread halign
    rw [this] at h
    simp [RETIRE_SUCCESS] at h

/-- The second row of a narrow load, the window mask for the access width.
For example, word width is `VirtualWindowMaskW`. -/
private def maskRow : JoltISA.AccessWidth → JoltISA.Dst → JoltISA.Src → BitVec 64 →
    JoltISA.Instr
  | .byte, lane, base, offset => .VirtualWindowMaskB lane base offset
  | .halfword, lane, base, offset => .VirtualWindowMaskH lane base offset
  | .word, lane, base, offset => .VirtualWindowMaskW lane base offset

/-- The mask value the window-mask row of the given width computes.
For example, for a halfword at offset 2 it selects bits 16 to 31 of the doubleword. -/
private def maskValue : JoltISA.AccessWidth → BitVec 64 → BitVec 12 → BitVec 64
  | .byte, base, imm => jolt_virtual_window_mask_b_value base imm
  | .halfword, base, imm => jolt_virtual_window_mask_h_value base imm
  | .word, base, imm => jolt_virtual_window_mask_w_value base imm

/-- The value the extraction row computes, signed or unsigned.
For example, extracting the byte `0x80` with `signed` gives `0xFFFFFFFFFFFFFF80`. -/
private def extractValue (signed : Bool) (D M : BitVec 64) : BitVec 64 :=
  if signed then jolt_virtual_pext_signed_value D M else jolt_virtual_pext_value D M

/-- The value a narrow load leaves: the lane of the doubleword, extended.
For example, `LB` of `0x80` leaves `0xFFFFFFFFFFFFFF80`. -/
private def loadValue (w : JoltISA.AccessWidth) (signed : Bool) (D base : BitVec 64)
    (imm : BitVec 12) : BitVec 64 :=
  extractValue signed D (maskValue w base imm)

private theorem laneWindowOpen_eq (w : JoltISA.AccessWidth) (d l : JoltISA.Dst)
    (b : JoltISA.Src) (o : BitVec 64) (fc : JoltISA.LoadFaultClass) (f : ExceptionType)
    (tail : JoltISA.Program) :
    JoltISA.laneWindowOpen w d l b o fc f tail =
      .instr (LoadFamily.floorLoadRow w d b o fc f) (.instr (maskRow w l b o) tail) := by
  cases w <;> rfl

/-- The window-mask row retires and writes the mask to its scratch register.
For example, the byte mask of address 0x40000003 is written to the lane register. -/
private theorem maskRow_run (w : JoltISA.AccessWidth) (lane : JoltISA.VReg) (rs1 : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok x js.sail) (hlane : WritableVReg lane) :
    (JoltISA.execInstr (maskRow w (.vreg lane) (.xreg rs1) (sign_extend (m := 64) imm))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js lane (maskValue w x imm)) := by
  cases w
  · exact JoltISA.virtual_window_mask_b_run_vreg_xreg lane rs1 imm js x hread hlane
  · exact JoltISA.virtual_window_mask_h_run_vreg_xreg lane rs1 imm js x hread hlane
  · exact JoltISA.virtual_window_mask_w_run_vreg_xreg lane rs1 imm js x hread hlane

/-- The extraction row of a narrow load retires and writes the extended lane to a register.
For example, with `signed` it writes the sign-extended lane to `rd`. -/
private theorem pextRow_xreg_run (signed : Bool) (rd : regidx) (dw lane : JoltISA.VReg)
    (js : SailJoltState) :
    (JoltISA.execInstr (if signed then
        JoltISA.Instr.VirtualPextSigned (.xreg rd) (.vreg dw) (.vreg lane)
      else JoltISA.Instr.VirtualPext (.xreg rd) (.vreg dw) (.vreg lane))).run js =
      .ok RETIRE_SUCCESS { js with
        sail := stateAfterWrite js.sail rd (extractValue signed (js.vregs dw) (js.vregs lane)) } := by
  cases signed
  · simp only [Bool.false_eq_true, ↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_run_xreg_vreg_vreg rd dw lane js _
      (wX_bits_stateAfterWrite rd _ js.sail)
  · simp only [↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_signed_run_xreg_vreg_vreg rd dw lane js _
      (wX_bits_stateAfterWrite rd _ js.sail)

/-- The extraction row of a narrow load retires and writes the extended lane to a scratch
register. -/
private theorem pextRow_vreg_run (signed : Bool) (v dw lane : JoltISA.VReg)
    (js : SailJoltState) (hv : WritableVReg v) :
    (JoltISA.execInstr (if signed then
        JoltISA.Instr.VirtualPextSigned (.vreg v) (.vreg dw) (.vreg lane)
      else JoltISA.Instr.VirtualPext (.vreg v) (.vreg dw) (.vreg lane))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js v
        (extractValue signed (js.vregs dw) (js.vregs lane))) := by
  cases signed
  · simp only [Bool.false_eq_true, ↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_run_vreg_vreg_vreg v dw lane js hv
  · simp only [↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_signed_run_vreg_vreg_vreg v dw lane js hv

/-- A retiring narrow load program reads an aligned doubleword and leaves the extended lane.
From a retiring run of the three rows, the effective address is aligned for the width, the
containing doubleword was read, the device is unchanged, and the destination holds the lane. -/
private theorem loadRows_inv (w : JoltISA.AccessWidth) (signed : Bool)
    (dw lane : JoltISA.VReg) (dst : JoltISA.Dst) (hdw : WritableVReg dw)
    (hlane : WritableVReg lane) (hne : dw ≠ lane) (hdst : ∀ v, dst = .vreg v → WritableVReg v)
    (rs1 : regidx) (imm : BitVec 12) (base : BitVec 64) (js gp : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execProgram (JoltISA.laneWindowOpen w (.vreg dw) (.vreg lane) (.xreg rs1)
        (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg dw) (.vreg lane) dst signed
          (.done RETIRE_SUCCESS)))).run js = .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)) js = .ok (.Ok D) js ∧
        gp.jolt_device = js.jolt_device ∧
        (∀ rd, dst = .xreg rd →
          gp.sail = stateAfterWrite js.sail rd (loadValue w signed D base imm)) ∧
        (∀ v, dst = .vreg v → gp.sail = js.sail) := by
  have hrun' := hrun
  rw [laneWindowOpen_eq] at hrun'
  obtain ⟨js1, h1, -⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ js gp hrun'
  obtain ⟨hal, D, hD⟩ := floorLoad_inv w dw rs1 (sign_extend (m := 64) imm) base .normal
    (ExceptionType.E_Load_Addr_Align ()) js js1 hread hlt h1
  refine ⟨hal, D, hD, ?_⟩
  have e1 := LoadFamily.floorLoad_run w dw rs1 (sign_extend (m := 64) imm) base D .normal
    (ExceptionType.E_Load_Addr_Align ()) js hread hal hD hdw
  have hread1 : rX_bits rs1 (stateAfterVRegWrite js dw D).sail =
      .ok base (stateAfterVRegWrite js dw D).sail := hread
  have e2 := maskRow_run w lane rs1 imm _ base hread1 hlane
  have hv1 : (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane
      (maskValue w base imm)).vregs dw = D := by simp [stateAfterVRegWrite, hne]
  have hv2 : (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane
      (maskValue w base imm)).vregs lane = maskValue w base imm := by simp [stateAfterVRegWrite]
  cases dst with
  | xreg rd =>
    have e3 := pextRow_xreg_run signed rd dw lane
      (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane (maskValue w base imm))
    rw [hv1, hv2] at e3
    have hprog := LoadFamily.threeRows_run e1 e2 e3
    unfold JoltISA.Program.Run at hprog
    rw [laneWindowOpen_eq] at hrun
    have hg := hrun.symm.trans hprog
    simp only [EStateM.Result.ok.injEq, true_and] at hg
    subst hg
    refine ⟨rfl, ?_, nofun⟩
    intro rd' h
    cases h
    rfl
  | vreg v =>
    have e3 := pextRow_vreg_run signed v dw lane
      (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane (maskValue w base imm))
      (hdst v rfl)
    rw [hv1, hv2] at e3
    have hprog := LoadFamily.threeRows_run e1 e2 e3
    unfold JoltISA.Program.Run at hprog
    rw [laneWindowOpen_eq] at hrun
    have hg := hrun.symm.trans hprog
    simp only [EStateM.Result.ok.injEq, true_and] at hg
    subst hg
    refine ⟨rfl, nofun, ?_⟩
    intro v' h
    rfl

/-! ### Sail's load rows -/

/-- The bytes of an access inside an aligned doubleword are present when the doubleword is.
For example, a halfword at `0x40000006` lies in the doubleword at `0x40000000`. -/
private theorem present_in_dword (s : SailState) (ea : BitVec 64)
    (hb : MemBytesPresentAt s (ea &&& (-8 : BitVec 64)) 8) (width : Nat)
    (hw : ea.toNat % 8 + width ≤ 8) : MemBytesPresentAt s ea width := by
  intro k hk
  have h := hb (ea.toNat % 8 + k) (by omega)
  have hA := toNat_and_neg8 ea
  have : (ea &&& (-8 : BitVec 64)).toNat + (ea.toNat % 8 + k) = ea.toNat + k := by omega
  rw [this] at h
  exact h

private theorem neg8_eq : ~~~(7 : BitVec 64) = (-8 : BitVec 64) := by decide

open virtaddr MemoryAccessType mem_payload in
/-- A byte load from the I/O window whose doubleword Sail holds retires with that byte.
For example, `LB x5, 3(x6)` at `0x40000010` writes the sign-extended byte `0x40000013`. -/
private theorem sail_load_b (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 1).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .byte (!u) D base imm)) := by
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 1 :=
    present_in_dword js.sail _ hb 1 (by omega)
  have hp : MemBytePresentAt js.sail (load_effective_address base imm).toNat :=
    hbytes.single_byte
  obtain ⟨hl, -⟩ := io_checks js.sail _ 1 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) (Nat.mod_one _)
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 1 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_1_eq_loaded_byte _ js.sail hbytes)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 1 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread (aligned_access_1 _) _ hmem]
  congr 2
  rw [loaded_byte_in_dword js.sail _ hb no hp, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_b_pext_signed]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_b_pext]

open virtaddr MemoryAccessType mem_payload in
/-- A halfword load from the I/O window whose doubleword Sail holds retires with that halfword.
For example, `LHU x5, 2(x6)` at `0x40000010` writes the zero-extended halfword at
`0x40000012`. -/
private theorem sail_load_h (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (1 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 2).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .halfword (!u) D base imm)) := by
  have hmod := mod_of_and1 _ hal
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 2 :=
    present_in_dword js.sail _ hb 2 (by omega)
  have hno : (load_effective_address base imm).toNat + 1 < 2 ^ 64 := by
    simp only [JoltISA.RAM_START_ADDRESS] at hhi; omega
  obtain ⟨hl, -⟩ := io_checks js.sail _ 2 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 2 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_2_eq_loaded_halfword _ js.sail hbytes hno)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 2 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread ⟨access_misaligned_2_aligned_false _ hal, split_misaligned_aligned_2 _ hal⟩ _ hmem]
  congr 2
  rw [loaded_halfword_in_dword js.sail _ hal hb no hbytes hno, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_h_pext_signed _ _ _ hal]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_h_pext _ _ _ hal]

open virtaddr MemoryAccessType mem_payload in
/-- A word load from the I/O window whose doubleword Sail holds retires with that word.
For example, `LW x5, 4(x6)` at `0x40000010` writes the sign-extended word at `0x40000014`. -/
private theorem sail_load_w (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (3 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 4).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .word (!u) D base imm)) := by
  have hmod := mod_of_and3 _ hal
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 4 :=
    present_in_dword js.sail _ hb 4 (by omega)
  have hno : (load_effective_address base imm).toNat + 3 < 2 ^ 64 := by
    simp only [JoltISA.RAM_START_ADDRESS] at hhi; omega
  obtain ⟨hl, -⟩ := io_checks js.sail _ 4 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 4 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_4_eq_loaded_word _ js.sail hbytes hno)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 4 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread ⟨access_misaligned_4_aligned_false _ hal, split_misaligned_aligned_4 _ hal⟩ _ hmem]
  congr 2
  rw [loaded_word_in_dword js.sail _ hal hb no hbytes hno, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_w_pext_signed _ _ _ hal]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_w_pext _ _ _ hal]

/-- Sign-extending a 64-bit value to 64 bits changes nothing.
For example, `sign_extend 0x8000000000000000` is `0x8000000000000000`. -/
private theorem sign_extend_64_eq_self' (v : BitVec 64) : sign_extend (m := 64) v = v := by
  simp [sign_extend, Sail.BitVec.signExtend]

open virtaddr MemoryAccessType mem_payload in
/-- A doubleword load from the I/O window whose bytes Sail holds retires with that doubleword.
For example, `LD x5, 8(x6)` at `0x40000010` writes the doubleword at `0x40000018`. -/
private theorem sail_load_d (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (7 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm) 8)
    (no : (load_effective_address base imm).toNat + 7 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 8).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loaded_dword_at js.sail (load_effective_address base imm) hb no)) := by
  have hmod := mod_of_and7 _ hal
  obtain ⟨hl, -⟩ := io_checks js.sail _ 8 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 8 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_eq_loaded_dword _ js.sail hb no)
  rw [execute_LOAD_of_mem_read imm rs1 rd false 8 (by norm_num) (by norm_num) js.sail hpriv
    hmprv base hread (aligned_dword_access_of_align _ hal).toAlignedAccess _ hmem]
  simp only [extend_value, Bool.false_eq_true, ite_false]
  rw [sign_extend_64_eq_self']

/-! ### The effect of a narrow load -/

/-- The aligned doubleword around a non-flag, non-low address is a non-flag doubleword.
For example, the doubleword at `0x40000010` is a non-flag word when the panic word is at
`0x40000100`. -/
private theorem dword_geometry (d : JoltDevice) (hgeo : IoGeo d) (ea : Nat)
    (h0 : IsFlagWord d ea = false) (hlow : memLow d ≤ ea) :
    memLow d ≤ ea / 8 * 8 ∧ ∀ k < 8, IsFlagWord d (ea / 8 * 8 + k) = false := by
  have h := hgeo
  obtain ⟨-, hla, -, hoa, hp, hma, ht, he, -⟩ := h
  simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt] at h0
  refine ⟨by omega, fun k hk => ?_⟩
  simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt]
  omega

/-- A narrow load that retires in the I/O window leaves what Sail's load leaves.
From a retiring run of the three rows, Sail's `LOAD` retires to the same register write, and
the device is unchanged. -/
private theorem narrow_load_outcome (w : JoltISA.AccessWidth) (signed : Bool) (n : Nat)
    (dw lane : JoltISA.VReg) (dst : JoltISA.Dst) (hdw : WritableVReg dw)
    (hlane : WritableVReg lane) (hne : dw ≠ lane) (hdst : ∀ v, dst = .vreg v → WritableVReg v)
    (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hx0 : ∀ v, dst = .vreg v → JoltISA.isX0 rd = true) (hxr : ∀ r, dst = .xreg r → r = rd)
    (hinv : Step.StepInvariant js.sail) (hmem : MemRel js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (h0 : IsFlagWord js.jolt_device
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat = false)
    (hlow : memLow js.jolt_device ≤
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat)
    (hsail : ∀ (base : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < RAM_START_ADDRESS →
      ∀ (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
        (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
        (D : BitVec 64),
        loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D →
        (execute_LOAD imm rs1 rd (!signed) n).run js.sail = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd (loadValue w signed D base imm)))
    (hrun : (JoltISA.execProgram (JoltISA.laneWindowOpen w (.vreg dw) (.vreg lane) (.xreg rs1)
        (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg dw) (.vreg lane) dst signed
          (.done RETIRE_SUCCESS)))).run js = .ok RETIRE_SUCCESS gp) :
    ∃ V, (execute_LOAD imm rs1 rd (!signed) n).run js.sail =
        .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  have hread : rX_bits rs1 js.sail = .ok (sourceValue (.xreg rs1) js) js.sail :=
    (bundleHelper% source_read) js hinv rs1
  generalize hbase : sourceValue (.xreg rs1) js = base at hread hhi h0 hlow
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat =
      (load_effective_address base imm).toNat / 8 * 8 := by
    rw [← hea, neg8_eq, toNat_and_neg8]
  have hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    simp only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] at hhi ⊢
    omega
  obtain ⟨hal, D, hD, hdev, hxreg, hvreg⟩ :=
    loadRows_inv w signed dw lane dst hdw hlane hne hdst rs1 imm base js gp hread hlt hrun
  have hD' : JoltISA.Mmu.load_doubleword (load_effective_address base imm &&& (-8 : BitVec 64))
      js = .ok (.Ok D) js := by
    rw [hea, ← neg8_eq]
    exact hD
  have hA' := toNat_and_neg8 (load_effective_address base imm)
  have hlt' : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    simp only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] at hhi ⊢
    omega
  obtain ⟨hmod, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hlt' hD'
  cases hr
  obtain ⟨hlowA, hflagA⟩ := dword_geometry _ hgeo _ h0 hlow
  have hlo40 : 0x40000000 ≤ (load_effective_address base imm).toNat := by
    have := hgeo.low
    omega
  obtain ⟨hb, no, hDeq⟩ := io_dword_eq js _ D hmem hmod (by rw [hA']; exact hlowA)
    hlt' (by rw [hA']; exact hflagA) hrd
  have hsl := hsail base hread hal hlo40 hhi hb no D hDeq
  refine ⟨_, hsl, ?_, hdev⟩
  cases dst with
  | xreg r =>
    obtain rfl := hxr r rfl
    exact hxreg r rfl
  | vreg v =>
    have hx := hx0 v rfl
    rw [hvreg v rfl, stateAfterWrite_of_isX0_eq_true hx]

/-! ### The effect of a doubleword load -/

private theorem ld_inv (rd rs1 : regidx) (imm : BitVec 12) (base : BitVec 64)
    (js gp : SailJoltState) (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword (base + sign_extend (m := 64) imm) js = .ok (.Ok D) js ∧
        gp.jolt_device = js.jolt_device ∧ gp.sail = stateAfterWrite js.sail rd D ∧
        Projection.ProjectedVRegsPreserved js gp := by
  unfold JoltISA.ldNativeInstr at hrun
  simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind,
    EStateM.bind, EStateM.run, hread] at hrun
  by_cases halign : (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0
  · simp only [halign, ↓reduceIte] at hrun
    refine ⟨halign, ?_⟩
    cases hl : JoltISA.Mmu.load_doubleword (base + sign_extend (m := 64) imm) js with
    | ok r s' =>
      obtain ⟨-, D, hr, hs, -⟩ := load_doubleword_inv _ js s' r hlt hl
      subst hr
      subst hs
      refine ⟨D, rfl, ?_⟩
      simp only [EStateM.bind, hl] at hrun
      by_cases hx0 : JoltISA.isX0 rd = true
      · have hdst : JoltISA.sideEffectingRdZeroDst rd =
            JoltISA.Dst.vreg JoltISA.rdZeroRewriteVReg := by
          simp [JoltISA.sideEffectingRdZeroDst, hx0]
        have hnl : ¬ JoltISA.rdZeroRewriteVReg.toNat < 32 := by
          simp [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
            JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
            JoltISA.numReservedVirtualRegisters]
        rw [hdst] at hrun
        simp only [JoltISA.writeDst, writeVReg, hnl, ite_false, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure] at hrun
        simp only [EStateM.Result.ok.injEq, true_and] at hrun
        subst hrun
        refine ⟨rfl, (stateAfterWrite_of_isX0_eq_true hx0 _ _).symm, ?_⟩
        unfold Projection.ProjectedVRegsPreserved
        simp [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
          JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
          JoltISA.numReservedVirtualRegisters, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
          JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg,
          JoltISA.reservationWReg, JoltISA.reservationDReg]
      · have hdst : JoltISA.sideEffectingRdZeroDst rd = JoltISA.Dst.xreg rd := by
          simp [JoltISA.sideEffectingRdZeroDst, hx0]
        rw [hdst] at hrun
        simp only [JoltISA.writeDst, liftSail, wX_bits_stateAfterWrite, pure,
          EStateM.pure] at hrun
        simp only [EStateM.Result.ok.injEq, true_and] at hrun
        subst hrun
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | error e s' =>
      exfalso
      simp [EStateM.bind, hl] at hrun
  · exfalso
    simp only [halign, ↓reduceIte] at hrun
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this

/-- A doubleword load that retires in the I/O window leaves what Sail's load leaves.
From a retiring run of `LD`, Sail's `LOAD` retires to the same register write, and the
device is unchanged. -/
private theorem ld_outcome (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (h0 : IsFlagWord js.jolt_device
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat = false)
    (hlow : memLow js.jolt_device ≤
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ V, (execute_LOAD imm rs1 rd false 8).run js.sail =
        .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device ∧
      Projection.ProjectedVRegsPreserved js gp := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  have hread : rX_bits rs1 js.sail = .ok (sourceValue (.xreg rs1) js) js.sail :=
    (bundleHelper% source_read) js hinv rs1
  generalize hbase : sourceValue (.xreg rs1) js = base at hread hhi h0 hlow
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]
    simpa only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] using hhi
  obtain ⟨hal, D, hD, hdev, hsail, hproj⟩ := ld_inv rd rs1 imm base js gp hread hlt hrun
  obtain ⟨hmod, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hlt hD
  cases hr
  have hmod' : (load_effective_address base imm).toNat % 8 = 0 := mod_of_and7 _ hal
  obtain ⟨hlowA, hflagA⟩ := dword_geometry _ hgeo _ h0 hlow
  have hdiv : (load_effective_address base imm).toNat / 8 * 8 =
      (load_effective_address base imm).toNat := by omega
  rw [hdiv] at hlowA hflagA
  have hlo40 : 0x40000000 ≤ (load_effective_address base imm).toNat := by
    have := hgeo.low
    omega
  obtain ⟨hb, no, hDeq⟩ := io_dword_eq js _ D hmem hmod hlowA hlt hflagA hrd
  have hDeq' : loaded_dword_at js.sail (load_effective_address base imm) hb no = D := hDeq
  have hsl := sail_load_d js imm rs1 rd base hpriv hmprv hpma hhtif hread hal hlo40 hhi hb no
  rw [hDeq'] at hsl
  exact ⟨D, hsl, hsail, hdev, hproj⟩

/-! ### Loads, assembled -/

/-- A load whose Sail register write matches Jolt's is a faithful step.
From Sail's retiring `LOAD` and Jolt's final state, which differ only by the write of `V`
to `rd` and by scratch registers, the conclusion of `io_core` follows. -/
private theorem load_finish (ast : instruction) (rd : regidx) (js gp : SailJoltState)
    (V : BitVec 64) (hlink : System.systemProject js = js.sail)
    (hmem : MemRel js.jolt_device js.sail)
    (hexec : execute ast js.sail = .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V))
    (hgp : gp.sail = stateAfterWrite js.sail rd V) (hdev : gp.jolt_device = js.jolt_device)
    (hproj : Projection.ProjectedVRegsPreserved js gp) :
    ∃ t : SailState, execute ast js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  refine ⟨stateAfterWrite js.sail rd V, hexec, ?_, fun a _ => by rw [hgp], ?_⟩
  · rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved js gp rd V hgp hproj,
      hlink]
  · rw [hdev]
    exact hmem.of_mem_eq rfl

/-- A narrow load in the I/O window, from the rows of its expansion to Sail's `execute`.
The expansion has two shapes, one for `rd = x0`, which only writes scratch registers. -/
private theorem narrow_load_core (w : JoltISA.AccessWidth) (signed : Bool) (n : Nat)
    (rd rs1 : regidx) (imm : BitVec 12) (prog : JoltISA.Program) (js gp : SailJoltState)
    (hprog0 : JoltISA.isX0 rd = true → prog =
      JoltISA.laneWindowOpen w (.vreg (BitVec.ofNat 7 41)) (.vreg (BitVec.ofNat 7 42))
        (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg (BitVec.ofNat 7 41)) (.vreg (BitVec.ofNat 7 42))
          (.vreg (BitVec.ofNat 7 40)) signed (.done RETIRE_SUCCESS)))
    (hprog1 : ¬ JoltISA.isX0 rd = true → prog =
      JoltISA.laneWindowOpen w (.vreg (BitVec.ofNat 7 40)) (.vreg (BitVec.ofNat 7 41))
        (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg (BitVec.ofNat 7 40)) (.vreg (BitVec.ofNat 7 41))
          (.xreg rd) signed (.done RETIRE_SUCCESS)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemRel js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (h0 : IsFlagWord js.jolt_device
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat = false)
    (hlow : memLow js.jolt_device ≤
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat)
    (hsail : ∀ (base : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < RAM_START_ADDRESS →
      ∀ (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
        (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
        (D : BitVec 64),
        loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D →
        (execute_LOAD imm rs1 rd (!signed) n).run js.sail = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd (loadValue w signed D base imm)))
    (hrun : (JoltISA.execProgram prog).run js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.LOAD (imm, rs1, rd, !signed, n)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hw : ∀ k, WritableVReg (BitVec.ofNat 7 k) ↔ 32 ≤ k % 128 := fun k => by
    simp [WritableVReg, BitVec.toNat_ofNat]
  obtain ⟨V, hexec, hgp, hdev⟩ : ∃ V, (execute_LOAD imm rs1 rd (!signed) n).run js.sail =
      .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device := by
    by_cases hx : JoltISA.isX0 rd = true
    · rw [hprog0 hx] at hrun
      exact narrow_load_outcome w signed n _ _ _ (by rw [hw]; decide) (by rw [hw]; decide)
        (by decide) (by intro v h; cases h; rw [hw]; decide) rd rs1 imm js gp
        (by intro v _; exact hx) (by intro r h; cases h) hinv hmem hhi h0 hlow hsail hrun
    · rw [hprog1 hx] at hrun
      exact narrow_load_outcome w signed n _ _ _ (by rw [hw]; decide) (by rw [hw]; decide)
        (by decide) (by intro v h; cases h) rd rs1 imm js gp
        (by intro v h; cases h) (by intro r h; cases h; rfl) hinv hmem hhi h0 hlow hsail hrun
  exact load_finish _ rd js gp V hlink hmem hexec hgp hdev hproj

/-- A doubleword load in the I/O window, from the native `LD` row to Sail's `execute`. -/
private theorem ld_core (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (h0 : IsFlagWord js.jolt_device
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat = false)
    (hlow : memLow js.jolt_device ≤
      (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.LOAD (imm, rs1, rd, false, 8)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  obtain ⟨V, hexec, hgp, hdev, hproj⟩ := ld_outcome rd rs1 imm js gp hinv hlink hmstatus hmem hpma hhtif
    hhi h0 hlow hrun
  exact load_finish _ rd js gp V hlink hmem hexec hgp hdev hproj

/-- The access premises of a load, at its own effective address.
For example, for `LB` they give that the address is below RAM, not a flag byte and not
below `memLow`. -/
private theorem load_access (i : RiscvInstruction) (js : SailJoltState) (rs1 : regidx)
    (imm : BitVec 12) (n : Nat) (hn : 0 < n)
    (hacc : i.memAccess js = some (false, n, load_effective_address (sourceValue (.xreg rs1) js) imm))
    (hio : i.IoAccess js) (hflag : i.NoFlagWordLoad js) (hlow : i.NoLowLoad js) :
    (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS ∧
      IsFlagWord js.jolt_device
        (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat = false ∧
      memLow js.jolt_device ≤ (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat := by
  obtain ⟨store, width, ea, hacc', hlt⟩ := hio
  rw [hacc] at hacc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
  obtain ⟨-, -, rfl⟩ := hacc'
  exact ⟨hlt, by simpa using hflag n _ hacc 0 hn, hlow n _ hacc⟩

/-! ### Sail's store rows -/

open virtaddr MemoryAccessType mem_payload in
/-- A virtual-memory write of `rs1 + imm` that succeeds at the checked address is the write
`vmem_write` performs.
For example, `SB x5, 3(x6)` writes where `vmem_write_addr` writes at `x6 + 3`. -/
private theorem vmem_write_of_addr {n : Nat} (imm : BitVec 12) (rs1 : regidx)
    (s s' : SailState) (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec (8 * n))
    (h : vmem_write_addr (Virtaddr (v + sign_extend (m := 64) imm)) n data (Store Data)
      false false false s = .ok (Ok true) s') :
    vmem_write rs1 (sign_extend (m := 64) imm) n data (Store Data) false false false s =
      .ok (Ok true) s' := by
  unfold vmem_write
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx, h]

open virtaddr MemoryAccessType mem_payload in
/-- A doubleword store whose virtual-memory write succeeds retires with that write's state.
For example, `SD x5, 8(x6)` retires in the state the write leaves. -/
private theorem execute_STORE_dword_of_write (imm : BitVec 12) (rs2 rs1 : regidx)
    (s s' : SailState) (v val : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (hry : rX_bits rs2 s = .ok val s)
    (h : vmem_write_addr (Virtaddr (v + sign_extend (m := 64) imm)) 8 val (Store Data)
      false false false s = .ok (Ok true) s') :
    (execute_STORE imm rs2 rs1 8).run s = .ok RETIRE_SUCCESS s' := by
  unfold execute_STORE
  simp only [bind, pure]
  unfold LeanRV64D.sail_assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    EStateM.bind, pure, EStateM.pure, EStateM.run, ite_true]
  rw [hry]
  simp only
  set data : BitVec (8 * 8) :=
    BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb val
        ((((8 : Nat) : Int) * (8 : Int) - (1 : Int)).toNat) 0)
  have hdata : data = val := by
    subst data
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  rw [hdata, vmem_write_of_addr (n := 8) imm rs1 s s' v hrx val h]
  rfl

/-- The write checks of an aligned store of `n` bytes inside Sail's I/O window.
For example, a word store at `0x40000010` passes the PMP check and avoids MMIO. -/
private theorem io_write_checks (s : SailState) (addr : BitVec 64) (n : Nat)
    (hpma : s.regs.get? Register.pma_regions = some platformPma)
    (hhtif : s.regs.get? Register.htif_tohost_base = some none)
    (hlo : 0x40000000 ≤ addr.toNat) (hn : 0 < n) (hwidth : n ≤ 8)
    (hhi : addr.toNat + n ≤ JoltISA.RAM_START_ADDRESS) (halign : addr.toNat % n = 0) :
    Assumptions.StorePmpOk addr n s ∧
      within_mmio_writable (physaddr.Physaddr addr) n s = .ok false s :=
  ⟨(io_checks s addr n hpma hlo hn hwidth hhi halign).2, (not_mmio_io s addr n hlo hhtif).2⟩

open virtaddr MemoryAccessType mem_payload in
/-- A byte store into the I/O window retires with the one-byte memory update.
For example, `SB x5, 3(x6)` at `0x40000010` inserts the low byte of `x5` at `0x40000013`. -/
private theorem sail_store_b (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
    (base val : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail) (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS) :
    (execute_STORE imm rs2 rs1 1).run js.sail = .ok RETIRE_SUCCESS
      (state_after_byte_store js.sail (load_effective_address base imm)
        (Sail.BitVec.extractLsb val 7 0)) := by
  obtain ⟨hs, hm⟩ := io_write_checks js.sail _ 1 hpma hhtif hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) (Nat.mod_one _)
  have hval := mem_write_value_of_plain (n := 1) (load_effective_address base imm)
    (Sail.BitVec.extractLsb val 7 0) js.sail _ hpriv hmprv hs hm
    (write_ram_byte_eq_state_after_byte_store _ _ _)
  have hv := vmem_write_addr_byte_store_bridge _ _ js.sail hpriv hmprv (aligned_access_1 _)
    (mem_write_ea_plain_store_ok _ 1 _) hval
  exact execute_STORE_byte_eq_state_after_byte_store imm rs2 rs1 js val _ ⟨base, hr1, rfl⟩ hr2
    (vmem_write_of_addr imm rs1 _ _ base hr1 _ hv)

open virtaddr MemoryAccessType mem_payload in
/-- A halfword store into the I/O window retires with the two-byte memory update.
For example, `SH x5, 2(x6)` at `0x40000010` inserts the low two bytes of `x5` at `0x40000012`. -/
private theorem sail_store_h (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
    (base val : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail) (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hal : load_effective_address base imm &&& (1 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS) :
    (execute_STORE imm rs2 rs1 2).run js.sail = .ok RETIRE_SUCCESS
      (state_after_halfword_store js.sail (load_effective_address base imm)
        (Sail.BitVec.extractLsb val 15 0)) := by
  obtain ⟨hs, hm⟩ := io_write_checks js.sail _ 2 hpma hhtif hlo (by norm_num) (by norm_num)
    (by have := mod_of_and1 _ hal; simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega)
    (mod_of_and1 _ hal)
  have hval := mem_write_value_of_plain (n := 2) (load_effective_address base imm)
    (Sail.BitVec.extractLsb val 15 0) js.sail _ hpriv hmprv hs hm
    (write_ram_halfword_eq_state_after_halfword_store _ _ _)
  have hv := vmem_write_addr_halfword_store_bridge _ _ js.sail hpriv hmprv
    (halfword_store_aligned_access _ hal) (mem_write_ea_plain_store_ok _ 2 _) hval
  exact execute_STORE_halfword_eq_state_after_halfword_store imm rs2 rs1 js val _
    ⟨base, hr1, rfl⟩ hr2 (vmem_write_of_addr imm rs1 _ _ base hr1 _ hv)

open virtaddr MemoryAccessType mem_payload in
/-- A word store into the I/O window retires with the four-byte memory update.
For example, `SW x5, 4(x6)` at `0x40000010` inserts the low four bytes of `x5` at `0x40000014`. -/
private theorem sail_store_w (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
    (base val : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail) (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hal : load_effective_address base imm &&& (3 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS) :
    (execute_STORE imm rs2 rs1 4).run js.sail = .ok RETIRE_SUCCESS
      (state_after_word_store js.sail (load_effective_address base imm)
        (Sail.BitVec.extractLsb val 31 0)) := by
  obtain ⟨hs, hm⟩ := io_write_checks js.sail _ 4 hpma hhtif hlo (by norm_num) (by norm_num)
    (by have := mod_of_and3 _ hal; simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega)
    (mod_of_and3 _ hal)
  have hval := mem_write_value_of_plain (n := 4) (load_effective_address base imm)
    (Sail.BitVec.extractLsb val 31 0) js.sail _ hpriv hmprv hs hm
    (write_ram_word_eq_state_after_word_store _ _ _)
  have hv := vmem_write_addr_word_store_bridge _ _ js.sail hpriv hmprv
    (word_store_aligned_access _ hal) (mem_write_ea_plain_store_ok _ 4 _) hval
  exact execute_STORE_word_eq_state_after_word_store imm rs2 rs1 js val _ base
    ⟨base, hr1, rfl⟩ hr2 (vmem_write_of_addr imm rs1 _ _ base hr1 _ hv)

open virtaddr MemoryAccessType mem_payload in
/-- A doubleword store into the I/O window retires with the eight-byte memory update.
For example, `SD x5, 8(x6)` at `0x40000010` inserts the eight bytes of `x5` at `0x40000018`. -/
private theorem sail_store_d (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
    (base val : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail) (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hal : load_effective_address base imm &&& (7 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS) :
    (execute_STORE imm rs2 rs1 8).run js.sail = .ok RETIRE_SUCCESS
      (state_after_dword_store js.sail (load_effective_address base imm) val) := by
  obtain ⟨hs, hm⟩ := io_write_checks js.sail _ 8 hpma hhtif hlo (by norm_num) (by norm_num)
    (by have := mod_of_and7 _ hal; simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega)
    (mod_of_and7 _ hal)
  have hval := mem_write_value_of_plain (n := 8) (load_effective_address base imm) val
    js.sail _ hpriv hmprv hs hm (write_ram_dword_eq_state_after_dword_store _ _ _)
  have hv := vmem_write_addr_dword_store_bridge _ _ js.sail hpriv hmprv
    (aligned_dword_access_of_align _ hal).toAlignedAccess (mem_write_ea_plain_store_ok _ 8 _) hval
  exact execute_STORE_dword_of_write imm rs2 rs1 js.sail _ base val hr1 hr2 hv

/-! ### Jolt's device writes -/

/-- A fold of failing-on-`none` steps that starts failing stays failing.
For example, folding `Option.bind` steps from `none` gives `none`. -/
private theorem foldl_bind_none (g : Nat → SailJoltState → Option SailJoltState) (l : List Nat) :
    l.foldl (fun cur k => cur.bind (g k)) none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldl_cons, Option.bind_none] using ih

/-- A fold over eight steps that succeeds has a successful first step.
For example, if the first byte store fails, so does the doubleword store. -/
private theorem foldl_range_first (g : Nat → SailJoltState → Option SailJoltState)
    (s s' : SailJoltState) (n : Nat)
    (h : (List.range (n + 1)).foldl (fun cur k => cur.bind (g k)) (some s) = some s') :
    ∃ s1, g 0 s = some s1 := by
  rw [List.range_succ_eq_map, List.foldl_cons] at h
  cases hg : g 0 s with
  | none =>
    simp only [Option.bind_some, hg] at h
    rw [foldl_bind_none] at h
    cases h
  | some s1 => exact ⟨s1, rfl⟩

/-- A successful byte store below RAM passed the address check.
For example, a store at `0x40000010` that succeeds had `effective_address_ok` true there. -/
private theorem store_raw_below_ok (s s1 : SailJoltState) (a : Nat) (x : BitVec 8)
    (hlt : a < JoltISA.RAM_START_ADDRESS) (h : JoltISA.Mmu.store_raw? s a x = some s1) :
    JoltISA.Mmu.effective_address_ok s.jolt_device a true = true := by
  unfold JoltISA.Mmu.store_raw? at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ a := by omega
  simp only [hnle, ite_false] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i _ hok
      simpa using hok

/-- A retiring doubleword store below RAM is aligned and passed the first byte's check.
For example, a store at `0x40000008` that retires has `effective_address_ok` true there. -/
private theorem store_doubleword_below_inv (A V : BitVec 64) (js js' : SailJoltState)
    (r : Result Bool ExecutionResult) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.store_doubleword A V js = .ok r js') :
    A.toNat % 8 = 0 ∧ r = .Ok true ∧
      JoltISA.Mmu.effective_address_ok js.jolt_device A.toNat true = true := by
  unfold JoltISA.Mmu.store_doubleword at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ A.toNat := by omega
  by_cases hal : A.toNat % 8 = 0
  · simp only [hal, ne_eq, not_true_eq_false, ite_false, hnle] at h
    split at h
    · rename_i s' hs
      cases h
      refine ⟨hal, rfl, ?_⟩
      obtain ⟨s1, hs1⟩ := foldl_range_first
        (fun k s => JoltISA.Mmu.store_raw? s (A.toNat + k) (V.extractLsb' (8 * k) 8)) js _ 7 hs
      exact store_raw_below_ok js s1 _ _ (by simpa using hlt) hs1
    · simp at h
  · simp [hal] at h

/-- An address whose residue modulo eight is zero has clear low three bits.
For example, `0x40000008 &&& 7 = 0`. -/
private theorem and7_of_mod (addr : BitVec 64) (h : addr.toNat % 8 = 0) :
    addr &&& (7 : BitVec 64) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h7 : (7 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

/-- Jolt accepts a store below RAM exactly in the output, panic and termination words.
For example, an address in the input region fails the check. -/
private theorem eao_store_below (d : JoltDevice) (hgeo : IoGeo d) (ea : Nat)
    (hlt : ea < JoltISA.RAM_START_ADDRESS) :
    JoltISA.Mmu.effective_address_ok d ea true = true ↔
      d.memory_layout.output_start.toNat ≤ ea ∧ ea < d.memory_layout.io_end.toNat := by
  have h := hgeo
  obtain ⟨hlow, -, hlo, -, hp, -, ht, he, hb, -⟩ := h
  have hl : memLow d ≤ d.memory_layout.output_start.toNat := hlo
  simp only [JoltISA.Mmu.effective_address_ok, hlt, ite_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, JoltDevice.is_output, JoltDevice.is_panic,
    JoltDevice.is_termination]
  have hm : memLow d = d.memory_layout.get_lowest_address.toNat := rfl
  constructor
  · intro hh
    omega
  · intro hh
    refine ⟨⟨by omega, Or.inl (by omega)⟩, ?_⟩
    omega

/-- The output buffer after storing the eight bytes of `V` at the doubleword `A`.
For example, storing at the start of the buffer overwrites its first eight bytes, growing
the buffer with zeros if it is shorter. -/
private def outputsAfter (d : JoltDevice) (A V : BitVec 64) : Array (BitVec 8) :=
  (deviceHelper% storeOutputBytes) d.outputs (A.toNat - d.memory_layout.output_start.toNat) 8
    (fun k => V.extractLsb' (8 * k) 8)

/-- The device writes of an aligned doubleword store below RAM that retires.
It lies in the output buffer, at the panic word or at the termination word; an output store
rewrites the buffer with the stored bytes, a panic store sets the flag, and a termination
store changes nothing. -/
private theorem store_effect (js gp : SailJoltState) (A V : BitVec 64)
    (hmem : MemRel js.jolt_device js.sail) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.store_doubleword A V js = .ok (.Ok true) gp) :
    A.toNat % 8 = 0 ∧
    ((js.jolt_device.memory_layout.output_start.toNat ≤ A.toNat ∧
        A.toNat + 8 ≤ js.jolt_device.memory_layout.panic.toNat ∧
        gp = { js with jolt_device :=
          { js.jolt_device with outputs := outputsAfter js.jolt_device A V } }) ∨
      (A.toNat = js.jolt_device.memory_layout.panic.toNat ∧
        gp = { js with jolt_device := { js.jolt_device with panic := true } }) ∨
      (A.toNat = js.jolt_device.memory_layout.termination.toNat ∧ gp = js)) := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  obtain ⟨config, hb⟩ := hmem.layout
  obtain ⟨hal, -, hok⟩ := store_doubleword_below_inv A V js gp _ hlt h
  have hal8 := and7_of_mod A hal
  have hin := (eao_store_below _ hgeo _ hlt).mp hok
  have hg := hgeo
  obtain ⟨hlow, hla, hlo, hoa, hp, hma, ht, he, hbd, -, -, -, -⟩ := hg
  have hm : memLow js.jolt_device = js.jolt_device.memory_layout.get_lowest_address.toNat := rfl
  have hord := new_io_ordered config _ hb
  have hpan8 : js.jolt_device.memory_layout.panic.toNat % 8 = 0 := by omega
  have checks : A.toNat + 8 ≤ js.jolt_device.memory_layout.io_end.toNat →
      A.toNat + 8 ≤ JoltISA.RAM_START_ADDRESS →
      JoltConstraints.Soundness.DoublewordAddressChecks js.jolt_device A true := by
    intro h1 h2
    have hn : ¬ JoltISA.RAM_START_ADDRESS ≤ A.toNat := by omega
    simp only [JoltConstraints.Soundness.DoublewordAddressChecks, hn, ite_false]
    intro off hoff
    exact (eao_store_below _ hgeo _ (by omega)).mpr ⟨by omega, by omega⟩
  refine ⟨hal, ?_⟩
  by_cases hout : A.toNat < js.jolt_device.memory_layout.panic.toNat
  · left
    have hA8 : A.toNat + 8 ≤ js.jolt_device.memory_layout.panic.toNat := by omega
    have heff := (deviceHelper% output_store_doubleword) js A V hal8 (by omega) (by omega)
      (checks (by omega) (by omega)) ⟨by omega, hA8⟩ (by omega)
    rw [heff] at h
    simp only [EStateM.Result.ok.injEq, true_and] at h
    exact ⟨by omega, hA8, h.symm⟩
  · right
    have hcase : A.toNat = js.jolt_device.memory_layout.panic.toNat ∨
        A.toNat = js.jolt_device.memory_layout.termination.toNat := by omega
    rcases hcase with hP | hT
    · left
      have heff := (deviceHelper% flag_store_doubleword) config js hb A V true
        (by simpa using hP) hal8 (checks (by omega) (by omega))
      rw [heff] at h
      simp only [EStateM.Result.ok.injEq, true_and, Bool.or_true] at h
      exact ⟨hP, h.symm⟩
    · right
      have heff := (deviceHelper% flag_store_doubleword) config js hb A V false
        (by simpa using hT) hal8 (checks (by omega) (by omega))
      rw [heff] at h
      simp only [EStateM.Result.ok.injEq, true_and, Bool.or_false] at h
      exact ⟨hT, h.symm⟩

/-! ### Jolt's store rows -/

/-- A retiring floor store row is the doubleword store of its scratch register.
For example, if `VirtualStoreW` retires, `store_doubleword` of the containing doubleword
retired, with the register's value. -/
private theorem floorStore_inv (w : JoltISA.AccessWidth) (rs1 : regidx) (vv : JoltISA.VReg)
    (imm base : BitVec 64) (f : ExceptionType) (js js' : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + imm) &&& ~~~(7 : BitVec 64)).toNat < JoltISA.RAM_START_ADDRESS)
    (halign : (base + imm) &&& LoadFamily.alignmentMask w = 0)
    (h : (JoltISA.execInstr ((storeHelper% floorStoreRow) w (.xreg rs1) vv imm f)).run js =
      .ok RETIRE_SUCCESS js') :
    JoltISA.Mmu.store_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) (js.vregs vv) js =
      .ok (.Ok true) js' := by
  have hrow : (storeHelper% floorStoreRow) w (.xreg rs1) vv imm f =
      match w with
      | .byte => .VirtualStoreB (.xreg rs1) (.vreg vv) imm f
      | .halfword => .VirtualStoreH (.xreg rs1) (.vreg vv) imm f
      | .word => .VirtualStoreW (.xreg rs1) (.vreg vv) imm f := by
    cases w <;> rfl
  rw [hrow] at h
  cases hs : JoltISA.Mmu.store_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) (js.vregs vv) js with
  | ok r s' =>
    obtain ⟨-, hr, -⟩ := store_doubleword_below_inv _ _ js s' r hlt hs
    subst hr
    cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
      simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
        hread, halign, ↓reduceIte, readVReg, get, getThe, MonadStateOf.get, EStateM.get, pure,
        EStateM.pure, hs] at h <;>
      simp only [EStateM.Result.ok.injEq, true_and] at h <;>
      rw [h]
  | error e s' =>
    exfalso
    cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
      simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
        hread, halign, ↓reduceIte, readVReg, get, getThe, MonadStateOf.get, EStateM.get, pure,
        EStateM.pure, hs] at h <;>
      simp at h

/-- A retiring narrow store program loads, splices and stores a doubleword.
From a retiring run of the six rows, the effective address is aligned for the width, the
containing doubleword was read as `D`, and the doubleword with the stored bytes spliced in
was stored from a state with the same Sail state and device. -/
private theorem storeRows_inv (w : JoltISA.AccessWidth) (rs1 rs2 : regidx) (imm : BitVec 12)
    (base val : BitVec 64) (js gp : SailJoltState)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execProgram (StoreProgramBlocks.laneStoreProgram w rs1 rs2
        (sign_extend (m := 64) imm))).run js = .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ (D : BitVec 64) (js_s : SailJoltState),
        JoltISA.Mmu.load_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)) js = .ok (.Ok D) js ∧
        js_s.sail = js.sail ∧ js_s.jolt_device = js.jolt_device ∧
        JoltISA.Mmu.store_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64))
          (StoreProgramBlocks.fusedSpliceValue w D val (base + sign_extend (m := 64) imm)) js_s =
          .ok (.Ok true) gp := by
  rw [(storeHelper% laneStoreProgram_rows)] at hrun
  have hrun' : (JoltISA.execProgram (.instr
      (LoadFamily.floorLoadRow w (.vreg 40) (.xreg rs1) (sign_extend (m := 64) imm) .normal
        (ExceptionType.E_SAMO_Addr_Align ()))
      (((storeHelper% fusedSpliceProgram) w 40 41 rs1 rs2 (sign_extend (m := 64) imm)).append
        (.instr ((storeHelper% floorStoreRow) w (.xreg rs1) 40 (sign_extend (m := 64) imm)
          (ExceptionType.E_SAMO_Addr_Align ())) (.done RETIRE_SUCCESS))))).run js =
      .ok RETIRE_SUCCESS gp := hrun
  obtain ⟨js1, h1, hrest⟩ := execProgram_instr_run_retire_inv _ _ js gp hrun'
  obtain ⟨hal, D, hD⟩ := floorLoad_inv w 40 rs1 (sign_extend (m := 64) imm) base .normal
    (ExceptionType.E_SAMO_Addr_Align ()) js js1 hr1 hlt h1
  have e1 := LoadFamily.floorLoad_run w 40 rs1 (sign_extend (m := 64) imm) base D .normal
    (ExceptionType.E_SAMO_Addr_Align ()) js hr1 hal hD (by unfold WritableVReg; decide)
  have hj1 : js1 = stateAfterVRegWrite js 40 D := by
    have := h1.symm.trans e1
    simpa only [EStateM.Result.ok.injEq, true_and] using this
  subst hj1
  obtain ⟨js_s, hsplice, hsail, hdword, hdev⟩ := (storeHelper% fusedSpliceBlock) w 40 41
    (by decide) (by unfold WritableVReg; decide) (by unfold WritableVReg; decide) rs1 rs2
    (sign_extend (m := 64) imm) base val (stateAfterVRegWrite js 40 D) hr1 hr2
  obtain ⟨js2, hs2, hlast⟩ := JoltISA.execProgram_append_succeeds_inv _ _ _ gp hrest
  have hj2 : js2 = js_s := by
    unfold JoltISA.Program.Run at hsplice
    have := hs2.symm.trans hsplice
    simpa only [EStateM.Result.ok.injEq, true_and] using this
  subst hj2
  obtain ⟨js3, h3, hdone⟩ := execProgram_instr_run_retire_inv _ _ _ gp hlast
  have hj3 : js3 = gp := by
    simpa [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] using hdone
  subst hj3
  have hsd := floorStore_inv w rs1 40 (sign_extend (m := 64) imm) base _ js2 js3 (by rw [hsail]; exact hr1)
    hlt hal h3
  have hv40 : js2.vregs 40 = StoreProgramBlocks.fusedSpliceValue w D val
      (base + sign_extend (m := 64) imm) := by
    rw [hdword]
    simp [stateAfterVRegWrite]
  rw [hv40] at hsd
  exact ⟨hal, D, js2, hD, by simpa [stateAfterVRegWrite] using hsail,
    by simpa [stateAfterVRegWrite] using hdev, hsd⟩

/-- A retiring `SD` is an aligned doubleword store of the source register.
For example, `SD` at an aligned I/O address retires only if `store_doubleword` does. -/
private theorem sd_inv (rs1 rs2 : regidx) (imm : BitVec 12) (base val : BitVec 64)
    (js gp : SailJoltState) (hr1 : rX_bits rs1 js.sail = .ok base js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0 ∧
      JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val js =
        .ok (.Ok true) gp := by
  unfold JoltISA.Encoded.SD at hrun
  simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
    hr1, hr2] at hrun
  by_cases halign : (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0
  · refine ⟨halign, ?_⟩
    simp only [halign, ↓reduceIte] at hrun
    change EStateM.bind (JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val)
      _ js = _ at hrun
    cases hs : JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val js with
    | ok r s' =>
      obtain ⟨-, hr, -⟩ := store_doubleword_below_inv _ _ js s' r hlt hs
      subst hr
      simp only [EStateM.bind, hs, pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at hrun
      rw [hrun]
    | error e s' =>
      exfalso
      simp [EStateM.bind, hs] at hrun
  · exfalso
    simp only [halign, ↓reduceIte, pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this

/-! ### The memory Sail's stores leave -/

/-- The memory a store of the low `n` bytes of `V` at `ea` leaves in Sail's state.
Registers are unchanged, bytes `ea` to `ea + n - 1` are the stored bytes and every other
byte is as before. For example, `SH` of `0xBEEF` at `0x40000002` leaves `0xEF` at
`0x40000002`, `0xBE` at `0x40000003` and the rest. -/
private def SailStore (s t : SailState) (ea : BitVec 64) (n : Nat) (V : BitVec 64) : Prop :=
  t.regs = s.regs ∧ ∀ a, t.mem.get? a =
    if ea.toNat ≤ a ∧ a < ea.toNat + n then
      some (V.extractLsb' (8 * (a - ea.toNat)) 8)
    else s.mem.get? a

private theorem sailStore_byte (s : SailState) (ea V : BitVec 64) :
    SailStore s (state_after_byte_store s ea (Sail.BitVec.extractLsb V 7 0)) ea 1 V := by
  refine ⟨rfl, fun a => ?_⟩
  by_cases h : ea.toNat ≤ a ∧ a < ea.toNat + 1
  · rw [ite_eq_left h]
    obtain ⟨j, rfl⟩ : ∃ j, a = ea.toNat + j := ⟨a - ea.toNat, by omega⟩
    have hj : j = 0 := by omega
    subst hj
    rw [stored_byte_get?_hit _ _ _ 0 (by omega)]
    simp only [byte_byte, Nat.add_zero, Nat.sub_self, Nat.mul_zero, Sail.BitVec.extractLsb]
    congr 1
  · rw [ite_eq_right h]
    exact stored_byte_untouched _ _ _ a (by omega)

private theorem sailStore_halfword (s : SailState) (ea V : BitVec 64) :
    SailStore s (state_after_halfword_store s ea (Sail.BitVec.extractLsb V 15 0)) ea 2 V := by
  refine ⟨rfl, fun a => ?_⟩
  by_cases h : ea.toNat ≤ a ∧ a < ea.toNat + 2
  · rw [ite_eq_left h]
    obtain ⟨j, rfl⟩ : ∃ j, a = ea.toNat + j := ⟨a - ea.toNat, by omega⟩
    rw [stored_halfword_get?_hit _ _ _ j (by omega)]
    rw [show ea.toNat + j - ea.toNat = j by omega]
    simp only [halfword_byte, Sail.BitVec.extractLsb]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, hi, decide_true,
      Bool.true_and]
    have hj : j < 2 := by omega
    interval_cases j <;> simp <;> omega
  · rw [ite_eq_right h]
    exact stored_halfword_untouched _ _ _ a (by omega)

private theorem sailStore_word (s : SailState) (ea V : BitVec 64) :
    SailStore s (state_after_word_store s ea (Sail.BitVec.extractLsb V 31 0)) ea 4 V := by
  refine ⟨rfl, fun a => ?_⟩
  by_cases h : ea.toNat ≤ a ∧ a < ea.toNat + 4
  · rw [ite_eq_left h]
    obtain ⟨j, rfl⟩ : ∃ j, a = ea.toNat + j := ⟨a - ea.toNat, by omega⟩
    rw [stored_word_get?_hit _ _ _ j (by omega)]
    rw [show ea.toNat + j - ea.toNat = j by omega]
    simp only [word_byte, Sail.BitVec.extractLsb]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, hi, decide_true,
      Bool.true_and]
    have hj : j < 4 := by omega
    interval_cases j <;> simp <;> omega
  · rw [ite_eq_right h]
    exact stored_word_untouched _ _ _ a (by omega)

private theorem sailStore_dword (s : SailState) (ea V : BitVec 64) :
    SailStore s (state_after_dword_store s ea V) ea 8 V := by
  refine ⟨rfl, fun a => ?_⟩
  by_cases h : ea.toNat ≤ a ∧ a < ea.toNat + 8
  · rw [ite_eq_left h]
    obtain ⟨j, rfl⟩ : ∃ j, a = ea.toNat + j := ⟨a - ea.toNat, by omega⟩
    rw [stored_dword_get?_hit _ _ _ j (by omega)]
    rw [show ea.toNat + j - ea.toNat = j by omega]
    rfl
  · rw [ite_eq_right h]
    exact stored_dword_untouched _ ea _ _ a (by omega)

/-! ### The doubleword Jolt stores -/

private theorem lowHalf_byte (V : BitVec 64) (j : Nat) (hj : j < 2) :
    (Sail.BitVec.extractLsb V 15 0).extractLsb' (8 * j) 8 = V.extractLsb' (8 * j) 8 := by
  simp only [Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, hi, decide_true,
    Bool.true_and]
  interval_cases j <;> simp <;> omega

private theorem lowWord_byte (V : BitVec 64) (j : Nat) (hj : j < 4) :
    (Sail.BitVec.extractLsb V 31 0).extractLsb' (8 * j) 8 = V.extractLsb' (8 * j) 8 := by
  simp only [Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, hi, decide_true,
    Bool.true_and]
  interval_cases j <;> simp <;> omega

/-- Byte `k` of the doubleword a `SB` stores: the stored byte inside the lane and the
original doubleword's byte outside it.
For example, `SB` at address 5 replaces byte 5. -/
private theorem fusedSplice_byte_b (D V b : BitVec 64) (imm : BitVec 12) (k : Nat) (hk : k < 8) :
    (StoreProgramBlocks.fusedSpliceValue .byte D V
        (load_effective_address b imm)).extractLsb' (8 * k) 8 =
      if (load_effective_address b imm).toNat % 8 ≤ k ∧
          k < (load_effective_address b imm).toNat % 8 + 1 then
        V.extractLsb' (8 * (k - (load_effective_address b imm).toNat % 8)) 8
      else D.extractLsb' (8 * k) 8 := by
  have hs := StoreSplice.byteStoreFacts_of_effective_address b imm
  generalize load_effective_address b imm = ea at hs ⊢
  generalize compute_aligned_dword_base_address b imm = base at hs
  have hsp := StoreSplice.fusedByteSplice_eq D V ea base hs
  have hb : base.toNat = ea.toNat / 8 * 8 := by
    rw [hs.base_is_aligned]; exact toNat_and_neg8 ea
  have hnat := hs.ea_toNat
  have hoff := hs.byte_offset_cases
  generalize (ea - base).toNat = off at hoff hsp hnat
  have hoff' : off = ea.toNat % 8 := by rcases hoff with h | h | h | h | h | h | h | h <;> omega
  rw [← hoff']
  change ((D &&& ~~~(jolt_virtual_window_mask_b_value ea 0)) +
    jolt_virtual_shift_data_b_value V ea).extractLsb' (8 * k) 8 = _
  rw [hsp, Nat.mul_comm off 8]
  by_cases hin : off ≤ k ∧ k < off + 1
  · rw [ite_eq_left hin]
    obtain ⟨j, rfl⟩ : ∃ j, k = off + j := ⟨k - off, by omega⟩
    have := StoreSplice.byteSplice_target_bytes D (Sail.BitVec.extractLsb V 7 0) off hoff j
      (by omega)
    simp only [dword_byte, byte_byte] at this
    rw [this]
    have hj : j = 0 := by omega
    subst hj
    simp only [Nat.add_zero, Nat.sub_self, Nat.mul_zero, Sail.BitVec.extractLsb]
    rfl
  · rw [ite_eq_right hin]
    have := StoreSplice.byteSplice_other_bytes D (Sail.BitVec.extractLsb V 7 0) off hoff k hk
      (by omega)
    simpa [dword_byte] using this

/-- Byte `k` of the doubleword an `SH` stores. -/
private theorem fusedSplice_byte_h (D V b : BitVec 64) (imm : BitVec 12)
    (hal : load_effective_address b imm &&& (1 : BitVec 64) = 0) (k : Nat) (hk : k < 8) :
    (StoreProgramBlocks.fusedSpliceValue .halfword D V
        (load_effective_address b imm)).extractLsb' (8 * k) 8 =
      if (load_effective_address b imm).toNat % 8 ≤ k ∧
          k < (load_effective_address b imm).toNat % 8 + 2 then
        V.extractLsb' (8 * (k - (load_effective_address b imm).toNat % 8)) 8
      else D.extractLsb' (8 * k) 8 := by
  have hs := StoreSplice.halfwordStoreFacts_of_effective_address b imm hal
  generalize load_effective_address b imm = ea at hs ⊢
  generalize compute_aligned_dword_base_address b imm = base at hs
  have hsp := StoreSplice.fusedHalfwordSplice_eq D V ea base hs
  have hb : base.toNat = ea.toNat / 8 * 8 := by
    rw [hs.base_is_aligned]; exact toNat_and_neg8 ea
  have hnat := hs.ea_toNat
  have hoff := hs.halfword_offset_cases
  generalize (ea - base).toNat = off at hoff hsp hnat
  have hoff' : off = ea.toNat % 8 := by rcases hoff with h | h | h | h <;> omega
  rw [← hoff']
  change ((D &&& ~~~(jolt_virtual_window_mask_h_value ea 0)) +
    jolt_virtual_shift_data_h_value V ea).extractLsb' (8 * k) 8 = _
  rw [hsp, Nat.mul_comm off 8]
  by_cases hin : off ≤ k ∧ k < off + 2
  · rw [ite_eq_left hin]
    obtain ⟨j, rfl⟩ : ∃ j, k = off + j := ⟨k - off, by omega⟩
    have := StoreSplice.halfwordSplice_target_bytes D (Sail.BitVec.extractLsb V 15 0) off hoff j
      (by omega)
    simp only [dword_byte, halfword_byte] at this
    rw [this, Nat.add_sub_cancel_left]
    exact lowHalf_byte V j (by omega)
  · rw [ite_eq_right hin]
    have := StoreSplice.halfwordSplice_other_bytes D (Sail.BitVec.extractLsb V 15 0) off hoff k hk
      (by omega)
    simpa [dword_byte] using this

/-- Byte `k` of the doubleword an `SW` stores. -/
private theorem fusedSplice_byte_w (D V b : BitVec 64) (imm : BitVec 12)
    (hal : load_effective_address b imm &&& (3 : BitVec 64) = 0) (k : Nat) (hk : k < 8) :
    (StoreProgramBlocks.fusedSpliceValue .word D V
        (load_effective_address b imm)).extractLsb' (8 * k) 8 =
      if (load_effective_address b imm).toNat % 8 ≤ k ∧
          k < (load_effective_address b imm).toNat % 8 + 4 then
        V.extractLsb' (8 * (k - (load_effective_address b imm).toNat % 8)) 8
      else D.extractLsb' (8 * k) 8 := by
  have hs := StoreSplice.wordStoreFacts_of_effective_address b imm hal
  generalize load_effective_address b imm = ea at hs ⊢
  generalize compute_aligned_dword_base_address b imm = base at hs
  have hsp := StoreSplice.fusedWordSplice_eq D V ea base hs
  have hb : base.toNat = ea.toNat / 8 * 8 := by
    rw [hs.base_is_aligned]; exact toNat_and_neg8 ea
  have hnat := hs.ea_toNat
  have hoff := hs.word_offset_cases
  generalize (ea - base).toNat = off at hoff hsp hnat
  have hoff' : off = ea.toNat % 8 := by rcases hoff with h | h <;> omega
  rw [← hoff']
  change ((D &&& ~~~(jolt_virtual_window_mask_w_value ea 0)) +
    jolt_virtual_shift_data_w_value V ea).extractLsb' (8 * k) 8 = _
  rw [hsp, Nat.mul_comm off 8]
  by_cases hin : off ≤ k ∧ k < off + 4
  · rw [ite_eq_left hin]
    obtain ⟨j, rfl⟩ : ∃ j, k = off + j := ⟨k - off, by omega⟩
    have := StoreSplice.wordSplice_target_bytes D (Sail.BitVec.extractLsb V 31 0) off hoff j
      (by omega)
    simp only [dword_byte, word_byte] at this
    rw [this, Nat.add_sub_cancel_left]
    exact lowWord_byte V j (by omega)
  · rw [ite_eq_right hin]
    have := StoreSplice.wordSplice_other_bytes D (Sail.BitVec.extractLsb V 31 0) off hoff k hk
      (by omega)
    simpa [dword_byte] using this

/-! ### Reading the device and Sail's panic word -/

/-- Eight present bytes read as a doubleword whose bytes are those bytes.
For example, if bytes `0x40000008` to `0x4000000f` are in memory, `read_doubleword?`
returns the doubleword they form. -/
private theorem read_dword_of_present {f : Nat → Option (BitVec 8)} {a : Nat}
    (h : ∀ k < 8, ∃ b, f (a + k) = some b) :
    ∃ W, JoltISA.read_doubleword? f a = some W ∧ ∀ k < 8, f (a + k) = some (W.extractLsb' (8 * k) 8) := by
  obtain ⟨b0, h0⟩ := h 0 (by omega)
  obtain ⟨b1, h1⟩ := h 1 (by omega)
  obtain ⟨b2, h2⟩ := h 2 (by omega)
  obtain ⟨b3, h3⟩ := h 3 (by omega)
  obtain ⟨b4, h4⟩ := h 4 (by omega)
  obtain ⟨b5, h5⟩ := h 5 (by omega)
  obtain ⟨b6, h6⟩ := h 6 (by omega)
  obtain ⟨b7, h7⟩ := h 7 (by omega)
  have hr : JoltISA.read_doubleword? f a = some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) := by
    unfold JoltISA.read_doubleword?
    simp only [Nat.add_zero] at h0
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  exact ⟨_, hr, read_doubleword_bytes hr⟩

/-- A change of the output buffer or the panic flag changes `load?` only where it is
read: the output buffer is read only at output addresses that are not panic addresses,
and the flag only at panic addresses.
Stated for the three fields that matter; `load?` reads nothing else that these change. -/
private theorem load_outputs_congr (d : JoltDevice) (o : Array (BitVec 8)) (a : Nat)
    (h : d.is_panic a = true ∨ d.is_output a = false) :
    ({ d with outputs := o } : JoltDevice).load? a = d.load? a := by
  have e1 : ({ d with outputs := o } : JoltDevice).is_panic a = d.is_panic a := rfl
  have e2 : ({ d with outputs := o } : JoltDevice).is_termination a = d.is_termination a := rfl
  have e3 : ({ d with outputs := o } : JoltDevice).is_input a = d.is_input a := rfl
  have e4 : ({ d with outputs := o } : JoltDevice).is_trusted_advice a = d.is_trusted_advice a :=
    rfl
  have e5 : ({ d with outputs := o } : JoltDevice).is_untrusted_advice a =
      d.is_untrusted_advice a := rfl
  have e6 : ({ d with outputs := o } : JoltDevice).is_output a = d.is_output a := rfl
  unfold JoltDevice.load?
  simp only [e1, e2, e3, e4, e5, e6]
  rcases h with h | h
  · simp [h]
  · simp [h]

private theorem load_outputs_in (d : JoltDevice) (hgeo : IoGeo d) (o : Array (BitVec 8))
    (a : Nat) (h : d.memory_layout.output_start.toNat ≤ a ∧ a < d.memory_layout.panic.toNat) :
    ({ d with outputs := o } : JoltDevice).load? a =
      some (o[a - d.memory_layout.output_start.toNat]?.getD 0) := by
  have hg := hgeo
  obtain ⟨-, -, -, -, hp, -, ht, -, -, hi, htr, hun, -⟩ := hg
  have e1 : ({ d with outputs := o } : JoltDevice).is_panic a = false := by
    simp only [JoltDevice.is_panic]; simp; omega
  have e2 : ({ d with outputs := o } : JoltDevice).is_termination a = false := by
    simp only [JoltDevice.is_termination]; simp; omega
  have e3 : ({ d with outputs := o } : JoltDevice).is_input a = false := by
    simp only [JoltDevice.is_input]; simp; omega
  have e4 : ({ d with outputs := o } : JoltDevice).is_trusted_advice a = false := by
    simp only [JoltDevice.is_trusted_advice]; simp; omega
  have e5 : ({ d with outputs := o } : JoltDevice).is_untrusted_advice a = false := by
    simp only [JoltDevice.is_untrusted_advice]; simp; omega
  have e6 : ({ d with outputs := o } : JoltDevice).is_output a = true := by
    simp only [JoltDevice.is_output]; simp; omega
  unfold JoltDevice.load?
  simp only [e1, e2, e3, e4, e5, e6]
  simp

/-- The panic flag is read only at panic addresses. -/
private theorem load_panic_congr (d : JoltDevice) (b : Bool) (a : Nat)
    (h : d.is_panic a = false) :
    ({ d with panic := b } : JoltDevice).load? a = d.load? a := by
  have e1 : ({ d with panic := b } : JoltDevice).is_panic a = d.is_panic a := rfl
  have e2 : ({ d with panic := b } : JoltDevice).is_termination a = d.is_termination a := rfl
  have e3 : ({ d with panic := b } : JoltDevice).is_input a = d.is_input a := rfl
  have e4 : ({ d with panic := b } : JoltDevice).is_trusted_advice a = d.is_trusted_advice a :=
    rfl
  have e5 : ({ d with panic := b } : JoltDevice).is_untrusted_advice a =
      d.is_untrusted_advice a := rfl
  have e6 : ({ d with panic := b } : JoltDevice).is_output a = d.is_output a := rfl
  unfold JoltDevice.load?
  simp only [e1, e2, e3, e4, e5, e6, h]
  simp

/-- The output-buffer fold of `Mmu.store_doubleword_raw`: successive bytes starting at
`start`, extending the array with zeros. -/
private def storeBytes (bytes : Array (BitVec 8)) (start count : Nat)
    (value : Nat → BitVec 8) : Array (BitVec 8) :=
  (deviceHelper% storeOutputBytes) bytes start count value

private theorem storeBytes_succ (bytes : Array (BitVec 8)) (start count : Nat)
    (value : Nat → BitVec 8) :
    storeBytes bytes start (count + 1) value =
      (storeBytes bytes start count value ++
        Array.replicate (start + count + 1 - (storeBytes bytes start count value).size) 0).set!
        (start + count) (value count) := by
  change (List.range (count + 1)).foldl (fun current offset =>
    (current ++ Array.replicate (start + offset + 1 - current.size) 0).set!
      (start + offset) (value offset)) bytes = _
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Writing `count` bytes into the output buffer leaves at most the larger of the old size
and the end of the written range. -/
private theorem storeBytes_size (bytes : Array (BitVec 8)) (start count : Nat)
    (value : Nat → BitVec 8) :
    (storeBytes bytes start count value).size ≤ max bytes.size (start + count) := by
  induction count with
  | zero => exact le_max_of_le_left (le_refl _)
  | succ count ih =>
    rw [storeBytes_succ]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_append,
      Array.size_replicate]
    omega

/-- A doubleword read depends only on its eight bytes. -/
private theorem read_dword_congr (f g : Nat → Option (BitVec 8)) (a : Nat)
    (h : ∀ k < 8, f (a + k) = g (a + k)) :
    JoltISA.read_doubleword? f a = JoltISA.read_doubleword? g a := by
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  unfold JoltISA.read_doubleword?
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]

/-- Sail's panic word is unchanged by a store that writes none of its bytes. -/
private theorem sailPanicWord_unaffected (d : JoltDevice) (s t : SailState) (ea : BitVec 64)
    (n : Nat) (V : BitVec 64) (hst : SailStore s t ea n V)
    (hout : ∀ k < 8, ¬ (ea.toNat ≤ d.memory_layout.panic.toNat + k ∧
      d.memory_layout.panic.toNat + k < ea.toNat + n)) :
    sailPanicWord d t = sailPanicWord d s := by
  unfold sailPanicWord
  rw [read_dword_congr t.mem.get? s.mem.get? _
    (fun k hk => by rw [hst.2, ite_eq_right (hout k hk)])]

/-- A byte address outside the flag words is below the panic word or at or above the end of
the I/O window. -/
private theorem flag_false (d : JoltDevice) (a : Nat) (h : IsFlagWord d a = false) :
    a < d.memory_layout.panic.toNat ∨ d.memory_layout.io_end.toNat ≤ a := by
  simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le,
    Nat.not_lt] at h
  omega

/-- The memory relation after a store, from what changes in the device.
It reduces the relation to the bytes of the lane agreeing with the new device, the
bytes outside it agreeing with the old, and the panic word. -/
private theorem memRel_of_store (d d' : JoltDevice) (s t : SailState) (ea : BitVec 64)
    (n : Nat) (V : BitVec 64) (hmem : MemRel d s) (hst : SailStore s t ea n V)
    (hlay : d'.memory_layout = d.memory_layout)
    (hsize : d'.outputs.size ≤ d.memory_layout.max_output_size.toNat)
    (hio : ∀ a, memLow d ≤ a → a < RAM_START_ADDRESS → IsFlagWord d a = false →
      (ea.toNat ≤ a ∧ a < ea.toNat + n →
        V.extractLsb' (8 * (a - ea.toNat)) 8 = (d'.load? a).getD 0) ∧
      (¬ (ea.toNat ≤ a ∧ a < ea.toNat + n) → (d.load? a).getD 0 = (d'.load? a).getD 0))
    (hpan : d'.panic = true ↔ sailPanicWord d t ≠ 0) : MemRel d' t := by
  have hl : memLow d' = memLow d := by simp [memLow, hlay]
  have hh : memHigh d' = memHigh d := by simp [memHigh, hlay]
  have hf : ∀ a, IsFlagWord d' a = IsFlagWord d a := fun a => by simp [IsFlagWord, hlay]
  have hs2 := hst.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a h1 h2
    rw [hl] at h1
    rw [hh] at h2
    rw [hs2 a]
    by_cases hin : ea.toNat ≤ a ∧ a < ea.toNat + n
    · rw [ite_eq_left hin]; exact ⟨_, rfl⟩
    · rw [ite_eq_right hin]; exact hmem.present a h1 h2
  · intro a h1 h2 h3
    rw [hl] at h1
    rw [hf] at h3
    obtain ⟨hy, hn⟩ := hio a h1 h2 h3
    rw [hs2 a]
    by_cases hin : ea.toNat ≤ a ∧ a < ea.toNat + n
    · rw [ite_eq_left hin, hy hin]
    · rw [ite_eq_right hin, hmem.io a h1 h2 h3, hn hin]
  · have : sailPanicWord d' t = sailPanicWord d t := by simp [sailPanicWord, hlay]
    rw [this]
    exact hpan
  · obtain ⟨config, hb⟩ := hmem.layout
    exact ⟨config, by rw [hlay]; exact hb⟩
  · rw [hlay]
    exact hsize

private theorem outputsAfter_eq (d : JoltDevice) (A V : BitVec 64) :
    outputsAfter d A V = storeBytes d.outputs (A.toNat - d.memory_layout.output_start.toNat) 8
      (fun k => V.extractLsb' (8 * k) 8) := rfl

/-- The device byte at an output address is the buffer's byte there. -/
private theorem load_output_byte (d : JoltDevice) (hgeo : IoGeo d) (a : Nat)
    (h : d.memory_layout.output_start.toNat ≤ a ∧ a < d.memory_layout.panic.toNat) :
    (d.load? a).getD 0 = d.outputs[a - d.memory_layout.output_start.toNat]?.getD 0 := by
  have := load_outputs_in d hgeo d.outputs a h
  have e : ({ d with outputs := d.outputs } : JoltDevice) = d := rfl
  rw [e] at this
  rw [this]
  rfl

/-- The device byte after replacing the output buffer. -/
private theorem load_outputs_getD (d : JoltDevice) (hgeo : IoGeo d) (o : Array (BitVec 8))
    (a : Nat) :
    (({ d with outputs := o } : JoltDevice).load? a).getD 0 =
      if d.memory_layout.output_start.toNat ≤ a ∧ a < d.memory_layout.panic.toNat then
        o[a - d.memory_layout.output_start.toNat]?.getD 0 else (d.load? a).getD 0 := by
  by_cases h : d.memory_layout.output_start.toNat ≤ a ∧ a < d.memory_layout.panic.toNat
  · rw [ite_eq_left h, load_outputs_in d hgeo o a h]
    rfl
  · rw [ite_eq_right h, load_outputs_congr d o a ?_]
    have hg := hgeo
    obtain ⟨-, -, -, -, hp, -, ht, -, -, -, -, -, -⟩ := hg
    rcases Nat.lt_or_ge a d.memory_layout.panic.toNat with hlt | hge
    · right
      have : ¬ d.memory_layout.output_start.toNat ≤ a := fun hos => h ⟨hos, hlt⟩
      simp [JoltDevice.is_output, this]
    · by_cases htm : a < d.memory_layout.termination.toNat
      · left
        simp [JoltDevice.is_panic, hge, htm]
      · right
        simp [JoltDevice.is_output]
        omega

/-- A retiring doubleword store below RAM leaves Sail's memory related to the new device.
`A` is the containing doubleword of the access `ea`, `n` bytes of `val`; Jolt stored `W`,
which holds the stored bytes inside the lane and the doubleword `D` it read outside it.
The Sail state `t` is the one Sail's store leaves. -/
private theorem store_finish (js js_s gp : SailJoltState) (t : SailState)
    (A W ea val D : BitVec 64) (n : Nat)
    (hmem : MemRel js.jolt_device js.sail)
    (hs1 : js_s.sail = js.sail) (hs2 : js_s.jolt_device = js.jolt_device)
    (_hn : 0 < n) (hA : A.toNat = ea.toNat / 8 * 8) (hwin : ea.toNat % 8 + n ≤ 8)
    (hDb : ∀ k < 8, ¬ (ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n) →
      D.extractLsb' (8 * k) 8 = (js.jolt_device.load? (A.toNat + k)).getD 0)
    (hWb : ∀ k < 8, W.extractLsb' (8 * k) 8 =
      if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n then
        val.extractLsb' (8 * (k - ea.toNat % 8)) 8 else D.extractLsb' (8 * k) 8)
    (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hst : JoltISA.Mmu.store_doubleword A W js_s = .ok (.Ok true) gp)
    (hsail : SailStore js.sail t ea n val)
    (hpanic : ea.toNat / 8 * 8 = js.jolt_device.memory_layout.panic.toNat →
      ∀ old new : BitVec 64, (old ≠ 0 ↔ js.jolt_device.panic = true) →
        (∀ k < 8, new.extractLsb' (8 * k) 8 =
          if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n then
            val.extractLsb' (8 * (k - ea.toNat % 8)) 8 else old.extractLsb' (8 * k) 8) →
        new ≠ 0) :
    gp.sail = js.sail ∧ MemRel gp.jolt_device t := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  have hmem_s : MemRel js_s.jolt_device js_s.sail := by rw [hs1, hs2]; exact hmem
  obtain ⟨hA8, hcases⟩ := store_effect js_s gp A W hmem_s hlt hst
  have hg := hgeo
  obtain ⟨hlow, hla, hlo, hoa, hp, hma, ht, he, hbd, -, -, -, hheap⟩ := hg
  have hH : memHigh js.jolt_device = js.jolt_device.memory_layout.heap_end.toNat + 8 := rfl
  have hmodlt : ea.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
  have hs2' := hsail.2
  rw [hs2] at hcases
  rcases hcases with ⟨hos, hAp, rfl⟩ | ⟨hAp, rfl⟩ | ⟨hAt, rfl⟩
  · -- the output buffer
    refine ⟨hs1, ?_⟩
    change MemRel ({ js.jolt_device with
      outputs := outputsAfter js.jolt_device A W } : JoltDevice) t
    refine memRel_of_store js.jolt_device _ js.sail t ea n val hmem hsail rfl ?_ ?_ ?_
    · have hsz := storeBytes_size js.jolt_device.outputs
        (A.toNat - js.jolt_device.memory_layout.output_start.toNat) 8
        (fun k => W.extractLsb' (8 * k) 8)
      have := hmem.outputs_size
      dsimp only
      rw [outputsAfter_eq]
      omega
    · intro a h1 h2 h3
      have hL := load_outputs_getD js.jolt_device hgeo (outputsAfter js.jolt_device A W) a
      have hR : (outputsAfter js.jolt_device A W)[a -
          js.jolt_device.memory_layout.output_start.toNat]?.getD 0 =
          if A.toNat - js.jolt_device.memory_layout.output_start.toNat ≤
              a - js.jolt_device.memory_layout.output_start.toNat ∧
            a - js.jolt_device.memory_layout.output_start.toNat <
              A.toNat - js.jolt_device.memory_layout.output_start.toNat + 8 then
            W.extractLsb' (8 * (a - js.jolt_device.memory_layout.output_start.toNat -
              (A.toNat - js.jolt_device.memory_layout.output_start.toNat))) 8
          else js.jolt_device.outputs[a -
            js.jolt_device.memory_layout.output_start.toNat]?.getD 0 :=
        (deviceHelper% storeOutputBytes_read) js.jolt_device.outputs
          (A.toNat - js.jolt_device.memory_layout.output_start.toNat) 8 _ _
      constructor
      · intro hl
        have hin : js.jolt_device.memory_layout.output_start.toNat ≤ a ∧
            a < js.jolt_device.memory_layout.panic.toNat := by omega
        rw [hL, ite_eq_left hin, hR, ite_eq_left (by omega)]
        rw [show a - js.jolt_device.memory_layout.output_start.toNat -
          (A.toNat - js.jolt_device.memory_layout.output_start.toNat) = a - A.toNat by omega,
          hWb (a - A.toNat) (by omega), ite_eq_left (by omega),
          show a - A.toNat - ea.toNat % 8 = a - ea.toNat by omega]
      · intro hl
        by_cases hin : js.jolt_device.memory_layout.output_start.toNat ≤ a ∧
            a < js.jolt_device.memory_layout.panic.toNat
        · rw [hL, ite_eq_left hin, hR, load_output_byte js.jolt_device hgeo a hin]
          by_cases hw : A.toNat ≤ a ∧ a < A.toNat + 8
          · rw [ite_eq_left (by omega), show a - js.jolt_device.memory_layout.output_start.toNat -
              (A.toNat - js.jolt_device.memory_layout.output_start.toNat) = a - A.toNat by omega,
              hWb (a - A.toNat) (by omega), ite_eq_right (by omega), hDb (a - A.toNat) (by omega) (by omega),
              show A.toNat + (a - A.toNat) = a by omega,
              load_output_byte js.jolt_device hgeo a hin]
          · rw [ite_eq_right (by omega)]
        · rw [hL, ite_eq_right hin]
    · change js.jolt_device.panic = true ↔ _
      rw [sailPanicWord_unaffected js.jolt_device js.sail t ea n val hsail
        (fun k hk => by omega)]
      exact hmem.panic
  · -- the panic word
    refine ⟨hs1, ?_⟩
    change MemRel ({ js.jolt_device with panic := true } : JoltDevice) t
    refine memRel_of_store js.jolt_device _ js.sail t ea n val hmem hsail rfl
      hmem.outputs_size ?_ ?_
    · intro a h1 h2 h3
      have hfa := flag_false _ a h3
      constructor
      · intro hl
        omega
      · intro hl
        exact (load_panic_congr js.jolt_device true a (by simp [JoltDevice.is_panic]; omega)).symm ▸ rfl
    · have hpb : ∀ k < 8, ∃ b, js.sail.mem.get? (js.jolt_device.memory_layout.panic.toNat + k) =
          some b := fun k hk => hmem.present _ (by omega) (by omega)
      obtain ⟨old, hrd, hold⟩ := read_dword_of_present hpb
      have hpbt : ∀ k < 8, ∃ b, t.mem.get? (js.jolt_device.memory_layout.panic.toNat + k) =
          some b := by
        intro k hk
        rw [hs2' (js.jolt_device.memory_layout.panic.toNat + k)]
        split_ifs
        · exact ⟨_, rfl⟩
        · exact hpb k hk
      obtain ⟨new, hrdt, hnew⟩ := read_dword_of_present hpbt
      have hsw : sailPanicWord js.jolt_device t = new := by simp [sailPanicWord, hrdt]
      have hso : sailPanicWord js.jolt_device js.sail = old := by simp [sailPanicWord, hrd]
      have hold_iff : old ≠ 0 ↔ js.jolt_device.panic = true := by
        rw [← hso]; exact hmem.panic.symm
      have hbytes : ∀ k < 8, new.extractLsb' (8 * k) 8 =
          if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n then
            val.extractLsb' (8 * (k - ea.toNat % 8)) 8 else old.extractLsb' (8 * k) 8 := by
        intro k hk
        have h1 := hnew k hk
        rw [hs2' (js.jolt_device.memory_layout.panic.toNat + k)] at h1
        by_cases hl : ea.toNat ≤ js.jolt_device.memory_layout.panic.toNat + k ∧
            js.jolt_device.memory_layout.panic.toNat + k < ea.toNat + n
        · rw [ite_eq_left hl] at h1
          rw [ite_eq_left (by omega), ← Option.some.inj h1]
          rw [show js.jolt_device.memory_layout.panic.toNat + k - ea.toNat =
            k - ea.toNat % 8 by omega]
        · rw [ite_eq_right hl] at h1
          rw [ite_eq_right (by omega)]
          have := hold k hk
          rw [h1] at this
          exact Option.some.inj this
      have hnz := hpanic (by omega) old new hold_iff hbytes
      rw [hsw]
      exact ⟨fun _ => hnz, fun _ => rfl⟩
  · -- the termination word
    refine ⟨hs1, ?_⟩
    rw [hs2]
    refine memRel_of_store js.jolt_device _ js.sail t ea n val hmem hsail rfl
      hmem.outputs_size ?_ ?_
    · intro a h1 h2 h3
      have hfa := flag_false _ a h3
      constructor
      · intro hl
        omega
      · intro _
        rfl
    · rw [sailPanicWord_unaffected js.jolt_device js.sail t ea n val hsail
        (fun k hk => by omega)]
      exact hmem.panic


/-- A retiring doubleword store below RAM lies inside the I/O window.
For example, a retiring store at an output address is at or above `0x40000000` and its
eight bytes end at or below `RAM_START_ADDRESS`. -/
private theorem store_bounds (js gp : SailJoltState) (A V : BitVec 64)
    (hmem : MemRel js.jolt_device js.sail) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.store_doubleword A V js = .ok (.Ok true) gp) :
    0x40000000 ≤ A.toNat ∧ A.toNat + 8 ≤ JoltISA.RAM_START_ADDRESS := by
  have hgeo := IoGeo.of_layout _ hmem.layout
  obtain ⟨-, hc⟩ := store_effect js gp A V hmem hlt h
  obtain ⟨hlow, hla, hlo, hoa, hp, hma, ht, he, hbd, -, -, -, -⟩ := hgeo
  rcases hc with ⟨h1, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> constructor <;> omega

/-- A transition that keeps Sail's state and the projected virtual registers has the same
projection. -/
private theorem systemProject_of_store (js gp : SailJoltState) (hsail : gp.sail = js.sail)
    (hproj : Projection.ProjectedVRegsPreserved js gp) :
    System.systemProject gp = System.systemProject js := by
  rcases hproj with ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus, hresW, hresD⟩
  unfold System.systemProject
  simp only [hsail, hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus, hresW, hresD]

/-- The access premises of a store, at its own effective address.
For example, for `SB x5, 0(x6)` they give that the address is below RAM and, when it
lies in the panic doubleword, that the stored bytes spliced into any old panic word leave
it nonzero. -/
private theorem store_access (i : RiscvInstruction) (js : SailJoltState) (rs1 rs2 : regidx)
    (imm : BitVec 12) (n : Nat)
    (hacc : i.memAccess js =
      some (true, n, load_effective_address (sourceValue (.xreg rs1) js) imm))
    (hst : i.storeData js = sourceValue (.xreg rs2) js)
    (hio : i.IoAccess js) (hpanic : i.PanicStoreNonzero js) :
    (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat <
        JoltISA.RAM_START_ADDRESS ∧
      ((load_effective_address (sourceValue (.xreg rs1) js) imm).toNat / 8 * 8 =
          js.jolt_device.memory_layout.panic.toNat →
        ∀ old new : BitVec 64, (old ≠ 0 ↔ js.jolt_device.panic = true) →
          (∀ k < 8, new.extractLsb' (8 * k) 8 =
            if (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 ≤ k ∧
                k < (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 + n then
              (sourceValue (.xreg rs2) js).extractLsb' (8 * (k -
                (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8)) 8
            else old.extractLsb' (8 * k) 8) →
          new ≠ 0) := by
  obtain ⟨store, width, ea, hacc', hlt⟩ := hio
  rw [hacc] at hacc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
  obtain ⟨-, -, rfl⟩ := hacc'
  refine ⟨hlt, ?_⟩
  have := hpanic n _ hacc
  rwa [hst] at this

/-! ### Stores, assembled -/

/-- A narrow store in the I/O window, from the rows of its expansion to Sail's `execute`.
Jolt loads the doubleword around the access, splices the stored bytes in and stores it;
Sail stores the bytes alone. -/
private theorem narrow_store_core (w : JoltISA.AccessWidth) (n : Nat) (hn : 0 < n)
    (hfit : ∀ x : BitVec 64, x &&& LoadFamily.alignmentMask w = 0 → x.toNat % 8 + n ≤ 8)
    (rs1 rs2 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemRel js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hpanic : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat / 8 * 8 =
          js.jolt_device.memory_layout.panic.toNat →
        ∀ old new : BitVec 64, (old ≠ 0 ↔ js.jolt_device.panic = true) →
          (∀ k < 8, new.extractLsb' (8 * k) 8 =
            if (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 ≤ k ∧
                k < (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 + n then
              (sourceValue (.xreg rs2) js).extractLsb' (8 * (k -
                (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8)) 8
            else old.extractLsb' (8 * k) 8) →
          new ≠ 0)
    (hsplice : ∀ (b D V : BitVec 64), load_effective_address b imm &&&
        LoadFamily.alignmentMask w = 0 → ∀ k < 8,
      (StoreProgramBlocks.fusedSpliceValue w D V
          (load_effective_address b imm)).extractLsb' (8 * k) 8 =
        if (load_effective_address b imm).toNat % 8 ≤ k ∧
            k < (load_effective_address b imm).toNat % 8 + n then
          V.extractLsb' (8 * (k - (load_effective_address b imm).toNat % 8)) 8
        else D.extractLsb' (8 * k) 8)
    (hsail : ∀ (base val : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      rX_bits rs2 js.sail = .ok val js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS →
      ∃ t : SailState, (execute_STORE imm rs2 rs1 n).run js.sail = .ok RETIRE_SUCCESS t ∧
        SailStore js.sail t (load_effective_address base imm) n val)
    (hrun : (JoltISA.execProgram (StoreProgramBlocks.laneStoreProgram w rs1 rs2
        (sign_extend (m := 64) imm))).run js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.STORE (imm, rs2, rs1, n)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  generalize sourceValue (.xreg rs1) js = base at hr1 hhi hpanic
  generalize sourceValue (.xreg rs2) js = val at hr2 hpanic
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]; exact hhi
  have hltA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    rw [neg8_eq, toNat_and_neg8]
    omega
  obtain ⟨hal, D, js_s, hD, hs1, hs2, hst⟩ :=
    storeRows_inv w rs1 rs2 imm base val js gp hr1 hr2 hltA hrun
  have hmem_s : MemRel js_s.jolt_device js_s.sail := by rw [hs1, hs2]; exact hmem
  obtain ⟨hlo40, hhi8⟩ := store_bounds js_s gp _ _ hmem_s hltA hst
  have hal' : load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 := hal
  have hfit' := hfit _ hal'
  have hA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat =
      (load_effective_address base imm).toNat / 8 * 8 := by
    rw [neg8_eq, toNat_and_neg8]
  obtain ⟨-, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hltA hD
  cases hr
  have hDb : ∀ k < 8, ¬ ((load_effective_address base imm).toNat % 8 ≤ k ∧
      k < (load_effective_address base imm).toNat % 8 + n) →
      D.extractLsb' (8 * k) 8 =
        (js.jolt_device.load? (((base + sign_extend (m := 64) imm) &&&
          ~~~(7 : BitVec 64)).toNat + k)).getD 0 := by
    intro k hk _
    rw [load_raw_load js _ _ (by simp only [JoltISA.RAM_START_ADDRESS] at hhi8 ⊢; omega)
      (read_doubleword_bytes hrd k hk)]
    rfl
  obtain ⟨t, hex, hst'⟩ := hsail base val hr1 hr2 hal' (by omega) hhi
  obtain ⟨hgp, hmemT⟩ := store_finish js js_s gp t _ _ (load_effective_address base imm) val D
    n hmem hs1 hs2 hn hA hfit' hDb (hsplice base D val hal') hltA hst hst' hpanic
  refine ⟨t, hex, ?_, ?_, hmemT⟩
  · rw [systemProject_of_store js gp hgp hproj, hlink]
    exact hst'.1
  · intro a ha
    rw [hgp]
    simp only [Mmu.ram_byte]
    rw [hst'.2 a, ite_eq_right]
    simp only [JoltISA.RAM_START_ADDRESS, RAM_START_ADDRESS] at ha hhi8 hA hfit'
    omega

/-- A doubleword store in the I/O window, from the native `SD` row to Sail's `execute`. -/
private theorem sd_core (rs1 rs2 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemRel js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hpanic : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat / 8 * 8 =
          js.jolt_device.memory_layout.panic.toNat →
        ∀ old new : BitVec 64, (old ≠ 0 ↔ js.jolt_device.panic = true) →
          (∀ k < 8, new.extractLsb' (8 * k) 8 =
            if (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 ≤ k ∧
                k < (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8 + 8 then
              (sourceValue (.xreg rs2) js).extractLsb' (8 * (k -
                (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat % 8)) 8
            else old.extractLsb' (8 * k) 8) →
          new ≠ 0)
    (hsail : ∀ (base val : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      rX_bits rs2 js.sail = .ok val js.sail →
      load_effective_address base imm &&& (7 : BitVec 64) = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS →
      ∃ t : SailState, (execute_STORE imm rs2 rs1 8).run js.sail = .ok RETIRE_SUCCESS t ∧
        SailStore js.sail t (load_effective_address base imm) 8 val)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.STORE (imm, rs2, rs1, 8)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  generalize sourceValue (.xreg rs1) js = base at hr1 hhi hpanic
  generalize sourceValue (.xreg rs2) js = val at hr2 hpanic
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]; exact hhi
  obtain ⟨hal, hst⟩ := sd_inv rs1 rs2 imm base val js gp hr1 hr2 hlt hrun
  obtain ⟨hlo40, hhi8⟩ := store_bounds js gp _ _ hmem hlt hst
  rw [← hea] at hlo40 hhi8
  have hal' : load_effective_address base imm &&& (7 : BitVec 64) = 0 := hal
  have hmod := mod_of_and7 _ hal'
  have hproj : Projection.ProjectedVRegsPreserved js gp := by
    obtain ⟨-, hc⟩ := store_effect js gp _ _ hmem hlt hst
    rcases hc with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨t, hex, hst'⟩ := hsail base val hr1 hr2 hal' (by omega) hhi
  obtain ⟨hgp, hmemT⟩ := store_finish js js gp t (load_effective_address base imm) val
    (load_effective_address base imm) val val 8 hmem rfl rfl (by omega) (by omega) (by omega)
    (fun k hk h => by exfalso; apply h; omega)
    (fun k hk => by rw [ite_eq_left (by omega), hmod, Nat.sub_zero]) hlt hst hst' hpanic
  refine ⟨t, hex, ?_, ?_, hmemT⟩
  · rw [systemProject_of_store js gp hgp hproj, hlink]
    exact hst'.1
  · intro a ha
    rw [hgp]
    simp only [Mmu.ram_byte]
    rw [hst'.2 a, ite_eq_right]
    simp only [JoltISA.RAM_START_ADDRESS, RAM_START_ADDRESS] at ha hhi8
    omega
/-! ### The effect of one I/O access -/

/-- One load or store in Sail's I/O window agrees with Jolt's rows.
From Jolt's retiring run of the instruction's rows, Sail's `execute` retires to a state
whose registers are the projection of Jolt's, whose RAM is Jolt's and whose memory
satisfies the memory relation with Jolt's device. -/
private theorem io_core (i : RiscvInstruction) (ast : instruction)
    (hm : RiscvInstruction.Matches i ast) (js gp : SailJoltState)
    (hio : i.IoAccess js) (hflag : i.NoFlagWordLoad js) (hlow : i.NoLowLoad js)
    (hpanic : i.PanicStoreNonzero js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemRel js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hrun : RiscvInstruction.joltRun (honestInstr i js) js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute ast js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemRel gp.jolt_device t := by
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  cases i with
  | LB rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 1) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 1 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .byte true 1 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lbProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lbProgramAuto, hx]; rfl)
      (LB_main.lbProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_b js imm rs1 rd false base hpriv hmprv hpma hhtif hr hlo' hhi' hb no D hD)
      hrun
  | LH rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 2) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 2 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .halfword true 2 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lhProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lhProgramAuto, hx]; rfl)
      (LH_main.lhProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_h js imm rs1 rd false base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LW rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 4) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 4 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .word true 4 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lwProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lwProgramAuto, hx]; rfl)
      (LW_main.lwProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_w js imm rs1 rd false base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LBU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 1) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 1 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lbuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .byte false 1 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lbuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lbuProgramAuto, hx]; rfl)
      (LBU_main.lbuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_b js imm rs1 rd true base hpriv hmprv hpma hhtif hr hlo' hhi' hb no D hD)
      hrun
  | LHU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 2) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 2 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .halfword false 2 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lhuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lhuProgramAuto, hx]; rfl)
      (LHU_main.lhuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_h js imm rs1 rd true base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LWU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 4) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 4 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execProgram (JoltISA.lwuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .word false 4 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lwuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lwuProgramAuto, hx]; rfl)
      (LWU_main.lwuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi h0 hlo
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_w js imm rs1 rd true base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LD rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 8) := hm
    subst hm'
    obtain ⟨hhi, h0, hlo⟩ := load_access _ js rs1 imm 8 (by norm_num) rfl hio hflag hlow
    change (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js = _ at hrun
    exact ld_core rd rs1 imm js gp hinv hlink hmstatus hmem hpma hhtif hhi h0 hlo hrun
  | SB rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 1) := hm
    subst hm'
    obtain ⟨hhi, hpanic'⟩ := store_access _ js rs1 rs2 imm 1 rfl rfl hio hpanic
    change (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .byte 1 (by norm_num)
      (fun x _ => by omega)
      rs1 rs2 imm js gp (SB_main.sbProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi hpanic'
      (fun b D V _ k hk => fusedSplice_byte_b D V b imm k hk)
      (fun base val hr1 hr2 _ hlo hhi' =>
        ⟨_, sail_store_b js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hlo hhi',
          sailStore_byte js.sail _ val⟩) hrun
  | SH rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 2) := hm
    subst hm'
    obtain ⟨hhi, hpanic'⟩ := store_access _ js rs1 rs2 imm 2 rfl rfl hio hpanic
    change (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .halfword 2 (by norm_num)
      (fun x hx => by
        have := mod_of_and1 x (by simpa [LoadFamily.alignmentMask] using hx)
        omega)
      rs1 rs2 imm js gp (SH_main.shProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi hpanic'
      (fun b D V hal k hk => fusedSplice_byte_h D V b imm hal k hk)
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_h js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_halfword js.sail _ val⟩) hrun
  | SW rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 4) := hm
    subst hm'
    obtain ⟨hhi, hpanic'⟩ := store_access _ js rs1 rs2 imm 4 rfl rfl hio hpanic
    change (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .word 4 (by norm_num)
      (fun x hx => by
        have := mod_of_and3 x (by simpa [LoadFamily.alignmentMask] using hx)
        omega)
      rs1 rs2 imm js gp (SW_main.swProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi hpanic'
      (fun b D V hal k hk => fusedSplice_byte_w D V b imm hal k hk)
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_w js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_word js.sail _ val⟩) hrun
  | SD rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 8) := hm
    subst hm'
    obtain ⟨hhi, hpanic'⟩ := store_access _ js rs1 rs2 imm 8 rfl rfl hio hpanic
    change (JoltISA.execInstr (Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js = _ at hrun
    exact sd_core rs1 rs2 imm js gp hinv hlink hmem hhi hpanic'
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_d js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_dword js.sail _ val⟩) hrun
  | _ =>
    obtain ⟨_, _, _, h, _⟩ := hio
    simp [RiscvInstruction.memAccess] at h

/-- A block whose source instruction is a load or store below `RAM_START_ADDRESS`, in the I/O
window, is one Sail `try_step` that preserves the whole-run relation `Related`.

The instruction is LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW or SD. Alignment and the
address range are derived from the block's retiring run `hruns`, not assumed. For example, a
`SW` of `0` to the first word of the output region is one `try_step` that appends four zero
bytes to the device's outputs, and the memory relation after the step includes
`outputs_size` and the panic flag.

Premises, by class:
* invariant: `hsys`, the system invariant on the block's entry state.
* platform: `hio`, the access lies below `RAM_START_ADDRESS`.
* from decoding: `hrow`, `hm`, `hwidth` and `hinputs`, the decode-only facts that Sail
  fetches and decodes the instruction word `encoding` to `ast`.
* documented deviation (`docs/riscv-alignment.md`, section 2): `hflag` (`NoFlagWordLoad`),
  `hlow` (`NoLowLoad`) and `hpanic` (`PanicStoreNonzero`). -/
theorem block_simulates_io (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hsys : SystemInv b.pre) (hio : i.IoAccess b.start)
    (hflag : i.NoFlagWordLoad b.start) (hlow : i.NoLowLoad b.start)
    (hpanic : i.PanicStoreNonzero b.start)
    (ast : instruction) (hm : RiscvInstruction.Matches i ast)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok ast (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  intro s hrel
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  obtain ⟨inc, hinc, hfetch, hdecode⟩ := hinputs s hrel pc m oldInc hnext hregs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  let Gs := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  have hshadow : Shadow ((blockHelper% overlayRows) b.pre.vregs m inc b.start) Gs :=
    (blockHelper% prelude_shadow) b s pc m oldInc inc hp hregs hrel.ram
  have hlift : i.Lifted := by
    obtain ⟨store, width, ea, hacc, _⟩ := hio
    cases i <;> simp_all [RiscvInstruction.memAccess, RiscvInstruction.Lifted]
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes
  have hadvice : blockInstrs b.row Gs = blockInstrs b.row b.start := by
    have he := ((blockHelper% advice_shadow) i _ _ hshadow).trans
      ((blockHelper% advice_overlayRows) i b.pre.vregs m inc b.start)
    simp only [blockInstrs, hrow, he]
  have hpatched := (blockHelper% execProgram_overlayRows) (Program.seq instrs)
    b.pre.vregs m inc b.start b.post RETIRE_SUCCESS hrun
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hpatched] at hsync
  obtain ⟨ghostPost, hghost, hpost, _, _⟩ := hsync.ok_exists
  have hrawG := blockInstrs_run i b.row.address b.row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hhonest : RiscvInstruction.joltRun (honestInstr i Gs) Gs = .ok RETIRE_SUCCESS ghostPost :=
    hrawG.symm.trans hghost
  have hGp : System.systemProject Gs = Step.preludeState s inc pc
      (if b.row.is_compressed then 2 else 4) := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, (blockHelper% ghost_projects) hrel]
  have hlink : System.systemProject Gs = Gs.sail := hGp
  have hinvG : Step.StepInvariant Gs.sail := hrel.inv.preludeState inc pc _
  have hsources : ∀ r, sourceValue (.xreg r) Gs = sourceValue (.xreg r) b.start := fun r =>
    ((blockHelper% sourceValue_shadow) hshadow r).trans
      ((blockHelper% sourceValue_overlayRows) b.pre.vregs m inc b.start r)
  obtain ⟨hio', -, -, -⟩ := access_congr i b.start Gs hsources rfl
  obtain ⟨-, hflag', -, -⟩ := access_congr i b.start Gs hsources rfl
  obtain ⟨-, -, hlow', -⟩ := access_congr i b.start Gs hsources rfl
  obtain ⟨-, -, -, hpanic'⟩ := access_congr i b.start Gs hsources rfl
  have hmemG : MemRel Gs.jolt_device Gs.sail := hrel.memRel.of_mem_eq rfl
  have hpmaG : Gs.sail.regs.get? Register.pma_regions = some platformPma := by
    simp [Gs, Step.preludeJolt, Step.preludeState, Step.setReg, hregs,
      sailRegs, Std.ExtDHashMap.get?_insert]
  have hhtifG : Gs.sail.regs.get? Register.htif_tohost_base = some none := by
    simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg,
      Std.ExtDHashMap.get?_insert] using hrel.htif
  obtain ⟨t, hexec, htregs, htram, htmem⟩ := io_core i ast hm Gs ghostPost
    (hio' hio) (hflag' hflag) (hlow' hlow) (hpanic' hpanic) hlink hinvG hsys.mstatus_bits
    hmemG hpmaG hhtifG hhonest
  have hexec' : execute ast (System.systemProject Gs) = .ok RETIRE_SUCCESS t := by
    rw [hlink]; exact hexec
  have hinvPre : Step.StepInvariant (System.systemProject Gs) := by
    rw [hGp]
    exact hrel.inv.preludeState inc pc _
  have hframe := Step.execProgram_regFrame (Program.seq instrs) Gs
  rw [hghost] at hframe
  change Step.RegFrame Gs ghostPost at hframe
  have hinvPost := hinvPre.systemProject_regFrame hframe
  obtain ⟨next, hnextGhost⟩ := (hinvPost.present Register.nextPC).exists_value
  obtain ⟨hn, hcount, hcountInc⟩ :=
    (blockHelper% projected_reads) b.pre b.post ghostPost m inc hpost
  have hnextPost : b.post.sail.regs.get? Register.nextPC = some next := hn.symm.trans hnextGhost
  have hinvT : Step.StepInvariant t :=
    hinvPost.of_agree (fun r _ => by rw [htregs]) (fun r => by
      obtain ⟨v, hv⟩ := (hinvPost.present r).exists_value
      exact ⟨v, by rw [htregs]; exact hv⟩)
  let s' := (blockHelper% finishState) t next m inc
  have hfinish := (blockHelper% finish_run) t hinvT encoding.bits next m inc
    (by rw [htregs]; exact hnextGhost) (by rw [htregs]; exact hcount)
    (by rw [htregs]; exact hcountInc)
  have hfs : ∀ (s : SailState) (pc m : BitVec 64) (inc : Bool),
      (blockHelper% finishState) s pc m inc =
        if inc then Step.setReg (Step.setReg s .PC pc) .minstret (BitVec.addInt m 1)
        else Step.setReg s .PC pc := fun _ _ _ _ => rfl
  have hft : s'.regs = ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs := by
    cases inc <;> simp [s', hfs, Step.setReg, htregs]
  have hpcS : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have htry := (blockHelper% encoding_try_step) encoding s hrel.inv inc hinc pc hpcS ast
    hfetch hdecode
  have hstep : try_step 0 false s = .ok false s' := by
    rw [htry]
    simp only [← hwidth]
    rw [← hGp]
    unfold Step.executeAndFinish Step.executeFull
    simp only [bind, EStateM.bind, hexec', RETIRE_SUCCESS, pure, EStateM.pure]
    exact hfinish
  refine ⟨false, s', hstep, ?_⟩
  have hmem' : s'.mem = t.mem := (blockHelper% finish_mem) t next m inc
  have hdev : ghostPost.jolt_device = b.post.jolt_device := hpost.device
  have hmemT : MemRel b.post.jolt_device s' := by
    rw [← hdev]
    exact htmem.of_mem_eq hmem'
  have hhtifT : (System.systemProject ghostPost).regs.get? Register.htif_tohost_base =
      some none := by
    rw [Step.systemProject_get?_of_not_overlaid _ (by simp [Step.Overlaid]),
      hframe.keep Register.htif_tohost_base (by simp [Step.JoltWritable])]
    change (Step.preludeState s inc pc _).regs.get? Register.htif_tohost_base = some none
    simpa [Step.preludeState, Step.setReg, Std.ExtDHashMap.get?_insert] using hrel.htif
  exact
    { regs := ⟨next, (if inc then BitVec.addInt m 1 else m), inc, hnextPost,
        hft.trans ((blockHelper% finish_regs) b.pre b.post ghostPost m next inc hpost)⟩
      inv := hinvT.stepFinish_retire encoding.bits hfinish
      htif := by
        change ((blockHelper% finishState) t next m inc).regs.get? Register.htif_tohost_base =
          some none
        rw [show ((blockHelper% finishState) t next m inc).regs =
          ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs from hft]
        cases inc <;> simpa [hfs, Step.setReg,
          Std.ExtDHashMap.get?_insert] using hhtifT
      ram := fun a ha => by
        rw [hmem']
        exact (htram a ha).trans (hpost.ram a ha)
      present := hmemT.present
      io := hmemT.io
      panic := hmemT.panic
      layout := hmemT.layout
      outputs_size := hmemT.outputs_size }

end WholeRun
