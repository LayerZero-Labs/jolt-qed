import JoltConstraints.theorems.WholeRun.Relation
import JoltBytecode.HartConfig
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write

/-!
Sail's platform permissions and plain-memory pipeline, independent of Jolt's
former device-byte representation.
Both the ordinary and atomic source simulations use these facts.
For example, a load from the output window reads the same Sail map as a RAM load.
The region-specific checks below describe `WholeRun.platformPma`.
Jolt pin: `ff6fc6568`; the platform regions are `sail-import/rv64d_jolt.json`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false
noncomputable section

namespace WholeRun.PlatformMemory

attribute [local instance] Classical.propDecidable

/-- Sail's wrapping range-subset test is an ordinary natural-number comparison
when the address subtraction and final offset do not wrap.
For example, a four-byte access at base plus eight needs a region of at least twelve bytes. -/
theorem range_subset_nat (addr base size : BitVec 64) (n : Nat)
    (hbase : base.toNat ≤ addr.toNat) (hn : n < 2 ^ 64)
    (hsum : addr.toNat - base.toNat + n < 2 ^ 64) :
    range_subset addr (BitVec.ofNat 64 n) base size =
      decide (addr.toNat - base.toNat + n ≤ size.toNat) := by
  have hsub : (addr - base).toNat = addr.toNat - base.toNat := BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hbase)
  have hadd : addr + BitVec.ofNat 64 n - base =
      (addr - base) + BitVec.ofNat 64 n := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n)]
  have hsize : base + size - base = size := by
    rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _
  have hnat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hsum' : (addr - base).toNat + (BitVec.ofNat 64 n).toNat < 2 ^ 64 := by
    simpa only [hsub, hnat] using hsum
  simp only [range_subset, hadd, hsize, zopz0zIzJ_u, Sail.BitVec.toNatInt,
    BitVec.toNat_add_of_lt hsum', hsub, hnat]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
  by_cases h : addr.toNat - base.toNat + n ≤ size.toNat
  · simp [h, show addr.toNat - base.toNat ≤ size.toNat by omega]
  · simp [h]

/-! ### Alignment -/

/-- A mask `2 ^ k - 1` clearing an address gives divisibility by `2 ^ k`.
For example, `addr &&& 3 = 0` gives `addr.toNat % 4 = 0`. -/
theorem mod_of_and (addr : BitVec 64) (k : Nat) (hk : k < 64)
    (h : addr &&& BitVec.ofNat 64 (2 ^ k - 1) = 0) : addr.toNat % 2 ^ k = 0 := by
  have h' := congrArg BitVec.toNat h
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod] at h'
  simpa using h'

theorem mod_of_and1 (addr : BitVec 64) (h : addr &&& (1 : BitVec 64) = 0) :
    addr.toNat % 2 = 0 := by
  simpa using mod_of_and addr 1 (by norm_num) (by simpa using h)

theorem mod_of_and3 (addr : BitVec 64) (h : addr &&& (3 : BitVec 64) = 0) :
    addr.toNat % 4 = 0 := by
  simpa using mod_of_and addr 2 (by norm_num) (by simpa using h)

theorem mod_of_and7 (addr : BitVec 64) (h : addr &&& (7 : BitVec 64) = 0) :
    addr.toNat % 8 = 0 := by
  simpa using mod_of_and addr 3 (by norm_num) (by simpa using h)

/-- A naturally aligned physical address satisfies Sail's aligned-address test.
For example, address 0x40000002 is aligned for a halfword. -/
theorem aligned_paddr (addr : BitVec 64) (n : Nat) (h : addr.toNat % n = 0) :
    is_aligned_paddr (.Physaddr addr) n = true := by
  unfold is_aligned_paddr Sail.BitVec.toNatInt
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % n)) == (0 : Int)) = true
  rw [h]
  rfl

/-! ### Sail's I/O window is plain memory -/

theorem io_matching (addr : BitVec 64) (n : Nat)
    (hlo : 0x40000000 ≤ addr.toNat) (hn : 0 < n) (hwidth : n ≤ 8)
    (hhi : addr.toNat + n ≤ JoltISA.RAM_START_ADDRESS) :
    matching_pma platformPma (.Physaddr addr) n = some ioRegion := by
  have haddr := addr.isLt
  simp only [JoltISA.RAM_START_ADDRESS] at hhi
  have hio := range_subset_nat addr 0x40000000 0x40000000 n
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
theorem io_checks (s : SailState) (addr : BitVec 64) (n : Nat)
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
theorem not_mmio_io (s : SailState) (addr : BitVec 64) (n : Nat)
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
theorem mem_read_of_plain {n : Nat} (addr : BitVec 64) (s : SailState)
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
theorem mem_write_value_of_plain {n : Nat} (addr : BitVec 64) (data : BitVec (8 * n))
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
theorem byte_of_dword_eq (D : BitVec 64) (k : Nat) :
    byte_of_dword D k = D.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [byte_of_dword, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- A doubleword is its eight bytes, high byte first.
For example, `0x0102030405060708` is the append of bytes `01, 02, ..., 08`. -/
theorem append_bytes (D : BitVec 64) :
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
theorem vmem_read_addr_of_mem_read (addr offset : BitVec 64) (n : Nat) (s : SailState)
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
theorem vmem_read_of_mem_read (imm : BitVec 12) (rs1 : regidx) (n : Nat)
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
theorem execute_LOAD_of_mem_read (imm : BitVec 12) (rs1 rd : regidx) (u : Bool)
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

end WholeRun.PlatformMemory
