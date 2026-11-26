import JoltConstraints.theorems.WholeRun.PlatformMemory
import JoltConstraints.theorems.SharedMemoryExecution

/-!
Plain Sail stores and byte-splice equations for shared memory.
These facts concern the single byte map, including its I/O and RAM regions.
For example, a narrow Jolt store rewrites a containing doubleword while preserving
its other bytes, and Sail writes only the selected lane.
Jolt pin: `ff6fc6568`, `tracer/src/emulator/mmu.rs` (`store_doubleword_raw`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false
noncomputable section

namespace WholeRun.PlatformMemory

attribute [local instance] Classical.propDecidable

/-- Clearing the low three bits of an address rounds it down to a multiple of eight.
For example, `0x1007 &&& -8 = 0x1000`. -/
theorem toNat_and_neg8 (ea : BitVec 64) :
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


/-! ### Sail's store rows -/

open virtaddr MemoryAccessType mem_payload in
/-- A virtual-memory write of `rs1 + imm` that succeeds at the checked address is the write
`vmem_write` performs.
For example, `SB x5, 3(x6)` writes where `vmem_write_addr` writes at `x6 + 3`. -/
theorem vmem_write_of_addr {n : Nat} (imm : BitVec 12) (rs1 : regidx)
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
theorem execute_STORE_dword_of_write (imm : BitVec 12) (rs2 rs1 : regidx)
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
theorem io_write_checks (s : SailState) (addr : BitVec 64) (n : Nat)
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
theorem sail_store_b (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
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
theorem sail_store_h (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
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
theorem sail_store_w (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
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
theorem sail_store_d (js : SailJoltState) (imm : BitVec 12) (rs2 rs1 : regidx)
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


/-! ### The memory Sail's stores leave -/

/-- The memory a store of the low `n` bytes of `V` at `ea` leaves in Sail's state.
Registers are unchanged, bytes `ea` to `ea + n - 1` are the stored bytes and every other
byte is as before. For example, `SH` of `0xBEEF` at `0x40000002` leaves `0xEF` at
`0x40000002`, `0xBE` at `0x40000003` and the rest. -/
def SailStore (s t : SailState) (ea : BitVec 64) (n : Nat) (V : BitVec 64) : Prop :=
  t.regs = s.regs ∧ ∀ a, t.mem.get? a =
    if ea.toNat ≤ a ∧ a < ea.toNat + n then
      some (V.extractLsb' (8 * (a - ea.toNat)) 8)
    else s.mem.get? a

/-- The canonical one-byte Sail update satisfies `SailStore`: registers stay fixed and only the addressed byte changes.
For example, storing 0xABCD writes 0xCD. -/
theorem sailStore_byte (s : SailState) (ea V : BitVec 64) :
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

/-- The canonical two-byte Sail update satisfies `SailStore`.
For example, storing 0xBEEF writes 0xEF followed by 0xBE and retains all other bytes. -/
theorem sailStore_halfword (s : SailState) (ea V : BitVec 64) :
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

/-- The canonical four-byte Sail update satisfies `SailStore`.
For example, storing 0x12345678 writes 0x78 at the lowest address. -/
theorem sailStore_word (s : SailState) (ea V : BitVec 64) :
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

/-- The canonical eight-byte Sail update satisfies `SailStore`.
For example, storing one writes byte one at the base and seven zero bytes. -/
theorem sailStore_dword (s : SailState) (ea V : BitVec 64) :
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

/-- Writing a lane directly agrees byte for byte with rewriting its containing
word after replacing that lane and preserving all other bytes.
For example, SB at word offset three changes only byte three on both sides.
This comparison uses one shared map and applies equally to I/O and RAM. -/
theorem SailStore.agrees_with_doubleword {s t u : SailState}
    (ea address value word old : BitVec 64) (width : Nat)
    (lane : SailStore s t ea width value)
    (whole : SailStore s u address 8 word)
    (base : address.toNat = ea.toNat / 8 * 8)
    (fits : ea.toNat % 8 + width ≤ 8)
    (oldBytes : ∀ k < 8, ¬ (ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + width) →
      old.extractLsb' (8 * k) 8 =
      Mmu.ram_byte s.mem (address.toNat + k))
    (wordBytes : ∀ k < 8, word.extractLsb' (8 * k) 8 =
      if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + width then
        value.extractLsb' (8 * (k - ea.toNat % 8)) 8
      else old.extractLsb' (8 * k) 8) :
    ∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte u.mem a := by
  intro a
  have offset : address.toNat + ea.toNat % 8 = ea.toNat := by omega
  simp only [Mmu.ram_byte, lane.2, whole.2]
  by_cases inWord : address.toNat ≤ a ∧ a < address.toNat + 8
  · rw [ite_eq_left inWord]
    have kBound : a - address.toNat < 8 := by omega
    rw [wordBytes (a - address.toNat) kBound]
    have kAddress : address.toNat + (a - address.toNat) = a := by omega
    by_cases inLane : ea.toNat ≤ a ∧ a < ea.toNat + width
    · rw [ite_eq_left inLane, ite_eq_left (by omega)]
      simp only [Option.getD_some]
      congr 1
      omega
    · rw [ite_eq_right inLane, ite_eq_right (by omega)]
      simp only [Option.getD_some]
      rw [oldBytes (a - address.toNat) kBound (by omega), kAddress]
      rfl
  · rw [ite_eq_right inWord, ite_eq_right (by omega)]

/-- A plain store retains the presence of every already allocated byte.
For example, overwriting an output byte leaves its address allocated. -/
theorem SailStore.preserves_present {s t : SailState} {ea value : BitVec 64}
    {width : Nat} (stored : SailStore s t ea width value)
    (address : Nat) (present : ∃ b, s.mem.get? address = some b) :
    ∃ b, t.mem.get? address = some b := by
  rw [stored.2]
  split
  · exact ⟨_, rfl⟩
  · exact present

/-- A successful Jolt doubleword rewrite and Sail's narrow lane store leave
identical shared bytes when the rewritten word preserves the other lanes.
For example, this compares the actual SB containing-word rewrite with Sail's SB.
The result includes allocation preservation for every already present byte. -/
theorem shared_store_finish (before after : SailJoltState) (t : SailState)
    (address word ea value old : BitVec 64) (width : Nat)
    (stored : Mmu.store_doubleword address word before = .ok (.Ok true) after)
    (lane : SailStore before.sail t ea width value)
    (base : address.toNat = ea.toNat / 8 * 8)
    (fits : ea.toNat % 8 + width ≤ 8)
    (oldBytes : ∀ k < 8, ¬ (ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + width) →
      old.extractLsb' (8 * k) 8 =
      Mmu.ram_byte before.sail.mem (address.toNat + k))
    (wordBytes : ∀ k < 8, word.extractLsb' (8 * k) 8 =
      if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + width then
        value.extractLsb' (8 * (k - ea.toNat % 8)) 8
      else old.extractLsb' (8 * k) 8) :
    after.jolt_device = before.jolt_device ∧ t.regs = after.sail.regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte after.sail.mem a) ∧
      (∀ a, (∃ b, before.sail.mem.get? a = some b) →
        ∃ b, t.mem.get? a = some b) := by
  have shape := JoltConstraints.store_doubleword_shape before after address word (.Ok true) stored
  have sailShape : after.sail = state_after_dword_store before.sail address word := by
    rw [shape]
    exact Mmu.write_ram_doubleword_eq before.sail address word
  refine ⟨by rw [shape], ?_, ?_, fun a present => lane.preserves_present a present⟩
  · rw [sailShape]
    exact lane.1
  · rw [sailShape]
    exact lane.agrees_with_doubleword ea address value word old width
      (sailStore_dword before.sail address word) base fits oldBytes wordBytes

/-! ### The doubleword Jolt stores -/

/-- Each of the first two bytes of a word is retained by taking its low halfword.
For example, byte one of 0x123456 is 0x34 before and after truncation. -/
theorem lowHalf_byte (V : BitVec 64) (j : Nat) (hj : j < 2) :
    (Sail.BitVec.extractLsb V 15 0).extractLsb' (8 * j) 8 = V.extractLsb' (8 * j) 8 := by
  simp only [Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, hi, decide_true,
    Bool.true_and]
  interval_cases j <;> simp <;> omega

/-- Each of the first four bytes of a word is retained by taking its low word.
For example, byte three of 0x12345678 remains 0x12. -/
theorem lowWord_byte (V : BitVec 64) (j : Nat) (hj : j < 4) :
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
theorem fusedSplice_byte_b (D V b : BitVec 64) (imm : BitVec 12) (k : Nat) (hk : k < 8) :
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
theorem fusedSplice_byte_h (D V b : BitVec 64) (imm : BitVec 12)
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
theorem fusedSplice_byte_w (D V b : BitVec 64) (imm : BitVec 12)
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


end WholeRun.PlatformMemory
