import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Alignment
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- Inputs: dw (64-bit dword), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a 64-bit dword in little-endian order.
-- Byte 0 is bits 7..0, byte 1 is bits 15..8, etc.
def dword_byte (dw : BitVec 64) (k : Nat) : BitVec 8 :=
  dw.extractLsb' (8 * k) 8

-- Inputs: s (Sail state), base (dword-aligned address), dword_new (64-bit value to write)
-- Assumptions: none
-- Constructs the state after writing 8 bytes of dword_new at base..base+7.
-- Uses s.mem.insert to match Sail's writeByte primitive.
-- `|>` is the pipeline operator: `x |>.f a` means `(x).f a`, chaining 8 inserts.
def state_after_dword_store (s : SailState) (base : BitVec 64) (dword_new : BitVec 64) :
    SailState :=
  { s with mem := s.mem
    |>.insert (base.toNat + 0) (dword_byte dword_new 0)
    |>.insert (base.toNat + 1) (dword_byte dword_new 1)
    |>.insert (base.toNat + 2) (dword_byte dword_new 2)
    |>.insert (base.toNat + 3) (dword_byte dword_new 3)
    |>.insert (base.toNat + 4) (dword_byte dword_new 4)
    |>.insert (base.toNat + 5) (dword_byte dword_new 5)
    |>.insert (base.toNat + 6) (dword_byte dword_new 6)
    |>.insert (base.toNat + 7) (dword_byte dword_new 7) }

/-- Selecting byte `k` from a directly loaded dword recovers the corresponding
direct byte load. -/
theorem dword_byte_loaded_dword_at (s : SailState) (base : BitVec 64)
    (hbytes : MemBytesPresentAt s base 8)
    (h_no_ovf : base.toNat + 7 < 2 ^ 64)
    (k : Nat) (hk : k < 8) :
    dword_byte (loaded_dword_at s base hbytes h_no_ovf) k =
      loaded_byte_at s (base + BitVec.ofNat 64 k)
        (hbytes.byte_addr (k := k) hk (by omega)) := by
  unfold dword_byte loaded_dword_at
  interval_cases k
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi_bool : (i <b 8) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
    simp (disch := omega) only [hi_bool, Bool.true_and, BitVec.getLsbD_extractLsb',
      Nat.reduceMul, Nat.reduceAdd]
    repeat rw [BitVec.getLsbD_append]
    simp (disch := omega) only [if_pos, if_neg, BitVec.add_zero]
    congr 1
    omega

/-- Sail's plain RAM dword write is the canonical direct hashmap update used by
the store/atomic proofs. -/
theorem write_ram_dword_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain (physaddr.Physaddr addr) 8
      data default_meta s =
    .ok true (state_after_dword_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_dword_store,
    dword_byte,
    default_meta,
    __WriteRAM_Meta]
  rfl

/-- A non-MMIO machine-mode dword store through Sail's physical write layer is
the canonical direct hashmap dword update. -/
theorem mem_write_value_dword_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp :
      phys_access_check (Store Data) Privilege.Machine
        (physaddr.Physaddr addr) 8 false s = .ok none s)
    (hmmio :
      within_mmio_writable (physaddr.Physaddr addr) 8 s = .ok false s) :
    mem_write_value (physaddr.Physaddr addr) 8 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_dword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hpriv.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 8 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind
                (within_mmio_writable (physaddr.Physaddr addr) 8)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 8 data
                  else
                    EStateM.bind
                      (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 8 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_dword_store s addr data)
  simp only [EStateM.bind, hpmp]
  simp only [hmmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_dword_eq_state_after_dword_store addr data s]

/-- The effective-address write phase for an ordinary dword store is a pure
success under the non-atomic, non-reservation flags used by Jolt stores. -/
theorem mem_write_ea_plain_dword_ok
    (addr : BitVec 64) (s : SailState) :
    mem_write_ea (physaddr.Physaddr addr) 8 false false false s =
      .ok (Ok ()) s := by
  unfold mem_write_ea
  simp only [Bool.false_or, Bool.false_and]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  unfold write_ram_ea
  change
    (EStateM.bind (EStateM.pure write_kind.Write_plain)
      (fun _ => EStateM.pure (Ok ()))) s =
      .ok (Ok ()) s
  rfl

/-- Collapse Sail's virtual dword store pipeline once translation, effective
address write, and physical value write have been reduced. -/
theorem vmem_write_addr_dword_store_bridge
    (addr data : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) (ha : AlignedAccess addr 8)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 8 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 8 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_dword_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 8 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_machine_mprv_zero addr s hpriv hmprv
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
    ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  have hdata_full :
      BitVec.setWidth 64 (Sail.BitVec.extractLsb data 63 0) = data := by
    unfold Sail.BitVec.extractLsb
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi_bool : (i <b 64) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, Nat.reduceSub,
      Nat.reduceAdd, hi_bool, Bool.true_and, Nat.zero_add]
  have hdata_loop :
      BitVec.setWidth (8 * (((1 : Int), (8 : Int)).2.toNat))
        (Sail.BitVec.extractLsb data
          (8 * ((↑((false, (0 : Nat), true).2.1 : Nat) : Int) + 1) *
              ((1 : Int), (8 : Int)).2 - 1).toNat
          (8 * (↑((false, (0 : Nat), true).2.1 : Nat) : Int) *
              ((1 : Int), (8 : Int)).2).toNat) = data := by
    exact hdata_full
  rw [hdata_loop]
  have hea_int :
      mem_write_ea (physaddr.Physaddr addr) (Int.toNat 8)
        false false false s =
        .ok (Ok ()) s := by
    change mem_write_ea (physaddr.Physaddr addr) 8
      false false false s = .ok (Ok ()) s
    exact hea
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 8) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_dword_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 8 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s addr data)
    exact hwrite
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk,
    bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, hea_int, hwrite_int,
    ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    is_store_conditional, BEq.beq, Bool.false_and, Bool.false_eq_true,
    if_true, pure, EStateM.pure, ExceptT.pure]

/-- Under exact aligned flat-memory evidence, Sail's virtual dword
store pipeline is exactly the canonical hashmap dword update. -/
theorem vmem_write_addr_dword_store_reduces
    (addr data : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) (ha : AlignedAccess addr 8)
    (hpmp :
      phys_access_check (Store Data) Privilege.Machine
        (physaddr.Physaddr addr) 8 false s = .ok none s)
    (hmmio :
      within_mmio_writable (physaddr.Physaddr addr) 8 s = .ok false s) :
    vmem_write_addr (Virtaddr addr) 8 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s addr data) := by
  exact
    vmem_write_addr_dword_store_bridge addr data s hpriv hmprv ha
      (mem_write_ea_plain_dword_ok addr s)
      (mem_write_value_dword_eq_state_after_dword_store
        addr data s hpriv hmprv hpmp hmmio)

-- Inputs: k (a natural number)
-- Assumptions: k < 8
-- A small natural number (< 8) fits in 64 bits, so converting to BitVec
-- and back to Nat is the identity: (ofNat 64 k).toNat = k.
theorem ofNat64_toNat (k : Nat) (hk : k < 8) :
    (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  have hk64 : k < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hk64

-- Inputs: base (64-bit address), k (byte offset)
-- Assumptions: k < 8, base.toNat + 7 < 2^64 (no overflow)
-- Adding a small offset to a 64-bit base does not overflow, so toNat
-- distributes over the addition: (base + k).toNat = base.toNat + k.
theorem toNat_base_add_small (base : BitVec 64) (k : Nat)
    (hk : k < 8) (h_no_ovf : base.toNat + 7 < 2 ^ 64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  have hk_toNat := ofNat64_toNat k hk
  have hsum : base.toNat + (BitVec.ofNat 64 k).toNat < 2 ^ 64 := by
    rw [hk_toNat]
    omega
  have hadd := BitVec.toNat_add_of_lt (x := base) (y := BitVec.ofNat 64 k) hsum
  rw [hk_toNat] at hadd
  exact hadd

-- Inputs: m (hash map), k (inserted key), a (lookup key), v (inserted value)
-- Assumptions: a ≠ k
-- Looking up a different key after an insert gives the same result as before.
theorem extHashMap_get_insert_of_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.ExtHashMap α β) (k a : α) (v : β) (h : a ≠ k) :
    (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases hEq : k == a
  · have : k = a := by simpa using hEq
    exact False.elim (h this.symm)
  · simp [hEq]

-- Inputs: base (start of dword window), a (lookup address), i (byte offset)
-- Assumptions: i < 8, a lies outside the byte window [base, base+7]
-- An address outside the dword window cannot equal any byte address base+i in that window.
theorem outside_dword_window_ne (base a i : Nat) (hi : i < 8)
    (hout : a < base ∨ a ≥ base + 8) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea, base (addresses), dword_new (dword written), a (any address)
-- Assumptions: a is outside base..base+7
-- After writing dword_new at base, all addresses outside the 8-byte range
-- are unchanged in the memory hashmap.
theorem stored_dword_untouched (s : SailState) (ea base : BitVec 64) (dword_new : BitVec 64)
    :
    ∀ a : Nat, (a < base.toNat ∨ a ≥ base.toNat + 8) →
      (state_after_dword_store s base dword_new).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_dword_store
  simp only
  rw [extHashMap_get_insert_of_ne
      (((((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4)).insert (base.toNat + 5) (dword_byte dword_new 5)).insert
          (base.toNat + 6) (dword_byte dword_new 6))
      (base.toNat + 7) a (dword_byte dword_new 7)
      (outside_dword_window_ne base.toNat a 7 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4)).insert (base.toNat + 5) (dword_byte dword_new 5))
      (base.toNat + 6) a (dword_byte dword_new 6)
      (outside_dword_window_ne base.toNat a 6 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4))
      (base.toNat + 5) a (dword_byte dword_new 5)
      (outside_dword_window_ne base.toNat a 5 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3))
      (base.toNat + 4) a (dword_byte dword_new 4)
      (outside_dword_window_ne base.toNat a 4 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2))
      (base.toNat + 3) a (dword_byte dword_new 3)
      (outside_dword_window_ne base.toNat a 3 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1))
      (base.toNat + 2) a (dword_byte dword_new 2)
      (outside_dword_window_ne base.toNat a 2 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (s.mem.insert (base.toNat + 0) (dword_byte dword_new 0))
      (base.toNat + 1) a (dword_byte dword_new 1)
      (outside_dword_window_ne base.toNat a 1 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      s.mem (base.toNat + 0) a (dword_byte dword_new 0)
      (outside_dword_window_ne base.toNat a 0 (by omega) hout)]
-- Inputs: word_val (32-bit value), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a 32-bit word in little-endian order.
-- Byte 0 is bits 7..0, byte 1 is bits 15..8, etc.
def word_byte (word_val : BitVec 32) (k : Nat) : BitVec 8 :=
  word_val.extractLsb' (8 * k) 8

-- Inputs: halfword_val (16-bit value), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a 16-bit halfword in little-endian order.
def halfword_byte (halfword_val : BitVec 16) (k : Nat) : BitVec 8 :=
  halfword_val.extractLsb' (8 * k) 8

-- Inputs: byte_val (8-bit value), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a byte. Only index 0 is meaningful in callers.
def byte_byte (byte_val : BitVec 8) (_k : Nat) : BitVec 8 :=
  byte_val

-- Inputs: s (Sail state), ea (byte address), byte_val (8-bit value to write)
-- Assumptions: none
-- Constructs the state after writing one byte at `ea`.
def state_after_byte_store (s : SailState) (ea : BitVec 64) (byte_val : BitVec 8) :
    SailState :=
  { s with mem := s.mem.insert (ea.toNat + 0) (byte_byte byte_val 0) }

-- Inputs: s (Sail state), ea (halfword address), halfword_val (16-bit value to write)
-- Assumptions: none
-- Constructs the state after writing two little-endian bytes at `ea..ea+1`.
def state_after_halfword_store (s : SailState) (ea : BitVec 64) (halfword_val : BitVec 16) :
    SailState :=
  { s with mem := s.mem
    |>.insert (ea.toNat + 0) (halfword_byte halfword_val 0)
    |>.insert (ea.toNat + 1) (halfword_byte halfword_val 1) }

-- Inputs: s (Sail state), ea (word-aligned address), word_val (32-bit value to write)
-- Assumptions: none
-- Constructs the state after writing 4 bytes of word_val at ea..ea+3.
-- This is what Sail's execute_STORE at width 4 does at the hashmap level.
def state_after_word_store (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    SailState :=
  { s with mem := s.mem
    |>.insert (ea.toNat + 0) (word_byte word_val 0)
    |>.insert (ea.toNat + 1) (word_byte word_val 1)
    |>.insert (ea.toNat + 2) (word_byte word_val 2)
    |>.insert (ea.toNat + 3) (word_byte word_val 3) }

/-- Plain RAM byte writes are the canonical one-byte hashmap update. -/
theorem write_ram_byte_eq_state_after_byte_store
    (addr : BitVec 64) (data : BitVec 8) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 1 data default_meta s =
    .ok true (state_after_byte_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_byte_store,
    byte_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- Plain RAM halfword writes are the canonical two-byte hashmap update. -/
theorem write_ram_halfword_eq_state_after_halfword_store
    (addr : BitVec 64) (data : BitVec 16) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 2 data default_meta s =
    .ok true (state_after_halfword_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_halfword_store,
    halfword_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- Plain RAM word writes are the canonical four-byte hashmap update. -/
theorem write_ram_word_eq_state_after_word_store
    (addr : BitVec 64) (data : BitVec 32) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 4 data default_meta s =
    .ok true (state_after_word_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_word_store,
    word_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- The effective-address write phase for plain stores is a pure success. -/
theorem mem_write_ea_plain_store_ok
    (addr : BitVec 64) (width : Nat) (s : SailState) :
    mem_write_ea (physaddr.Physaddr addr) width false false false s =
      .ok (Ok ()) s := by
  unfold mem_write_ea
  simp only [Bool.false_or, Bool.false_and]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  unfold write_ram_ea
  change
    (EStateM.bind (EStateM.pure write_kind.Write_plain)
      (fun _ => EStateM.pure (Ok ()))) s =
      .ok (Ok ()) s
  rfl

/-- Non-MMIO machine-mode byte writes reduce to the canonical byte-store
state. -/
theorem mem_write_value_byte_eq_state_after_byte_store
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp : Assumptions.StorePmpOk addr 1 s)
    (hmmio : Assumptions.NotWritableMmio addr 1 s) :
    mem_write_value (physaddr.Physaddr addr) 1 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_byte_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 1 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 1)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 1 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 1 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_byte_store s addr data)
  simp only [EStateM.bind, hpmp]
  simp only [hmmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_byte_eq_state_after_byte_store addr data s]

/-- Non-MMIO machine-mode halfword writes reduce to the canonical halfword-store
state. -/
theorem mem_write_value_halfword_eq_state_after_halfword_store
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp : Assumptions.StorePmpOk addr 2 s)
    (hmmio : Assumptions.NotWritableMmio addr 2 s) :
    mem_write_value (physaddr.Physaddr addr) 2 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_halfword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 2 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 2)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 2 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 2 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_halfword_store s addr data)
  simp only [EStateM.bind, hpmp]
  simp only [hmmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_halfword_eq_state_after_halfword_store addr data s]

/-- Non-MMIO machine-mode word writes reduce to the canonical word-store
state. -/
theorem mem_write_value_word_eq_state_after_word_store
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp : Assumptions.StorePmpOk addr 4 s)
    (hmmio : Assumptions.NotWritableMmio addr 4 s) :
    mem_write_value (physaddr.Physaddr addr) 4 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_word_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hmprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 4 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 4)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 4 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 4 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_word_store s addr data)
  simp only [EStateM.bind, hpmp]
  simp only [hmmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_word_eq_state_after_word_store addr data s]

private theorem bitvec_addInt_zero (addr : BitVec 64) :
    Sail.BitVec.addInt addr 0 = addr := by
  unfold Sail.BitVec.addInt
  rw [show BitVec.ofInt 64 0 = (0 : BitVec 64) by decide]
  exact BitVec.add_zero addr

private theorem extractLsb_full_width {w : Nat} (hpos : 0 < w)
    (data : BitVec w) :
    BitVec.extractLsb (w - 1) 0 data = data := by
  ext i
  simp

/-- A halfword-aligned store address is an aligned Sail access address. -/
theorem halfword_store_aligned_access (addr : BitVec 64)
    (halign : addr &&& (1 : BitVec 64) = 0) :
    AlignedAccess addr 2 :=
  { misalign := access_misaligned_2_aligned_false addr halign
    split := split_misaligned_aligned_2 addr halign }

/-- A word-aligned store address is an aligned Sail access address. -/
theorem word_store_aligned_access (addr : BitVec 64)
    (halign : addr &&& (3 : BitVec 64) = 0) :
    AlignedAccess addr 4 :=
  { misalign := access_misaligned_4_aligned_false addr halign
    split := split_misaligned_aligned_4 addr halign }

private theorem byte_store_loop_data_eq (data : BitVec 8) :
    BitVec.setWidth (8 * (((1 : Int), (1 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (1 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (1 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

private theorem halfword_store_loop_data_eq (data : BitVec 16) :
    BitVec.setWidth (8 * (((1 : Int), (2 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (2 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (2 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

private theorem word_store_loop_data_eq (data : BitVec 32) :
    BitVec.setWidth (8 * (((1 : Int), (4 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (4 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (4 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

theorem vmem_write_addr_byte_store_bridge
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) (ha : AlignedAccess addr 1)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 1 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 1 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_byte_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_machine_mprv_zero addr s hpriv hmprv
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [byte_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 1) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_byte_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea, hwrite_int]
  rfl

theorem vmem_write_addr_halfword_store_bridge
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) (ha : AlignedAccess addr 2)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 2 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 2 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_halfword_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_machine_mprv_zero addr s hpriv hmprv
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [halfword_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hea_int :
      mem_write_ea (physaddr.Physaddr addr) (Int.toNat 2)
        false false false s =
        .ok (Ok ()) s := by
    change mem_write_ea (physaddr.Physaddr addr) 2 false false false s =
      .ok (Ok ()) s
    exact hea
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 2) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_halfword_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea_int, hwrite_int]
  rfl

theorem vmem_write_addr_word_store_bridge
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) (ha : AlignedAccess addr 4)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 4 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 4 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_word_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_machine_mprv_zero addr s hpriv hmprv
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [word_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hea_int :
      mem_write_ea (physaddr.Physaddr addr) (Int.toNat 4)
        false false false s =
        .ok (Ok ()) s := by
    change mem_write_ea (physaddr.Physaddr addr) 4 false false false s =
      .ok (Ok ()) s
    exact hea
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 4) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_word_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea_int, hwrite_int]
  rfl

theorem vmem_write_addr_byte_store_reduces
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hpmp : Assumptions.StorePmpOk addr 1 s)
    (hmmio : Assumptions.NotWritableMmio addr 1 s) :
    vmem_write_addr (Virtaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data) :=
  vmem_write_addr_byte_store_bridge addr data s hpriv hmprv
    (aligned_access_1 addr)
    (mem_write_ea_plain_store_ok addr 1 s)
    (mem_write_value_byte_eq_state_after_byte_store addr data s hpriv hmprv hpmp hmmio)

theorem vmem_write_addr_halfword_store_reduces
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (halign : addr &&& (1 : BitVec 64) = 0)
    (hpmp : Assumptions.StorePmpOk addr 2 s)
    (hmmio : Assumptions.NotWritableMmio addr 2 s) :
    vmem_write_addr (Virtaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data) :=
  vmem_write_addr_halfword_store_bridge addr data s hpriv hmprv
    (halfword_store_aligned_access addr halign)
    (mem_write_ea_plain_store_ok addr 2 s)
    (mem_write_value_halfword_eq_state_after_halfword_store
      addr data s hpriv hmprv hpmp hmmio)

theorem vmem_write_addr_word_store_reduces
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hpmp : Assumptions.StorePmpOk addr 4 s)
    (hmmio : Assumptions.NotWritableMmio addr 4 s) :
    vmem_write_addr (Virtaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data) :=
  vmem_write_addr_word_store_bridge addr data s hpriv hmprv
    (word_store_aligned_access addr halign)
    (mem_write_ea_plain_store_ok addr 4 s)
    (mem_write_value_word_eq_state_after_word_store addr data s hpriv hmprv hpmp hmmio)

theorem vmem_write_byte_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 8)
    (hpmp : Assumptions.StorePmpOk (load_effective_address v imm) 1 s)
    (hmmio : Assumptions.NotWritableMmio (load_effective_address v imm) 1 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 1 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_byte_store s (load_effective_address v imm) data) := by
  unfold load_effective_address
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_byte_store_reduces _ data s hpriv hmprv hpmp hmmio]

theorem vmem_write_halfword_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 16)
    (halign : load_effective_address v imm &&& (1 : BitVec 64) = 0)
    (hpmp : Assumptions.StorePmpOk (load_effective_address v imm) 2 s)
    (hmmio : Assumptions.NotWritableMmio (load_effective_address v imm) 2 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 2 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_halfword_store s (load_effective_address v imm) data) := by
  unfold load_effective_address at halign hpmp hmmio ⊢
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_halfword_store_reduces _ data s hpriv hmprv halign hpmp hmmio]

theorem vmem_write_word_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 32)
    (halign : load_effective_address v imm &&& (3 : BitVec 64) = 0)
    (hpmp : Assumptions.StorePmpOk (load_effective_address v imm) 4 s)
    (hmmio : Assumptions.NotWritableMmio (load_effective_address v imm) 4 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 4 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_word_store s (load_effective_address v imm) data) := by
  unfold load_effective_address at halign hpmp hmmio ⊢
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_word_store_reduces _ data s hpriv hmprv halign hpmp hmmio]

-- Inputs: base (start of word window), a (lookup address), i (byte offset)
-- Assumptions: i < 4, a lies outside the byte window [base, base+3]
-- An address outside the word window cannot equal any byte address base+i in that window.
theorem outside_word_window_ne (base a i : Nat) (hi : i < 4)
    (hout : a < base ∨ a ≥ base + 4) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea (word address), word_val (word written), a (any address)
-- Assumptions: a is outside ea..ea+3
-- After writing word_val at ea, all addresses outside the 4-byte range
-- are unchanged in the memory hashmap.
theorem stored_word_untouched (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    ∀ a : Nat, (a < ea.toNat ∨ a ≥ ea.toNat + 4) →
      (state_after_word_store s ea word_val).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_word_store
  simp only
  rw [extHashMap_get_insert_of_ne
      (((s.mem.insert (ea.toNat + 0) (word_byte word_val 0)).insert (ea.toNat + 1)
          (word_byte word_val 1)).insert (ea.toNat + 2) (word_byte word_val 2))
      (ea.toNat + 3) a (word_byte word_val 3)
      (outside_word_window_ne ea.toNat a 3 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((s.mem.insert (ea.toNat + 0) (word_byte word_val 0)).insert (ea.toNat + 1)
          (word_byte word_val 1))
      (ea.toNat + 2) a (word_byte word_val 2)
      (outside_word_window_ne ea.toNat a 2 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (s.mem.insert (ea.toNat + 0) (word_byte word_val 0))
      (ea.toNat + 1) a (word_byte word_val 1)
      (outside_word_window_ne ea.toNat a 1 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      s.mem (ea.toNat + 0) a (word_byte word_val 0)
      (outside_word_window_ne ea.toNat a 0 (by omega) hout)]

-- Inputs: base (start of halfword window), a (lookup address), i (byte offset)
-- Assumptions: i < 2, a lies outside the byte window [base, base+1]
-- An address outside the halfword window cannot equal any byte address base+i.
theorem outside_halfword_window_ne (base a i : Nat) (hi : i < 2)
    (hout : a < base ∨ a ≥ base + 2) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea (halfword address), halfword_val (halfword written),
-- a (any address)
-- Assumptions: a is outside ea..ea+1
-- After writing `halfword_val` at `ea`, outside addresses are unchanged.
theorem stored_halfword_untouched (s : SailState) (ea : BitVec 64)
    (halfword_val : BitVec 16) :
    ∀ a : Nat, (a < ea.toNat ∨ a ≥ ea.toNat + 2) →
      (state_after_halfword_store s ea halfword_val).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_halfword_store
  simp only
  rw [extHashMap_get_insert_of_ne
      (s.mem.insert (ea.toNat + 0) (halfword_byte halfword_val 0))
      (ea.toNat + 1) a (halfword_byte halfword_val 1)
      (outside_halfword_window_ne ea.toNat a 1 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      s.mem (ea.toNat + 0) a (halfword_byte halfword_val 0)
      (outside_halfword_window_ne ea.toNat a 0 (by omega) hout)]

-- Inputs: base (start of byte window), a (lookup address), i (byte offset)
-- Assumptions: i < 1, a lies outside the singleton byte window [base, base]
-- An address outside the byte window cannot equal base+i.
theorem outside_byte_window_ne (base a i : Nat) (hi : i < 1)
    (hout : a < base ∨ a ≥ base + 1) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea (byte address), byte_val (byte written), a (any address)
-- Assumptions: a is not `ea`
-- After writing `byte_val` at `ea`, all other addresses are unchanged.
theorem stored_byte_untouched (s : SailState) (ea : BitVec 64) (byte_val : BitVec 8) :
    ∀ a : Nat, (a < ea.toNat ∨ a ≥ ea.toNat + 1) →
      (state_after_byte_store s ea byte_val).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_byte_store
  rw [extHashMap_get_insert_of_ne
      s.mem (ea.toNat + 0) a (byte_byte byte_val 0)
      (outside_byte_window_ne ea.toNat a 0 (by omega) hout)]

-- Inputs: s (Sail state), ea (word address), word_val (word written), j (byte index)
-- Assumptions: j < 4
-- Reading the byte just written at address ea + j returns the j-th byte of word_val.
theorem stored_word_get?_hit (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    ∀ j : Nat, j < 4 →
      (state_after_word_store s ea word_val).mem.get? (ea.toNat + j) =
      some (word_byte word_val j) := by
  intro j hj
  unfold state_after_word_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases j
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: s (Sail state), ea (halfword address), halfword_val (halfword written),
-- j (byte index)
-- Assumptions: j < 2
-- Reading back address ea+j returns the j-th little-endian halfword byte.
theorem stored_halfword_get?_hit (s : SailState) (ea : BitVec 64)
    (halfword_val : BitVec 16) :
    ∀ j : Nat, j < 2 →
      (state_after_halfword_store s ea halfword_val).mem.get? (ea.toNat + j) =
      some (halfword_byte halfword_val j) := by
  intro j hj
  unfold state_after_halfword_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases j
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: s (Sail state), ea (byte address), byte_val (byte written), j (byte index)
-- Assumptions: j < 1
-- Reading back address ea+j returns the stored byte.
theorem stored_byte_get?_hit (s : SailState) (ea : BitVec 64) (byte_val : BitVec 8) :
    ∀ j : Nat, j < 1 →
      (state_after_byte_store s ea byte_val).mem.get? (ea.toNat + j) =
      some (byte_byte byte_val j) := by
  intro j hj
  unfold state_after_byte_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases j
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: s (Sail state), base (dword address), dword_new (dword written), k (byte index)
-- Assumptions: k < 8
-- Reading the byte just written at address base + k returns the k-th byte of dword_new.
theorem stored_dword_get?_hit (s : SailState) (base : BitVec 64) (dword_new : BitVec 64) :
    ∀ k : Nat, k < 8 →
      (state_after_dword_store s base dword_new).mem.get? (base.toNat + k) =
      some (dword_byte dword_new k) := by
  intro k hk
  unfold state_after_dword_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases k
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: addr (effective address)
-- Assumptions: none
-- Splits a word-aligned address into its dword-aligned base plus the low 3-bit offset.
private theorem write_and_neg8_eq_shr_shl (addr : BitVec 64) :
    addr &&& (-8 : BitVec 64) = (addr >>> 3) <<< 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem write_addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [write_and_neg8_eq_shr_shl]
  apply BitVec.eq_of_toNat_eq
  have hbase : (((addr >>> 3) <<< 3) : BitVec 64).toNat =
      addr.toNat / 8 * 8 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have hlt : addr.toNat / 8 * 8 ≤ addr.toNat := by
      simpa [Nat.mul_comm] using Nat.mul_div_le addr.toNat 8
    exact lt_of_le_of_lt hlt addr.isLt
  have hlow : (addr &&& (7 : BitVec 64)).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    rw [h7, show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have hsum_lt :
      (((addr >>> 3) <<< 3) : BitVec 64).toNat +
          (addr &&& (7 : BitVec 64)).toNat < 2 ^ 64 := by
    rw [hbase, hlow]
    have h := Nat.div_add_mod addr.toNat 8
    omega
  rw [BitVec.toNat_add_of_lt hsum_lt, hbase, hlow]
  have h := Nat.div_add_mod addr.toNat 8
  omega

theorem write_addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

theorem write_halfword_offset_cases (addr : BitVec 64) (halign : addr &&& 1 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 2 ∨
    (addr &&& 7).toNat = 4 ∨ (addr &&& 7).toNat = 6 := by
  have hk_lt : (addr &&& 7).toNat < 8 := write_addr_and_seven_lt_eight addr
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_even_addr : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h1, h0] at h
    rw [show (1 : Nat) = 2^1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_even : (addr &&& 7).toNat % 2 = 0 := by
    rw [hk_mod8]
    omega
  omega

-- Inputs: addr (effective address)
-- Assumptions: addr is word aligned
-- The offset of a word-aligned address within its surrounding dword is either 0 or 4.
theorem write_word_offset_cases (addr : BitVec 64) (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 4 := by
  have hk_lt : (addr &&& 7).toNat < 8 := write_addr_and_seven_lt_eight addr
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_word_addr : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h3, h0] at h
    rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    rw [hk_mod8]
    omega
  omega

-- Inputs: ea, base (addresses)
-- The word offset within the dword is either 0 or 4.

-- Inputs: ea, base (addresses)
-- The effective address is the dword base plus the 0-or-4 word offset, at the Nat level.

-- Inputs: ea, base (addresses), j (word-byte offset)
-- Assumptions: j < 4
-- The target dword index base + ((ea-base)+j) is the same address as ea + j.

-- Inputs: ea, base (addresses), k (dword-byte offset)
-- Assumptions: k < 8
-- Every dword byte index is either in the target 4-byte subwindow or outside it.

-- Inputs: s (Sail state), addr (memory address), b (byte value)
-- Assumptions:
--   - the memory entry at addr is populated
--   - loaded_byte_at returns b at addr
-- If loaded_byte_at reads b from a populated address, then the underlying get?
-- lookup must be exactly some b.
theorem get?_of_loaded_byte_at_eq
    (s : SailState) (addr : BitVec 64) (b : BitVec 8)
    (hpresent : MemBytePresentAt s addr.toNat)
    (hload : loaded_byte_at s addr hpresent = b) :
    s.mem.get? addr.toNat = some b := by
  rcases hpresent with ⟨v, hv⟩
  have hv? : s.mem[addr.toNat]? = some v := by
    simpa [Std.ExtHashMap.get?_eq_getElem?] using hv
  rcases getElem_of_getElem? hv? with ⟨hmem, hvget⟩
  have hloaded_v : loaded_byte_at s addr ⟨v, hv⟩ = v := by
    unfold loaded_byte_at loaded_byte_at_nat
    simpa [hv] using hvget
  have hvb : v = b := by
    rw [← hloaded_v]
    exact hload
  simpa [hvb] using hv

-- Inputs: ea, base (addresses), k (dword-window offset)
-- Assumptions:
--   - k lies outside the 4-byte target subwindow inside the dword
-- The corresponding absolute address base+k lies outside the word-write window ea..ea+3.

-- Inputs: ea, base (addresses), a (lookup address)
-- Assumptions: a is outside base..base+7
-- If an address lies outside the whole dword window, it also lies outside
-- the 4-byte word window ea..ea+3 inside that dword.

-- Inputs: m1, m2 (memory hash maps)
-- Assumptions: pointwise equality of get? lookups at every key
-- Two ExtHashMaps are equal if they return the same value at every key.
theorem extHashMap_eq_of_get?_eq
    {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ a : Nat, m1.get? a = m2.get? a) :
    m1 = m2 := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  simpa [Std.ExtHashMap.get?_eq_getElem?] using h a

-- Inputs: base (start of dword window), a (address in the window)
-- Assumptions: base ≤ a, a < base + 8
-- Any address inside the dword window can be written uniquely as base + k for some k < 8.
theorem eq_base_add_of_mem_dword_window
    (base a : Nat)
    (hlo : base ≤ a) (hhi : a < base + 8) :
    ∃ k : Nat, k < 8 ∧ a = base + k := by
  refine ⟨a - base, ?_, ?_⟩
  · omega
  · omega

-- Inputs: base (start of dword window), m1, m2, orig (memory hash maps)
-- Assumptions:
--   - m1 agrees with orig outside base..base+7
--   - m2 agrees with orig outside base..base+7
--   - m1 and m2 agree on the 8 keys inside base..base+7
-- To prove equality of the two maps, it is enough to compare them on the 8-byte
-- dword window and show both revert to orig outside that window.
theorem mem_eq_of_eq_on_dword_window
    (base : Nat)
    (m1 m2 orig : Std.ExtHashMap Nat (BitVec 8))
    (h1_out : ∀ a : Nat, a < base ∨ a ≥ base + 8 -> m1.get? a = orig.get? a)
    (h2_out : ∀ a : Nat, a < base ∨ a ≥ base + 8 -> m2.get? a = orig.get? a)
    (h_in : ∀ k : Nat, k < 8 -> m1.get? (base + k) = m2.get? (base + k)) :
    m1 = m2 := by
  apply extHashMap_eq_of_get?_eq
  intro a
  by_cases hlo : a < base
  · rw [h1_out a (Or.inl hlo), h2_out a (Or.inl hlo)]
  · by_cases hhi : a ≥ base + 8
    · rw [h1_out a (Or.inr hhi), h2_out a (Or.inr hhi)]
    · have hbase_le : base ≤ a := by omega
      have hbase_hi : a < base + 8 := by omega
      obtain ⟨k, hk, rfl⟩ := eq_base_add_of_mem_dword_window base a hbase_le hbase_hi
      exact h_in k hk

-- Inputs:
--   s          : Sail state before the store
--   ea         : effective address (word-aligned, where the 32-bit word goes)
--   base       : dword-aligned base address (ea rounded down to 8)
--   word_val   : the 32-bit value being stored
--   dword_orig : the 64-bit dword loaded from memory at base (before the store)
--   dword_new  : the spliced 64-bit dword (dword_orig with word_val inserted)
--
-- Assumptions:
--   hword_aligned : ea is word-aligned
--   hbase      : base is `ea &&& -8`
--   h_no_ovf   : base + 7 does not overflow
--   hpop       : the 8 dword bytes at base..base+7 are populated in s.mem
--   hload      : dword_orig was loaded from memory at base
--   hsplice    : dword_new has word_val at the ea offset and dword_orig elsewhere
--
-- Statement:
--   Under populatedness of the dword window, writing dword_new at base produces
--   exactly the same .mem hashmap as writing word_val at ea.
