import JoltBytecode.InstructionEquivalence.Instructions.System.ReservationRows
import JoltBytecode.InstructionEquivalence.Instructions.System.ReservationMemory

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

noncomputable section
namespace SystemProofs

/-- The RAM window used by an aligned reservation access.
For example, an LR.W or SC.W at offset 4 reads the enclosing doubleword. -/
structure ReservationWindow (double : Bool) (addr : BitVec 64) (js : SailJoltState) : Prop where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail
  align : addr &&& (if double then 7#64 else 3#64) = 0#64
  dword_present : Assumptions.DwordPresent (reservationBase double addr) js.sail
  not_readable_mmio : Assumptions.NotReadableMmioWindow (reservationBase double addr) 8 js.sail
  jolt_ram : Assumptions.JoltRamLoadOk (reservationBase double addr) js

/-- The environment for a naturally aligned LR in Jolt RAM.
The physical check includes Sail's PMP, PMA and reservability requirements.
For example, LR.W at an address ending in 4 needs its enclosing doubleword populated. -/
structure ReservationReadEqAssumptions (double : Bool) (rs1 : regidx)
    (js : SailJoltState) : Type extends UnarySourceReadWithLinkedCSRs rs1 js,
      ReservationWindow double rs1_val js where
  reserved_access : phys_access_check (LoadReserved Data) Privilege.Machine
    (physaddr.Physaddr rs1_val) (if double then 8 else 4) true js.sail = .ok none js.sail

/-- Recover overlay agreement from an LR environment.
For example, the source read remains valid in the projected state. -/
theorem ReservationReadEqAssumptions.linkedCSRs {double : Bool} {rs1 : regidx}
    {js : SailJoltState} (h : ReservationReadEqAssumptions double rs1 js) : LinkedCSRs js :=
  h.toUnarySourceReadWithLinkedCSRs.linkedCSRs

/-- The selected read fits in the enclosing Jolt doubleword.
For example, a word access at offset 4 occupies its final four bytes. -/
theorem reservation_subaccess (double : Bool) (addr : BitVec 64)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64) :
    ∃ offset : Nat, offset + (if double then 8 else 4) ≤ 8 ∧
      reservationBase double addr + BitVec.ofNat 64 offset = addr := by
  cases double with
  | true => exact ⟨0, by decide, by simp [reservationBase]⟩
  | false =>
      refine ⟨(addr &&& (7 : BitVec 64)).toNat, ?_, addr_split_aligned_offset addr⟩
      rcases write_word_offset_cases addr ha with h | h
      · change (addr &&& (7 : BitVec 64)).toNat + 4 ≤ 8; rw [h]; decide
      · change (addr &&& (7 : BitVec 64)).toNat + 4 ≤ 8; rw [h]

/-- The ordinary and reserved virtual misalignment guards agree on this platform.
For example, both guards reject a word address ending in 2. -/
theorem reservation_misalignment (addr : BitVec 64) (width : Nat) :
    access_causes_misaligned_exception (Virtaddr addr) width true =
      access_causes_misaligned_exception (Virtaddr addr) width false := by
  simp [access_causes_misaligned_exception, plat_enable_misaligned_access,
    LeanRV64D.Functions.not]

/-- The reserved physical read returns the same signed value as Jolt's floor read.
For example, LR.W at offset 4 sign-extends the upper half of its doubleword. -/
theorem reservation_read_value (double : Bool) (addr : BitVec 64) (s : SailState)
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hb : MemBytesPresentAt s (reservationBase double addr) 8)
    (hmmio : Assumptions.NotReadableMmio addr (if double then 8 else 4) s)
    (hphys : phys_access_check (LoadReserved Data) Privilege.Machine
      (physaddr.Physaddr addr) (if double then 8 else 4) true s = .ok none s) :
    ∃ value : BitVec (8 * (if double then 8 else 4)),
      mem_read (LoadReserved Data) (physaddr.Physaddr addr) (if double then 8 else 4)
        false false true s = .ok (Ok value) s ∧
      sign_extend (m := 64) value =
        (if double then JoltISA.Mmu.ram_doubleword s.mem addr.toNat else
          AtomicFamily.amoWordLaneOld addr (JoltISA.Mmu.ram_doubleword s.mem (amoWordBase addr).toNat)) := by
  cases double with
  | true =>
      have hn := aligned_addr_no_ovf_of_align addr ha
      let value := loaded_dword_at s addr hb hn
      refine ⟨value, reserved_mem_read _ addr 8 s value hp hm
        (AtomicFamily.amo_dword_is_aligned_paddr_true addr ha) hphys hmmio.sail
        (AtomicFamily.amo_dword_read_ram_reserved_eq_loaded_dword addr s hb hn), ?_⟩
      rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at s addr hb hn]
      simp [sign_extend, Sail.BitVec.signExtend, value]
  | false =>
      have hn := AtomicFamily.amo_word_base_no_ovf addr
      obtain ⟨offset, hfits, heq⟩ := reservation_subaccess false addr ha
      change offset + 4 ≤ 8 at hfits
      have hb' : MemBytesPresentAt s addr 4 := by
        rw [← heq]
        exact memBytesPresentAt_subaccess hb hfits (by change (amoWordBase addr).toNat + offset < 2 ^ 64; omega)
      have hna := AtomicFamily.amo_word_aligned_no_ovf addr hn ha
      let value := loaded_word_at s addr hb' hna
      refine ⟨value, reserved_mem_read _ addr 4 s value hp hm
        (AtomicFamily.amo_word_is_aligned_paddr_true addr ha) hphys hmmio.sail
        (AtomicFamily.amo_word_read_ram_reserved_eq_loaded_word addr s hb' hna), ?_⟩
      rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at s (amoWordBase addr) hb hn,
        AtomicFamily.amo_word_lane_old_eq addr _ ha]
      congr 1
      exact loaded_word_in_dword s addr ha hb hn hb' hna

/-- LR's Jolt program and Sail executor have the same projected effect.
Natural alignment is an explicit environment field because a misaligned LR is
outside the successful Jolt-step handoff.
For example, LR.D records an eight-byte reservation and writes its loaded data. -/
theorem lrRows_eq_execute (double : Bool) (aq rl : Bool) (rd rs1 : regidx)
    (js : SailJoltState) (h : ReservationReadEqAssumptions double rs1 js) :
    System.systemProjectResult (JoltISA.execProgram (lrRows double rd rs1 (regidx.Regidx 0)) js) =
      execute_LOADRES aq rl rs1 (if double then 8 else 4) rd (System.systemProject js) := by
  have hp := Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  obtain ⟨offset, hfits, heq⟩ := reservation_subaccess double h.rs1_val h.align
  have hmmio : Assumptions.NotReadableMmio h.rs1_val (if double then 8 else 4) js.sail := by
    rw [← heq]
    exact h.not_readable_mmio.subaccess (by cases double <;> decide) hfits
  have hbase : Assumptions.NotReadableMmio (reservationBase double h.rs1_val) 8 js.sail := by
    simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide) (by decide)
  have ha0 : h.rs1_val ≠ 0#64 := by
    intro hz
    have hr := hmmio.ram
    simp [hz, JoltISA.RAM_START_ADDRESS] at hr
  obtain ⟨value, hmem, hvalue⟩ := reservation_read_value double h.rs1_val js.sail
    h.cur_privilege h.mstatus_mprv h.align
    (Assumptions.DwordPresent.memBytesPresentAt h.dword_present) hmmio h.reserved_access
  have hmis : access_causes_misaligned_exception (Virtaddr h.rs1_val)
      (if double then 8 else 4) true = false := by
    rw [reservation_misalignment]
    cases double
    · exact access_misaligned_4_aligned_false _ h.align
    · exact access_misaligned_8_aligned_false _ h.align
  have hsplit : split_misaligned (Virtaddr h.rs1_val) (if double then 8 else 4) js.sail =
      .ok (1, ((if double then 8 else 4 : Nat) : Int)) js.sail := by
    cases double
    · exact congrFun (split_misaligned_aligned_4 _ h.align) js.sail
    · exact congrFun (split_misaligned_aligned_8 _ h.align) js.sail
  have hread := reserved_vmem_read_addr (LoadReserved Data) h.rs1_val _ js.sail value
    (by cases double <;> decide) hmis hsplit
    (reservation_translate _ rfl _ _ h.cur_privilege h.mstatus_mprv) hmem
  have hsource := reservation_vmem_read_source rs1 h.rs1_val _ js.sail _ _ h.rs1_read hread
  rw [lrRows_spec double rd rs1 (regidx.Regidx 0) js h.rs1_val h.rs1_read h.align
    hmmio.ram hbase.ram (JoltISA.Mmu.effective_address_ok_of_load hbase.ram h.jolt_ram),
    systemProject_withReservation, hp, execute_LOADRES_flags]
  have hwidth : ((if double then 8 else 4 : Nat) ≤b LeanRV64D.Functions.xlen_bytes) = true := by
    cases double <;> decide
  have hres : System.reservationWidth h.rs1_val (if double then h.rs1_val else 0#64) =
      ((if double then 8 else 4 : Nat) : Int) := by
    cases double <;> simp [System.reservationWidth, ha0, Ne.symm ha0]
  have hvalid : (h.rs1_val != 0#64) = true := bne_iff_ne.mpr ha0
  simp [execute_LOADRES, LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    hwidth, hsource, bind, EStateM.bind, pure, EStateM.pure,
    wX_bits_stateAfterWrite, hres, hvalid, hvalue]

end SystemProofs
