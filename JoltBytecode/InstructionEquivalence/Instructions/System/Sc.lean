import JoltBytecode.InstructionEquivalence.Instructions.System.ScWord
import JoltBytecode.InstructionEquivalence.Instructions.System.ReservationStore

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

noncomputable section
namespace SystemProofs

/-- The environment for an aligned SC, including Jolt's legal initial reservation pair.
The physical check includes Sail's conditional-store PMP and PMA permissions.
For example, a word reservation has v33 = 0, and a doubleword reservation has v33 = v32. -/
structure ReservationStoreEqAssumptions (double : Bool) (rs2 rs1 : regidx)
    (js : SailJoltState) : Type extends BinarySourceReadWithLinkedCSRs rs2 rs1 js,
      ReservationWindow double rs1_val js where
  not_writable_mmio : Assumptions.NotWritableMmioWindow (reservationBase double rs1_val) 8 js.sail
  jolt_ram_store : Assumptions.JoltRamStoreOk (reservationBase double rs1_val) js
  conditional_access : phys_access_check (StoreConditional Data) Privilege.Machine
    (physaddr.Physaddr rs1_val) (if double then 8 else 4) true js.sail = .ok none js.sail
  reservation_pair : js.vregs 33#7 = 0#64 ∨ js.vregs 33#7 = js.vregs 32#7

/-- Recover the initial CSR and reservation overlay agreement for SC.
For example, Sail's match operation sees the reservation encoded in v32/v33. -/
theorem ReservationStoreEqAssumptions.linkedCSRs {double : Bool} {rs2 rs1 : regidx}
    {js : SailJoltState} (h : ReservationStoreEqAssumptions double rs2 rs1 js) : LinkedCSRs js :=
  h.toBinarySourceReadWithLinkedCSRs.linkedCSRs

/-- Select the existing generated SC program by width.
For example, `double = false` selects SC.W. -/
def scRows (double : Bool) (rd rs1 rs2 : regidx) : JoltISA.Program :=
  if double then JoltISA.scdProgramAuto rd rs1 rs2 else JoltISA.scwProgramAuto rd rs1 rs2

/-- SC compares its address with the matching reservation register.
For example, SC.D compares with v33. -/
def scSuccess (double : Bool) (js : SailJoltState) (addr : BitVec 64) : Bool :=
  addr == js.vregs (if double then 33#7 else 32#7)

/-- The canonical Sail memory effect of a successful SC.
For example, SC.W writes only the low 32 source bits. -/
def reservationStore (double : Bool) (s : SailState) (addr src : BitVec 64) : SailState :=
  if double then state_after_dword_store s addr src
  else state_after_word_store s addr (Sail.BitVec.extractLsb src 31 0)

/-- The source bits passed to Sail's conditional memory write.
For example, a word SC extracts bits 31 through zero. -/
def reservationStoreData (double : Bool) (src : BitVec 64) : BitVec (8 * (if double then 8 else 4)) :=
  BitVec.setWidth _ (Sail.BitVec.extractLsb src
    ((((if double then 8 else 4 : Nat) : Int) * 8 - 1).toNat) 0)

/-- The physical SC write returns the canonical memory update.
For example, a successful SC.D writes one full doubleword. -/
theorem reservation_store_value (double : Bool) (addr src : BitVec 64) (s : SailState)
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hmmio : Assumptions.NotWritableMmio addr (if double then 8 else 4) s)
    (hphys : phys_access_check (StoreConditional Data) Privilege.Machine (physaddr.Physaddr addr)
      (if double then 8 else 4) true s = .ok none s) :
    mem_write_value (physaddr.Physaddr addr) (if double then 8 else 4)
      (reservationStoreData double src) (StoreConditional Data) false false true s =
      .ok (Ok true) (reservationStore double s addr src) := by
  cases double with
  | true =>
      have h := conditional_mem_write (StoreConditional Data) addr 8 src s
        (state_after_dword_store s addr src) hp hm
        (AtomicFamily.amo_dword_is_aligned_paddr_true addr ha) hphys hmmio.sail
        (AtomicFamily.amo_dword_write_ram_conditional_eq_state_after_dword_store addr src s)
      simpa [reservationStoreData, reservationStore, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb'] using h
  | false =>
      have h := conditional_mem_write (StoreConditional Data) addr 4
        (Sail.BitVec.extractLsb src 31 0) s (state_after_word_store s addr (Sail.BitVec.extractLsb src 31 0)) hp hm
        (AtomicFamily.amo_word_is_aligned_paddr_true addr ha) hphys hmmio.sail
        (AtomicFamily.amo_word_write_ram_conditional_eq_state_after_word_store addr _ s)
      simpa [reservationStoreData, reservationStore] using h

/-- The actual memory write performed by Jolt's SC rows, including a failed SC's write-back.
For example, SC.W writes its containing doubleword after merging the chosen lane. -/
def joltScStore (double : Bool) (js : SailJoltState) (addr src : BitVec 64) : SailState :=
  let original := JoltISA.Mmu.ram_doubleword js.sail.mem (reservationBase double addr).toNat
  let choice := if scSuccess double js addr then src else
    if double then original else AtomicFamily.amoWordLaneOld addr original
  if double then state_after_dword_store js.sail addr choice
  else state_after_dword_store js.sail (amoWordBase addr) (AtomicFamily.amoWordLaneMerged addr original choice)

/-- Jolt's memory write agrees with storing on success and doing nothing on failure.
Populated bytes make the failed SC's write-back an identity.
For example, a failed SC.W preserves the entire containing doubleword. -/
theorem joltScStore_eq (double : Bool) (js : SailJoltState) (addr src : BitVec 64)
    (ha : addr &&& (if double then 7#64 else 3#64) = 0#64)
    (hb : MemBytesPresentAt js.sail (reservationBase double addr) 8) :
    joltScStore double js addr src =
      if scSuccess double js addr then reservationStore double js.sail addr src else js.sail := by
  cases double with
  | true =>
      change MemBytesPresentAt js.sail addr 8 at hb
      have hn := aligned_addr_no_ovf_of_align addr ha
      cases hsuc : scSuccess true js addr
      · simp only [joltScStore, hsuc, reservationBase, ite_false, ite_true, Bool.false_eq_true]
        change state_after_dword_store js.sail addr (JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat) = js.sail
        rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail addr hb hn]
        exact store_loaded_dword_self js.sail addr hb hn
      · simp only [joltScStore, hsuc, reservationBase, ite_false, ite_true, reservationStore]
  | false =>
      change MemBytesPresentAt js.sail (amoWordBase addr) 8 at hb
      have hn := AtomicFamily.amo_word_base_no_ovf addr
      cases hsuc : scSuccess false js addr
      · simp only [joltScStore, hsuc, reservationBase, ite_false, ite_true, Bool.false_eq_true]
        change state_after_dword_store js.sail (amoWordBase addr)
          (AtomicFamily.amoWordLaneMerged addr _ (AtomicFamily.amoWordLaneOld addr _)) = js.sail
        rw [scWord_merge_old addr _ ha,
          JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail (amoWordBase addr) hb hn]
        exact store_loaded_dword_self js.sail (amoWordBase addr) hb hn
      · simp only [joltScStore, hsuc, reservationBase, ite_false, ite_true, reservationStore]
        change state_after_dword_store js.sail (amoWordBase addr)
          (AtomicFamily.amoWordLaneMerged addr (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat) src) =
            state_after_word_store js.sail addr (Sail.BitVec.extractLsb src 31 0)
        rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail (amoWordBase addr) hb hn]
        exact AtomicFamily.amo_word_lane_store_eq_word_store js.sail addr src hb ha

/-- The architectural reservation-clear update used by Sail's SC executor.
For example, clearing stores false, address zero and width zero. -/
def clearReservation (s : SailState) : SailState :=
  Step.setReg (Step.setReg (Step.setReg s Register.reservation_valid false)
    Register.reservation_addr 0#64) Register.reservation_width 0

/-- Clearing a projected reservation commutes with integer writeback.
For example, SC may clear the reservation before or after writing its status. -/
theorem clearReservation_writeback (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    clearReservation (stateAfterWrite (System.systemProject js) rd value) =
      stateAfterWrite (System.systemProject (withReservation js 0#64 0#64)) rd value := by
  have hclear (state : SailJoltState) :
      System.systemProject (withReservation state 0#64 0#64) = clearReservation (System.systemProject state) := by
    simpa [clearReservation, System.reservationWidth] using systemProject_withReservation state 0#64 0#64
  calc
    _ = clearReservation (System.systemProject {js with sail := stateAfterWrite js.sail rd value}) := by
      rw [Projection.systemProject_stateAfterWrite]
    _ = System.systemProject (withReservation {js with sail := stateAfterWrite js.sail rd value} 0#64 0#64) :=
      (hclear _).symm
    _ = _ := Projection.systemProject_stateAfterWrite (withReservation js 0#64 0#64) rd value

/-- The projected effect of SC's existing generated rows.
For example, both widths clear v32/v33 and write a zero success status. -/
theorem scRows_spec (double : Bool) (rd rs1 rs2 : regidx) (js : SailJoltState)
    (h : ReservationStoreEqAssumptions double rs2 rs1 js) :
    System.systemProjectResult (JoltISA.execProgram (scRows double rd rs1 rs2) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite (System.systemProject (withReservation
        { js with sail := (if scSuccess double js h.rs1_val then
          reservationStore double js.sail h.rs1_val h.rs2_val else js.sail) } 0#64 0#64)) rd
        (if scSuccess double js h.rs1_val then 0#64 else 1#64)) := by
  obtain ⟨offset, hfits, heq⟩ := reservation_subaccess double h.rs1_val h.align
  have hmmio : Assumptions.NotReadableMmio h.rs1_val (if double then 8 else 4) js.sail := by
    rw [← heq]; exact h.not_readable_mmio.subaccess hfits
  have hbase : Assumptions.NotReadableMmio (reservationBase double h.rs1_val) 8 js.sail := by
    simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide)
  have hload := JoltISA.Mmu.effective_address_ok_of_load hbase.ram h.jolt_ram
  have hstore := JoltISA.Mmu.effective_address_ok_of_store hbase.ram h.jolt_ram_store
  have hraw : System.systemProjectResult (JoltISA.execProgram (scRows double rd rs1 rs2) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite (System.systemProject (withReservation
        {js with sail := joltScStore double js h.rs1_val h.rs2_val} 0#64 0#64)) rd
        (if scSuccess double js h.rs1_val then 0#64 else 1#64)) := by
    cases double
    · simpa only [scRows, joltScStore, scSuccess, reservationBase, Bool.false_eq_true, ite_false, ite_true] using
        scwProgram_spec rd rs1 rs2 js h.rs1_val h.rs2_val h.rs1_read h.rs2_read
          h.align hmmio.ram hbase.ram hload h.jolt_ram_store
    · simpa only [scRows, joltScStore, scSuccess, reservationBase, Bool.false_eq_true, ite_false, ite_true] using
        scdProgram_spec rd rs1 rs2 js h.rs1_val h.rs2_val h.rs1_read h.rs2_read h.align hmmio.ram hload hstore
  rw [hraw, joltScStore_eq double js h.rs1_val h.rs2_val h.align
    (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)]

/-- SC's Jolt rows agree with Sail's conditional store and reservation cancellation.
Natural alignment and the initial v32/v33 pair are explicit environment fields.
For example, SC.W can succeed after LR.D at the same address. -/
theorem scRows_eq_execute (double : Bool) (aq rl : Bool) (rd rs1 rs2 : regidx)
    (js : SailJoltState) (h : ReservationStoreEqAssumptions double rs2 rs1 js) :
    System.systemProjectResult (JoltISA.execProgram (scRows double rd rs1 rs2) js) =
      execute_STORECON aq rl rs2 rs1 (if double then 8 else 4) rd (System.systemProject js) := by
  let success := scSuccess double js h.rs1_val
  let post := if success then reservationStore double js.sail h.rs1_val h.rs2_val else js.sail
  have hp := Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  obtain ⟨offset, hfits, heq⟩ := reservation_subaccess double h.rs1_val h.align
  have hmmio : Assumptions.NotWritableMmio h.rs1_val (if double then 8 else 4) js.sail := by
    rw [← heq]; exact h.not_writable_mmio.subaccess hfits
  have ha0 : h.rs1_val ≠ 0#64 := by
    intro hz; have hr := hmmio.ram; simp [hz, JoltISA.RAM_START_ADDRESS] at hr
  have hres : Assumptions.ReservationVRegsMatchSail js := h.linkedCSRs.2.2.2.2.2.2
  have hmatches := Step.match_reservation_jolt js.sail (js.vregs JoltISA.reservationWReg)
    (js.vregs JoltISA.reservationDReg) h.rs1_val hres.valid_eq hres.addr_eq hres.width_eq h.reservation_pair ha0
  have hmatch : match_reservation h.rs1_val (if double then 8 else 4) js.sail = .ok success js.sail := by
    cases double
    · exact hmatches.1
    · exact hmatches.2
  have hmis : access_causes_misaligned_exception (Virtaddr h.rs1_val) (if double then 8 else 4) true = false := by
    rw [reservation_misalignment]
    cases double
    · exact access_misaligned_4_aligned_false _ h.align
    · exact access_misaligned_8_aligned_false _ h.align
  have hsplit : split_misaligned (Virtaddr h.rs1_val) (if double then 8 else 4) js.sail =
      .ok (1, ((if double then 8 else 4 : Nat) : Int)) js.sail := by
    cases double
    · exact congrFun (split_misaligned_aligned_4 _ h.align) js.sail
    · exact congrFun (split_misaligned_aligned_8 _ h.align) js.sail
  have hea : mem_write_ea (physaddr.Physaddr h.rs1_val) (if double then 8 else 4) false false true js.sail =
      .ok (Ok ()) js.sail := by
    cases double
    · exact AtomicFamily.amo_word_mem_write_ea_ok _ _ h.align
    · exact AtomicFamily.amo_dword_mem_write_ea_ok _ _ h.align
  have hvmem := conditional_vmem_write_addr (StoreConditional Data) rfl h.rs1_val _
    (reservationStoreData double h.rs2_val) js.sail _ success (by cases double <;> decide)
    hmis hsplit (reservation_translate _ rfl _ _ h.cur_privilege h.mstatus_mprv)
    hmatch h.cur_privilege h.mstatus_mprv h.conditional_access hea
    (reservation_store_value double h.rs1_val h.rs2_val js.sail
      h.cur_privilege h.mstatus_mprv h.align hmmio h.conditional_access)
  have hsource := reservation_vmem_write_source rs1 h.rs1_val _ _ js.sail post _ h.rs1_read hvmem
  simp only [reservationStoreData] at hsource
  have hpostRegs : post.regs = js.sail.regs := by
    cases hsuc : success <;> cases double <;>
      simp only [post, hsuc, Bool.false_eq_true, ite_false, ite_true, reservationStore] <;> rfl
  have hpostProject := Projection.systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
    js {js with sail := post} hpostRegs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.linkedCSRs
  have hwidth : ((if double then 8 else 4 : Nat) ≤b LeanRV64D.Functions.xlen_bytes) = true := by
    cases double <;> decide
  have hstatus : zero_extend (m := 64) (bool_bit_forwards (!success)) =
      (if success then 0#64 else 1#64) := by cases success <;> rfl
  rw [scRows_spec double rd rs1 rs2 js h, hp, execute_STORECON_flags]
  have hcancel (state : SailState) : cancel_reservation () state = .ok () (clearReservation state) := rfl
  have hclear := clearReservation_writeback {js with sail := post} rd (if success then 0#64 else 1#64)
  rw [hpostProject] at hclear
  simp [execute_STORECON, LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    hwidth, h.rs2_read, reservationStoreData, hsource, bind, EStateM.bind, pure, EStateM.pure,
    wX_bits_stateAfterWrite, hcancel, hstatus, hclear]
  rfl

end SystemProofs
