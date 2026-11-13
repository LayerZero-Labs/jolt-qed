import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword
import JoltBytecode.Step.SailReservation
import JoltBytecode.Step.AmoFlags

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

noncomputable section
namespace SystemProofs

/-- Machine-mode address translation is bare when MPRV is zero and the access
is not a shadow-stack access.
For example, both LR and SC use this identity translation. -/
theorem reservation_translate (access : MemoryAccessType mem_payload)
    (hshadow : is_shadow_stack_access access = (pure false : SailM Bool))
    (addr : BitVec 64) (s : SailState)
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s) :
    translateAddr (Virtaddr addr) access s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨m, hms, hzero⟩ := hm.value
  have hrm := readReg_eq_of_get? Register.mstatus s m hms
  have hrp := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine hp.value
  unfold translateAddr SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    ExceptT.lift, MonadLift.monadLift, liftM, monadLift, Functor.map,
    effectivePrivilege, translationMode, hshadow, hrm, hrp, hzero,
    bits_of_virtaddr, BEq.beq]
  rfl

/-- A reserved physical read checks the access's own PMP and PMA permissions,
then reads ordinary RAM.
For example, an LR.W read uses a 4-byte permission check with reservation enabled. -/
theorem reserved_mem_read (access : MemoryAccessType mem_payload)
    (addr : BitVec 64) (width : Nat) (s : SailState) (value : BitVec (8 * width))
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s)
    (ha : is_aligned_paddr (physaddr.Physaddr addr) width = true)
    (hphys : phys_access_check access Privilege.Machine (physaddr.Physaddr addr)
      width true s = .ok none s)
    (hmmio : within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s)
    (hram : LeanRV64D.Functions.read_ram read_kind.Read_RISCV_reserved
      (physaddr.Physaddr addr) width false s = .ok (value, default_meta) s) :
    mem_read access (physaddr.Physaddr addr) width false false true s =
      .ok (Ok value) s := by
  obtain ⟨m, hms, hzero⟩ := hm.value
  have hrm := readReg_eq_of_get? Register.mstatus s m hms
  have hrp := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine hp.value
  unfold mem_read mem_read_priv mem_read_priv_meta checked_mem_read
  simp [bind, EStateM.bind, pure, EStateM.pure, hrm, hrp, effectivePrivilege,
    hzero, ha, LeanRV64D.Functions.not, hphys, hmmio, read_kind_of_flags, hram,
    MemoryOpResult_drop_meta]

/-- An aligned reserved virtual read records its address and width after the
physical read succeeds.
For example, LR.D records a live reservation of width 8. -/
theorem reserved_vmem_read_addr (access : MemoryAccessType mem_payload)
    (addr : BitVec 64) (width : Nat) (s : SailState) (value : BitVec (8 * width))
    (hwidth : 0 < width)
    (hmis : access_causes_misaligned_exception (Virtaddr addr) width true = false)
    (hsplit : split_misaligned (Virtaddr addr) width s = .ok (1, width) s)
    (htrans : translateAddr (Virtaddr addr) access s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s)
    (hmem : mem_read access (physaddr.Physaddr addr) width false false true s =
      .ok (Ok value) s) :
    vmem_read_addr (Virtaddr addr) 0 width access false false true s =
      .ok (Ok value) (Step.setReg (Step.setReg (Step.setReg s
        Register.reservation_valid true) Register.reservation_addr addr)
          Register.reservation_width (width : Int)) := by
  have hw1 : (8 * (width : Int) - 1).toNat - (0 * (width : Int)).toNat + 1 = 8 * width := by omega
  have hw2 : (8 * (width : Int)).toNat = 8 * width := by omega
  unfold vmem_read_addr SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp [hmis, hsplit, bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    misaligned_order, sys_misaligned_order_decreasing, bits_of_virtaddr,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
    htrans, hmem, Step.reservationPolicyLegal.load, hw1, hw2, bits_of_physaddr,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  rw [hw1]
  simp

/-- A conditional physical write checks its exact access permissions and
writes RAM after the alignment guard.
For example, SC.D uses an 8-byte StoreConditional permission check. -/
theorem conditional_mem_write (access : MemoryAccessType mem_payload)
    (addr : BitVec 64) (width : Nat) (data : BitVec (8 * width)) (s t : SailState)
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s)
    (ha : is_aligned_paddr (physaddr.Physaddr addr) width = true)
    (hphys : phys_access_check access Privilege.Machine (physaddr.Physaddr addr)
      width true s = .ok none s)
    (hmmio : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s)
    (hram : LeanRV64D.Functions.write_ram write_kind.Write_RISCV_conditional
      (physaddr.Physaddr addr) width data default_meta s = .ok true t) :
    mem_write_value (physaddr.Physaddr addr) width data access false false true s =
      .ok (Ok true) t := by
  obtain ⟨m, hms, hzero⟩ := hm.value
  have hrm := readReg_eq_of_get? Register.mstatus s m hms
  have hrp := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine hp.value
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    checked_mem_write, bind, EStateM.bind, pure, EStateM.pure,
    hrm, hrp, effectivePrivilege, hzero, ha, LeanRV64D.Functions.not,
    hphys, hmmio, write_kind_of_flags, hram]

/-- An aligned conditional virtual write stores only when its reservation
matches; a failed match still checks physical permissions.
For example, a failed SC returns false and keeps memory unchanged. -/
theorem conditional_vmem_write_addr (access : MemoryAccessType mem_payload)
    (haccess : is_store_conditional access = true)
    (addr : BitVec 64) (width : Nat) (data : BitVec (8 * width))
    (s t : SailState) (success : Bool) (hwidth : 0 < width)
    (hmis : access_causes_misaligned_exception (Virtaddr addr) width true = false)
    (hsplit : split_misaligned (Virtaddr addr) width s = .ok (1, width) s)
    (htrans : translateAddr (Virtaddr addr) access s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s)
    (hmatch : match_reservation addr width s = .ok success s)
    (hp : Assumptions.CurPrivilegeMachine s) (hm : Assumptions.MstatusMprvZero s)
    (hphys : phys_access_check access Privilege.Machine (physaddr.Physaddr addr)
      width true s = .ok none s)
    (hea : mem_write_ea (physaddr.Physaddr addr) width false false true s = .ok (Ok ()) s)
    (hmem : mem_write_value (physaddr.Physaddr addr) width data access false false true s =
      .ok (Ok true) t) :
    vmem_write_addr (Virtaddr addr) width data access false false true s =
      .ok (Ok success) (if success then t else s) := by
  have hw : (8 * (width : Int) - 1).toNat - (0 * (width : Int)).toNat + 1 = 8 * width := by omega
  have hdata : BitVec.setWidth (8 * width)
      (BitVec.extractLsb (8 * (width : Int) - 1).toNat (0 * (width : Int)).toNat data) = data := by
    unfold BitVec.extractLsb BitVec.extractLsb'
    rw [hw]
    simp
  obtain ⟨m, hms, hzero⟩ := hm.value
  have hrm := readReg_eq_of_get? Register.mstatus s m hms
  have hrp := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine hp.value
  unfold vmem_write_addr SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  cases success <;> simp [hmis, hsplit, bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    ExceptT.lift, MonadLift.monadLift, liftM, monadLift, Functor.map,
    misaligned_order, sys_misaligned_order_decreasing, bits_of_virtaddr, bits_of_physaddr,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt, haccess,
    htrans, hmatch, andM, toBool, LeanRV64D.Functions.not, hrm, hrp, effectivePrivilege,
    hzero, hphys, hea,
    Sail.BitVec.extractLsb, hdata, hmem]

/-- Writing a populated doubleword's loaded value back leaves Sail memory
unchanged.
For example, Jolt's failed SC.D may perform this write-back. -/
theorem store_loaded_dword_self (s : SailState) (addr : BitVec 64)
    (hb : MemBytesPresentAt s addr 8) (hn : addr.toNat + 7 < 2 ^ 64) :
    state_after_dword_store s addr (loaded_dword_at s addr hb hn) = s := by
  have hmem : (state_after_dword_store s addr (loaded_dword_at s addr hb hn)).mem = s.mem := by
    apply Std.ExtHashMap.ext_getElem?
    intro a
    change (state_after_dword_store s addr (loaded_dword_at s addr hb hn)).mem.get? a = s.mem.get? a
    by_cases ha : addr.toNat ≤ a ∧ a < addr.toNat + 8
    · let k := a - addr.toNat
      have hk : k < 8 := by dsimp [k]; omega
      have hak : a = addr.toNat + k := by dsimp [k]; omega
      have hva : (addr + BitVec.ofNat 64 k).toNat = a := by
        rw [toNat_add_small_of_no_ovf addr k (by omega)]
        exact hak.symm
      calc
        _ = some (dword_byte (loaded_dword_at s addr hb hn) k) := by
          simpa only [hak] using stored_dword_get?_hit s addr _ k hk
        _ = some (loaded_byte_at s (addr + BitVec.ofNat 64 k)
            (hb.byte_addr hk (by omega))) :=
          congrArg some (dword_byte_loaded_dword_at s addr hb hn k hk)
        _ = s.mem.get? a := by
          have hget := get?_of_loaded_byte_at_eq s (addr + BitVec.ofNat 64 k) _
            (hb.byte_addr hk (by omega)) rfl
          simpa only [hva] using hget.symm

    · exact stored_dword_untouched s addr addr _ a (by omega)
  change { s with mem := (state_after_dword_store s addr (loaded_dword_at s addr hb hn)).mem } = s
  rw [hmem]

/-- A register-based reserved read reduces to its address-based pipeline.
For example, reading rs1 = a with zero offset accesses a. -/
theorem reservation_vmem_read_source (rs1 : regidx) (addr : BitVec 64)
    (width : Nat) (s t : SailState) (result : Result (BitVec (8 * width)) ExecutionResult)
    (hr : rX_bits rs1 s = .ok addr s)
    (hv : vmem_read_addr (Virtaddr addr) (0#64) width (LoadReserved Data) false false true s = .ok result t) :
    vmem_read rs1 (zeros (n := 64)) width (LoadReserved Data) false false true s = .ok result t := by
  unfold vmem_read SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map, ExceptT.run,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map, ext_data_get_addr,
    hr, zeros, hv]

/-- A register-based conditional write reduces to its address-based pipeline.
For example, SC reads its base register before checking the reservation. -/
theorem reservation_vmem_write_source (rs1 : regidx) (addr : BitVec 64)
    (width : Nat) (data : BitVec (8 * width)) (s t : SailState)
    (result : Result Bool ExecutionResult) (hr : rX_bits rs1 s = .ok addr s)
    (hv : vmem_write_addr (Virtaddr addr) width data (StoreConditional Data) false false true s = .ok result t) :
    vmem_write rs1 (zeros (n := 64)) width data (StoreConditional Data) false false true s = .ok result t := by
  unfold vmem_write SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map, ExceptT.run,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map, ext_data_get_addr,
    hr, zeros, hv]

/-- LR's ordering bits preserve its sequential execution.
For example, LR.D with aq set reads the same RAM bytes and reservation. -/
theorem execute_LOADRES_flags (aq rl : Bool) (rs1 : regidx) (width : Nat) (rd : regidx) :
    execute_LOADRES aq rl rs1 width rd = execute_LOADRES false false rs1 width rd := by
  unfold execute_LOADRES vmem_read vmem_read_addr
  simp only [Step.mem_read_amo, Bool.false_and]

/-- SC's ordering bits preserve its sequential execution.
For example, SC.W with rl set has the same reservation-match result. -/
theorem execute_STORECON_flags (aq rl : Bool) (rs2 rs1 : regidx) (width : Nat) (rd : regidx) :
    execute_STORECON aq rl rs2 rs1 width rd = execute_STORECON false false rs2 rs1 width rd := by
  unfold execute_STORECON vmem_write vmem_write_addr
  simp only [Step.mem_write_ea_amo, Step.mem_write_value_amo, Bool.false_and]

end SystemProofs
