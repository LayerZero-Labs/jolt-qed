import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Alignment
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows

/-!
# Derived facts from top-level assumptions

This file proves consequences of the primitive assumptions in
`JoltBytecode.Assumptions`. Nothing here is assumed.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-- Derived facts for the enclosing dword window used by load-family proofs. -/
structure LoadDwordWindowFacts
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) : Prop where
  aligned :
    AlignedDwordAccess (compute_aligned_dword_base_address h.rs1_val imm)
  bytes :
    MemBytesPresentAt js.sail (compute_aligned_dword_base_address h.rs1_val imm) 8
  load_pmp :
    Assumptions.LoadPmpOk
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
  read_mmio :
    Assumptions.NotReadableMmio
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail

def LoadProgramEqSailAssumptions.dwordWindowFacts
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    LoadDwordWindowFacts imm rs1 js h :=
  { aligned := by
      simpa [compute_aligned_dword_base_address, aligned_dword_addr_eq,
        load_effective_address] using
        aligned_dword_addr_is_aligned_dword_access h.rs1_val imm
    bytes := by
      simpa using h.dword_present.memBytesPresentAt
    load_pmp := by
      simpa using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    read_mmio := by
      simpa using h.not_readable_mmio.subaccess
        (offset := 0) (accessWidth := 8) (by omega) }

/-- Derived facts for the enclosing dword window used by store-family proofs.

All fields are consequences of `StoreProgramEqSailAssumptions`; this structure
adds no primitive assumptions. -/
structure StoreDwordWindowFacts
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop where
  aligned :
    AlignedDwordAccess (compute_aligned_dword_base_address h.rs1_val imm)
  bytes :
    MemBytesPresentAt js.sail (compute_aligned_dword_base_address h.rs1_val imm) 8
  load_pmp :
    Assumptions.LoadPmpOk
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
  read_mmio :
    Assumptions.NotReadableMmio
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
  store_pmp :
    Assumptions.StorePmpOk
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
  write_mmio :
    Assumptions.NotWritableMmio
      (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail

def StoreProgramEqSailAssumptions.dwordWindowFacts
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    StoreDwordWindowFacts imm rs2 rs1 js h :=
  { aligned := by
      simpa [compute_aligned_dword_base_address, aligned_dword_addr_eq,
        load_effective_address] using
        aligned_dword_addr_is_aligned_dword_access h.rs1_val imm
    bytes := by
      simpa using h.dword_present.memBytesPresentAt
    load_pmp := by
      simpa using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    read_mmio := by
      simpa using h.not_readable_mmio.subaccess
        (offset := 0) (accessWidth := 8) (by omega)
    store_pmp := by
      simpa using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    write_mmio := by
      simpa using h.not_writable_mmio.subaccess
        (offset := 0) (accessWidth := 8) (by omega) }

/-- Derived write-side facts for a native store access inside the enclosing
dword window. The caller supplies only the arithmetic fact that the access fits
inside that window. -/
structure StoreAccessFacts
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
    (width : Nat) : Prop where
  store_pmp :
    Assumptions.StorePmpOk (load_effective_address h.rs1_val imm) width js.sail
  write_mmio :
    Assumptions.NotWritableMmio (load_effective_address h.rs1_val imm) width js.sail

def StoreProgramEqSailAssumptions.storeAccessFacts
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
    (width : Nat)
    (hfits :
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat +
        width ≤ 8) :
    StoreAccessFacts imm rs2 rs1 js h width := by
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hsplit :
      (ea &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (ea &&& 7).toNat = ea := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hand_neg8_eq_shr_shl :
        ea &&& (-8 : BitVec 64) = (ea >>> 3) <<< 3 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ushiftRight]
      interval_cases i <;> simp
    rw [hand_neg8_eq_shr_shl]
    apply BitVec.eq_of_toNat_eq
    have hbase_toNat : (((ea >>> 3) <<< 3) : BitVec 64).toNat =
        ea.toNat / 8 * 8 := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
      simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      have hlt : ea.toNat / 8 * 8 ≤ ea.toNat := by
        simpa [Nat.mul_comm] using Nat.mul_div_le ea.toNat 8
      exact lt_of_le_of_lt hlt ea.isLt
    have hlow : (ea &&& (7 : BitVec 64)).toNat = ea.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : (7 : BitVec 64).toNat = 7 := by decide
      rw [h7, show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod]
    have hsum_lt :
        (((ea >>> 3) <<< 3) : BitVec 64).toNat +
            (ea &&& (7 : BitVec 64)).toNat < 2 ^ 64 := by
      rw [hbase_toNat, hlow]
      have h := Nat.div_add_mod ea.toNat 8
      omega
    rw [BitVec.toNat_add_of_lt hsum_lt, hbase_toNat, hlow]
    have h := Nat.div_add_mod ea.toNat 8
    omega
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa [base, ea, offset, compute_aligned_dword_base_address] using hsplit
  have hfits' : offset + width ≤ 8 := by
    simpa [ea, offset] using hfits
  refine
    { store_pmp := ?_
      write_mmio := ?_ }
  · have hsub :
        Assumptions.StorePmpOk (base + BitVec.ofNat 64 offset) width js.sail := by
      simpa [base] using h.store_pmp.subaccess
        (offset := offset) (accessWidth := width) hfits'
    simpa [haddr] using hsub
  · have hsub :
        Assumptions.NotWritableMmio (base + BitVec.ofNat 64 offset) width js.sail := by
      simpa [base] using h.not_writable_mmio.subaccess
        (offset := offset) (accessWidth := width) hfits'
    simpa [haddr] using hsub

theorem readReg_eq_of_get? (r : Register) (s : SailState) (rval : RegisterType r)
    (h : s.regs.get? r = some rval) :
    (Sail.readReg r : SailM (RegisterType r)) s = .ok rval s := by
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get, h]

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a normal data-load
    address translation is the bare identity translation. -/
theorem translateAddr_load_data_of_machine_mprv_zero
    (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) :
    translateAddr (Virtaddr addr) (Load Data) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv_zero⟩ := hmprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv_zero,
        bits_of_virtaddr, BEq.beq]
  rfl

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a normal data-store
    address translation is the bare identity translation. -/
theorem translateAddr_store_data_of_machine_mprv_zero
    (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) :
    translateAddr (Virtaddr addr) (Store Data) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv_zero⟩ := hmprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv_zero,
        bits_of_virtaddr, BEq.beq]
  rfl

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a data AMO address
    translation is the bare identity translation. -/
theorem translateAddr_atomic_data_of_machine_mprv_zero
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s) :
    translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv_zero⟩ := hmprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hpriv.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv_zero,
        bits_of_virtaddr, BEq.beq]
  rfl

end
