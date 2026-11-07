import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.StoreExec
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

open LeanRV64D

/-!
# SH: top-down store-halfword equivalence

`SH` uses the same floor-load and floor-store structure as `SB`, and
replaces two bytes of the enclosing doubleword.  This file
keeps the same proof architecture visible:

* aligned Jolt execution reduces to a dword write of a pure halfword splice;
* the pure bridge identifies that dword write with a native halfword store;
* native Sail execution reduces to the same canonical state; and
* the misaligned floor load stops before reading memory and matches Sail's alignment error.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SH_main

/-- The exact dword value that the Rust `SH` inline sequence writes back.

The bytecode loads the enclosing dword and replaces the selected two-byte lane
with the low sixteen bits of `rs2`. -/
def shSplicedDword (imm : BitVec 12) (rs1_val rs2_val dword_orig : BitVec 64) :
    BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.halfwordSplice
    dword_orig
    (Sail.BitVec.extractLsb rs2_val 15 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side aligned reduction for SH.**

The aligned floor load opens a halfword lane window; the merge rows splice
in the new halfword and write back the containing doubleword. -/
theorem shProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.HalfwordStoreFacts
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_base_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (shSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf))))
    (hstore_pmp :
      Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_mmio :
      Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)) := by
  have hsplice := StoreSplice.fusedHalfwordSplice_eq
    (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
      hbytes h_base_aligned.no_ovf)
    rs2_val (load_effective_address rs1_val imm)
    (compute_aligned_dword_base_address rs1_val imm) hsetup
  obtain ⟨js', hrun, hsail⟩ := StoreProgramBlocks.laneStoreProgram_run .halfword
    imm rs1 rs2 js rs1_val rs2_val hrs1 hrs2 hsetup.halfword_aligned
    h_base_aligned hbytes hread_mmio.ram hjolt_load hjolt_store
  refine ⟨js', hrun, ?_⟩
  rw [hsail]
  exact congrArg (state_after_dword_store js.sail
    (compute_aligned_dword_base_address rs1_val imm)) hsplice

/-- **Pure bridge for SH.**

The Jolt dword write is equivalent to a native halfword store because the
spliced dword changes exactly the two target bytes and preserves all other
bytes in the enclosing dword. -/
theorem sh_spliced_dword_store_eq_halfword_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreFacts
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hbytes :
      MemBytesPresentAt s (compute_aligned_dword_base_address rs1_val imm) 8) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (shSplicedDword imm rs1_val rs2_val
          (loaded_dword_at s (compute_aligned_dword_base_address rs1_val imm)
            hbytes hsetup.no_ovf)) =
      state_after_halfword_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 15 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base (by simpa [base] using hbytes)
    (by simpa [base] using hsetup.no_ovf)
  let halfword_val := Sail.BitVec.extractLsb rs2_val 15 0
  let dword_new := shSplicedDword imm rs1_val rs2_val dword_orig
  let off := (ea - base).toNat
  have hspec : StoreSplice.IsHalfwordSplice dword_orig dword_new halfword_val off := by
    simpa [dword_new, shSplicedDword, dword_orig, halfword_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.halfwordSplice_spec dword_orig halfword_val off
        hsetup.halfword_offset_cases
  have hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none := by
    intro k hk
    rcases hbytes k (by simpa [base] using hk) with ⟨b, hb⟩
    rw [hb]
    simp
  have hload : ∀ k : Nat, (hk : k < 8) →
      dword_byte dword_orig k =
        loaded_byte_at s (base + BitVec.ofNat 64 k)
          (by
            rw [toNat_base_add_small base k hk hsetup.no_ovf]
            exact Option.ne_none_iff_exists'.mp (hpop k hk)) := by
    intro k hk
    simpa [dword_orig] using
      dword_byte_loaded_dword_at s base (by simpa [base] using hbytes)
        (by simpa [base] using hsetup.no_ovf) k hk
  have hmem_eq :
      (state_after_dword_store s base dword_new).mem =
      (state_after_halfword_store s ea halfword_val).mem := by
    dsimp [StoreSplice.IsHalfwordSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_halfword_store_populated
      s ea base halfword_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_halfword_store s ea halfword_val := by
    simpa [state_after_dword_store, state_after_halfword_store] using hmem_eq
  simpa [ea, base, dword_new, halfword_val] using hstate

/-- **Concrete aligned SH execution on the Jolt side.** -/
theorem shProgramAuto_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.HalfwordStoreFacts
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_base_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address rs1_val imm))
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address rs1_val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (shSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf))))
    (hstore_pmp :
      Assumptions.StorePmpOk (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_mmio :
      Assumptions.NotWritableMmio (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hjolt_load : Assumptions.JoltRamLoadOk (compute_aligned_dword_base_address rs1_val imm) js)
    (hjolt_store : Assumptions.JoltRamStoreOk (compute_aligned_dword_base_address rs1_val imm) js) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0) := by
  rcases shProgramAuto_reduces_to_dword_store imm rs2 rs1 js hpriv hmprv rs1_val rs2_val
      hrs1 hrs2 hsetup h_base_aligned hbytes hload_pmp hread_mmio hwrite_dword
      hstore_pmp hwrite_mmio hjolt_load hjolt_store with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sh_spliced_dword_store_eq_halfword_store imm js.sail rs1_val rs2_val
    hsetup hbytes

/-- **Sail-side aligned SH reduction.** -/
theorem execute_SH_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hwrite_halfword :
      vmem_write rs1 (sign_extend (m := 64) imm) 2
        (Sail.BitVec.extractLsb rs2_val 15 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0))) :
    (execute_STORE imm rs2 rs1 2).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  exact execute_STORE_halfword_eq_state_after_halfword_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm) hrs1_exists hrs2 hwrite_halfword

/-- **Jolt-side misaligned SH reduction.**

The leading `VirtualLoadH` returns the Sail store/AMO alignment exception
without running the continuation. -/
theorem shProgramAuto_concrete_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js := by
  exact StoreProgramBlocks.laneStoreProgram_misaligned .halfword imm rs1 rs2 js rs1_val hrs1 hmis

/-- **Sail-side misaligned SH reduction.**

Sail reads `rs2` before it reaches the memory alignment check, so the source
register read remains an explicit hypothesis on the misaligned path. -/
theorem execute_SH_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 1 ≠ 0) :
    (execute_STORE imm rs2 rs1 2).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  let ea := load_effective_address rs1_val imm
  unfold execute_STORE
  simp only [bind, pure]
  unfold LeanRV64D.sail_assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [Sail.ConcurrencyInterfaceV1.PreSail.sail_assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_write
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  have hmis' :
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa [ea] using access_misaligned_2_unaligned_true ea hmis
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrs1, hrs2,
        vmem_write_addr, hmis', ea]
  rfl

/-- Successful `SH` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem shProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs2 rs1 : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.shProgramAuto rs1 rs2 imm) := by
    unfold JoltISA.shProgramAuto
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true]
    repeat' apply And.intro
    all_goals exact JoltISA.not_protected_of_instructionTmp rfl
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main public SH theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
def shProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js) =
    (execute_STORE imm rs2 rs1 2).run js.sail

/-- **Main public SH theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
theorem shProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    shProgramEqSailStatement imm rs2 rs1 js h := by
  unfold shProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hwin := h.dwordWindowFacts
  let dword_orig := loaded_dword_at js.sail base
    (by simpa [base] using hwin.bytes)
    (by simpa [base] using hwin.aligned.no_ovf)
  let dword_new := shSplicedDword imm h.rs1_val h.rs2_val dword_orig
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases halign : ea &&& (1 : BitVec 64) = 0
  · have hsetup : StoreSplice.HalfwordStoreFacts
        (load_effective_address h.rs1_val imm)
        (compute_aligned_dword_base_address h.rs1_val imm) :=
      StoreSplice.halfwordStoreFacts_of_effective_address
        h.rs1_val imm (by simpa [ea] using halign)
    have hwrite_dword :
        vmem_write_addr
          (Virtaddr base) 8 dword_new
          (Store Data) false false false js.sail =
        .ok (Ok true)
          (state_after_dword_store js.sail base dword_new) :=
      vmem_write_addr_dword_store_reduces base dword_new js.sail
        h.cur_privilege h.mstatus_mprv
        (by simpa [base] using hwin.aligned.toAlignedAccess)
        (by simpa [base] using hwin.store_pmp)
        (by simpa [base] using hwin.write_mmio)
    have hstore_fits : offset + 2 ≤ 8 := by
      have hcases := write_halfword_offset_cases ea (by simpa [ea] using halign)
      rcases hcases with h0 | h2 | h4 | h6 <;> omega
    have hstore_access :=
      StoreProgramEqSailAssumptions.storeAccessFacts h 2
        (by simpa [ea, offset] using hstore_fits)
    have hwrite_halfword :
        vmem_write rs1 (sign_extend (m := 64) imm) 2
          (Sail.BitVec.extractLsb h.rs2_val 15 0)
          (Store Data) false false false js.sail =
        .ok (Ok true)
          (state_after_halfword_store js.sail
            (load_effective_address h.rs1_val imm)
            (Sail.BitVec.extractLsb h.rs2_val 15 0)) :=
      vmem_write_halfword_store_reduces imm rs1 js.sail h.cur_privilege h.mstatus_mprv
        h.rs1_val h.rs1_read (Sail.BitVec.extractLsb h.rs2_val 15 0)
        (by simpa [ea] using halign)
        (by simpa [ea] using hstore_access.store_pmp)
        (by simpa [ea] using hstore_access.write_mmio)
    rcases shProgramAuto_concrete_aligned imm rs2 rs1 js h.cur_privilege h.mstatus_mprv
        h.rs1_val h.rs2_val
        h.rs1_read h.rs2_read hsetup
        (by simpa [base] using hwin.aligned)
        (by simpa [base] using hwin.bytes)
        (by simpa [base] using hwin.load_pmp)
        (by simpa [base] using hwin.read_mmio)
        (by simpa [base, dword_orig, dword_new] using hwrite_dword)
        (by simpa [base] using hwin.store_pmp)
        (by simpa [base] using hwin.write_mmio)
        h.jolt_ram h.jolt_ram_store with
      ⟨js', hjolt, hjolt_sail⟩
    have hsail := execute_SH_reduces imm rs2 rs1 js h.rs1_val h.rs2_val
      h.rs1_read h.rs2_read hwrite_halfword
    have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
      shProgramAuto_preserves_projected_vregs imm rs2 rs1 hjolt
    have hregs : js'.sail.regs = js.sail.regs := by
      rw [hjolt_sail]
      rfl
    have h_project_final : System.systemProject js' = js'.sail :=
      Projection.systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
        js js' hregs h_projected_vregs h.linkedCSRs
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    congr 1
    rw [h_project_final, hjolt_sail]
  · have hjolt := shProgramAuto_concrete_misaligned imm rs2 rs1 js h.rs1_val
      h.rs1_read (by simpa [ea] using halign)
    have hsail := execute_SH_misaligned imm rs2 rs1 js h.rs1_val h.rs2_val
      h.rs1_read h.rs2_read (by simpa [ea] using halign)
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    rw [h_project_initial]

end SH_main

end
