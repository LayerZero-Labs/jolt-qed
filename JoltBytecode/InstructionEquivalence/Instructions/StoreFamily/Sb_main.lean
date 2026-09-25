import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.StoreExec
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

/-!
# SB: top-down store-byte equivalence

`SB` is the simplest store-family proof in the new architecture.  There is no
leading alignment assertion, because every byte address is byte-aligned.  The
proof still has the same three visible phases as `SW`:

1. compute `ea`, compute the enclosing dword base, and load that dword;
2. run the Rust-faithful byte splice sequence; and
3. write the spliced dword back with `SD`.

The final bridge removes the implementation detail: writing the enclosing
spliced dword is the same hashmap update as Sail's native one-byte store.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SB_main

/-- The exact dword value that the Rust `SB` inline sequence writes back.

The bytecode loads the enclosing dword and replaces exactly one byte: the byte
selected by the effective address receives the low eight bits of `rs2`. -/
def sbSplicedDword (imm : BitVec 12) (rs1_val rs2_val dword_orig : BitVec 64) :
    BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.byteSplice
    dword_orig
    (Sail.BitVec.extractLsb rs2_val 7 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side reduction for SB.**

This theorem follows the program exactly as written in `JoltISA.sbProgramAuto`.
The statement hides all scratch-register churn and exposes only the semantic
boundary: after the program retires, Sail has performed an `SD` of the spliced
enclosing dword. -/
theorem sbProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.ByteStoreFacts
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
        (sbSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)) := by
  let writeTail : JoltISA.Program :=
    .instr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <| .done RETIRE_SUCCESS
  let spliceTail : JoltISA.Program :=
    .instr (.VirtualWindowMaskB (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0) <|
    .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.VirtualShiftDataB (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    writeTail
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig :=
    loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
      hbytes h_base_aligned.no_ovf
  let dword_new := sbSplicedDword imm rs1_val rs2_val dword_orig
  let finalSail := state_after_dword_store js.sail base dword_new
  rcases StoreProgramBlocks.setupBlock spliceTail imm rs1 js hpriv hmprv rs1_val hrs1
      h_base_aligned hbytes hload_pmp hread_mmio with
    ⟨js_load, hsetup_run, hload_sail, hload_v0, hload_v1, hload_v2⟩
  rcases StoreProgramBlocks.fusedByteSpliceBlock writeTail imm rs2 js js_load
      rs1_val rs2_val dword_orig hsetup hload_sail hload_v0 hload_v1
      (by simpa [dword_orig] using hload_v2) hrs2 with
    ⟨js_splice, hsplice_run, hsplice_sail, hsplice_v1, hsplice_v2⟩
  have hdword_new : js_splice.vregs JoltISA.inlineTmp2 = dword_new := by
    simpa [dword_new, sbSplicedDword] using hsplice_v2
  have hwrite_for_sd :
      vmem_write_addr (Virtaddr base) 8 dword_new
        (Store Data) false false false js_splice.sail =
      .ok (Ok true) finalSail := by
    rw [hsplice_sail]
    simpa [base, dword_new, finalSail] using hwrite_dword
  rcases StoreProgramBlocks.sdWriteBlock (.done RETIRE_SUCCESS)
      js_splice base dword_new finalSail hsplice_v1 hdword_new
      (by simpa [base] using StoreSplice.dword_base_aligns rs1_val imm)
      hwrite_for_sd hread_mmio.ram with
    ⟨js_write, hsd_run, hsail_write, _hvregs_write⟩
  refine ⟨js_write, ?_, ?_⟩
  · calc
      (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
          (JoltISA.execProgram spliceTail).run js_load := by
            simpa [JoltISA.sbProgramAuto, spliceTail, writeTail] using hsetup_run
      _ = (JoltISA.execProgram writeTail).run js_splice := by
            simpa [spliceTail, writeTail] using hsplice_run
      _ = (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_write := by
            simpa [writeTail] using hsd_run
      _ = .ok RETIRE_SUCCESS js_write := by
            rfl
  · simpa [finalSail, base, dword_new] using hsail_write

/-- **Pure bridge for SB.**

The Jolt implementation writes a whole enclosing dword, but the dword was
constructed to differ from the original only at the target byte.  This lemma
turns that dword write into the canonical native byte-store state. -/
theorem sb_spliced_dword_store_eq_byte_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.ByteStoreFacts
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hbytes :
      MemBytesPresentAt s (compute_aligned_dword_base_address rs1_val imm) 8) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (sbSplicedDword imm rs1_val rs2_val
          (loaded_dword_at s (compute_aligned_dword_base_address rs1_val imm)
            hbytes hsetup.no_ovf)) =
      state_after_byte_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 7 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base (by simpa [base] using hbytes)
    (by simpa [base] using hsetup.no_ovf)
  let byte_val := Sail.BitVec.extractLsb rs2_val 7 0
  let dword_new := sbSplicedDword imm rs1_val rs2_val dword_orig
  let off := (ea - base).toNat
  have hspec : StoreSplice.IsByteSplice dword_orig dword_new byte_val off := by
    simpa [dword_new, sbSplicedDword, dword_orig, byte_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.byteSplice_spec dword_orig byte_val off
        hsetup.byte_offset_cases
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
      (state_after_byte_store s ea byte_val).mem := by
    dsimp [StoreSplice.IsByteSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_byte_store_populated
      s ea base byte_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_byte_store s ea byte_val := by
    simpa [state_after_dword_store, state_after_byte_store] using hmem_eq
  simpa [ea, base, dword_new, byte_val] using hstate

/-- **Concrete SB execution on the Jolt side.**

After the pure bridge, the Jolt result is phrased in the same state expression
as the native Sail byte-store theorem. -/
theorem sbProgramAuto_concrete (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.ByteStoreFacts
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
        (sbSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0) := by
  rcases sbProgramAuto_reduces_to_dword_store imm rs2 rs1 js hpriv hmprv rs1_val rs2_val
      hrs1 hrs2 hsetup h_base_aligned hbytes hload_pmp hread_mmio hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sb_spliced_dword_store_eq_byte_store imm js.sail rs1_val rs2_val
    hsetup hbytes

/-- **Sail-side SB reduction.**

Native Sail `execute_STORE ... 1` reduces directly to the same canonical
byte-store state under an explicit successful `vmem_write` assumption. -/
theorem execute_SB_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hwrite_byte :
      vmem_write rs1 (sign_extend (m := 64) imm) 1
        (Sail.BitVec.extractLsb rs2_val 7 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0))) :
    (execute_STORE imm rs2 rs1 1).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  exact execute_STORE_byte_eq_state_after_byte_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm) hrs1_exists hrs2 hwrite_byte

/-- Successful `SB` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem sbProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs2 rs1 : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.sbProgramAuto rs1 rs2 imm) := by
    unfold JoltISA.sbProgramAuto
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      and_true]
    repeat' apply And.intro
    all_goals exact JoltISA.not_protected_of_instructionTmp rfl
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Public SB theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
def sbProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js) =
    (execute_STORE imm rs2 rs1 1).run js.sail

/-- **Public SB theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
theorem sbProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    sbProgramEqSailStatement imm rs2 rs1 js h := by
  unfold sbProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hwin := h.dwordWindowFacts
  have hsetup : StoreSplice.ByteStoreFacts
      (load_effective_address h.rs1_val imm)
      (compute_aligned_dword_base_address h.rs1_val imm) :=
    StoreSplice.byteStoreFacts_of_effective_address h.rs1_val imm
  let dword_orig := loaded_dword_at js.sail base
    (by simpa [base] using hwin.bytes)
    (by simpa [base] using hwin.aligned.no_ovf)
  let dword_new := sbSplicedDword imm h.rs1_val h.rs2_val dword_orig
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
  have hstore_fits : offset + 1 ≤ 8 := by
    have hlt := write_addr_and_seven_lt_eight ea
    omega
  have hstore_access :=
    StoreProgramEqSailAssumptions.storeAccessFacts h 1
      (by simpa [ea, offset] using hstore_fits)
  have hwrite_byte :
      vmem_write rs1 (sign_extend (m := 64) imm) 1
        (Sail.BitVec.extractLsb h.rs2_val 7 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_byte_store js.sail
          (load_effective_address h.rs1_val imm)
          (Sail.BitVec.extractLsb h.rs2_val 7 0)) :=
    vmem_write_byte_store_reduces imm rs1 js.sail h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs1_read (Sail.BitVec.extractLsb h.rs2_val 7 0)
      (by simpa [ea] using hstore_access.store_pmp)
      (by simpa [ea] using hstore_access.write_mmio)
  rcases sbProgramAuto_concrete imm rs2 rs1 js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs2_val
      h.rs1_read h.rs2_read hsetup
      (by simpa [base] using hwin.aligned)
      (by simpa [base] using hwin.bytes)
      (by simpa [base] using hwin.load_pmp)
      (by simpa [base] using hwin.read_mmio)
      (by simpa [base, dword_orig, dword_new] using hwrite_dword) with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_SB_reduces imm rs2 rs1 js h.rs1_val h.rs2_val
    h.rs1_read h.rs2_read hwrite_byte
  have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
    sbProgramAuto_preserves_projected_vregs imm rs2 rs1 hjolt
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

end SB_main

end
