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
# SW: top-down store-word equivalence

This file is deliberately organized like the program-level load proofs.
`JoltISA.swProgramAuto` is the Rust-faithful bytecode expansion; the proof reduces
that program in phases, reduces Sail's native `execute_STORE`, and then bridges
the two final memory states with a pure splice lemma.

The current goal is architectural clarity before proof grinding.  The hard
phase facts are named explicitly, so the structure of the finished proof stays
visible:

* `swProgram_reduces_to_dword_store` is the monadic Jolt side:
  assertion/setup, dword load, SW splice logic, and final `SD`.
* `sw_spliced_dword_store_eq_word_store` is the pure memory bridge:
  writing the spliced enclosing dword has the same memory effect as a native
  four-byte word store.
* `execute_SW_reduces` is the Sail side:
  native `execute_STORE ... 4` reduces to the same word-store state.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SW_main

/-- The exact dword value that the Rust `SW` inline sequence writes back.

The Jolt program first loads the enclosing dword, then replaces exactly the
four bytes selected by the effective address with the low word of `rs2`.
Keeping this expression named makes the theorem statements read top-down
instead of repeating the full splice expression everywhere. -/
def swSplicedDword (imm : BitVec 12) (rs1_val rs2_val dword_orig : BitVec 64) :
    BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.wordSplice
    dword_orig
    (Sail.BitVec.extractLsb rs2_val 31 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side reduction for SW.**

This is the store analogue of the load-side concrete program lemmas.  It says
that the structured Jolt-ISA program follows the Rust bytecode sequence and
ends by writing the spliced enclosing dword with `SD`.

Intended proof phases:
1. `VirtualAssertWordAlignment; ADDI; ANDI; LD` establishes `ea`, `base`, and original
   dword.
2. The SW mask/value logic computes `swSplicedDword`.
3. `SD v1, v2, 0` writes that dword through Sail's store pipeline. -/
theorem swProgramAuto_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreFacts
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
        (swSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)) := by
  let writeTail : JoltISA.Program :=
    .instr (JoltISA.Encoded.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <| .done RETIRE_SUCCESS
  let spliceTail : JoltISA.Program :=
    .instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0) <|
    .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.VirtualShiftDataW (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    writeTail
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig :=
    loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
      hbytes h_base_aligned.no_ovf
  let dword_new := swSplicedDword imm rs1_val rs2_val dword_orig
  let finalSail := state_after_dword_store js.sail base dword_new
  rcases StoreProgramBlocks.assertWordSetupBlockAligned spliceTail
      imm rs1 js hpriv hmprv rs1_val hrs1 hsetup.word_aligned
      h_base_aligned hbytes hload_pmp hread_mmio with
    ⟨js_load, hsetup_run, hload_sail, hload_v0, hload_v1, hload_v2⟩
  rcases StoreProgramBlocks.fusedWordSpliceBlock writeTail imm rs2 js js_load
      rs1_val rs2_val dword_orig hsetup hload_sail hload_v0 hload_v1
      (by simpa [dword_orig] using hload_v2) hrs2 with
    ⟨js_splice, hsplice_run, hsplice_sail, hsplice_v1, hsplice_v2⟩
  have hdword_new : js_splice.vregs JoltISA.inlineTmp2 = dword_new := by
    simpa [dword_new, swSplicedDword] using hsplice_v2
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
      (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
          (JoltISA.execProgram spliceTail).run js_load := by
            simpa [JoltISA.swProgramAuto, spliceTail, writeTail] using hsetup_run
      _ = (JoltISA.execProgram writeTail).run js_splice := by
            simpa [spliceTail, writeTail] using hsplice_run
      _ = (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_write := by
            simpa [writeTail] using hsd_run
      _ = .ok RETIRE_SUCCESS js_write := by
            rfl
  · simpa [finalSail, base, dword_new] using hsail_write

/-- **Pure bridge for SW.**

Once the Jolt side has reduced to an enclosing-dword write, this lemma removes
the Jolt implementation detail.  It states that the specific dword produced by
the SW splice has exactly the same memory effect as Sail's native four-byte
store at the effective address. -/
theorem sw_spliced_dword_store_eq_word_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hbytes :
      MemBytesPresentAt s (compute_aligned_dword_base_address rs1_val imm) 8) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (swSplicedDword imm rs1_val rs2_val
          (loaded_dword_at s (compute_aligned_dword_base_address rs1_val imm)
            hbytes hsetup.no_ovf)) =
      state_after_word_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 31 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base (by simpa [base] using hbytes)
    (by simpa [base] using hsetup.no_ovf)
  let word_val := Sail.BitVec.extractLsb rs2_val 31 0
  let dword_new := swSplicedDword imm rs1_val rs2_val dword_orig
  let off := (ea - base).toNat
  have hoff : off = 0 ∨ off = 4 := by
    simpa [off, ea, base] using hsetup.word_offset_cases
  have hspec : StoreSplice.IsWordSplice dword_orig dword_new word_val off := by
    simpa [dword_new, swSplicedDword, dword_orig, word_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.wordSplice_spec dword_orig word_val off hoff
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
      (state_after_word_store s ea word_val).mem := by
    dsimp [StoreSplice.IsWordSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_word_store_populated
      s ea base word_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_word_store s ea word_val := by
    simpa [state_after_dword_store, state_after_word_store] using hmem_eq
  simpa [ea, base, dword_new, word_val] using hstate

/-- **Concrete aligned SW execution on the Jolt side.**

This composes the Jolt monadic reduction with the pure splice bridge.  After
this theorem, the Jolt side is expressed in the same canonical memory state as
the Sail side: `state_after_word_store`. -/
theorem swProgramAuto_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreFacts
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
        (swSplicedDword imm rs1_val rs2_val
          (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
            hbytes h_base_aligned.no_ovf))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val
            (loaded_dword_at js.sail (compute_aligned_dword_base_address rs1_val imm)
              hbytes h_base_aligned.no_ovf)))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0) := by
  rcases swProgramAuto_reduces_to_dword_store imm rs2 rs1 js hpriv hmprv rs1_val rs2_val
      hrs1 hrs2 hsetup h_base_aligned hbytes hload_pmp hread_mmio hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sw_spliced_dword_store_eq_word_store imm js.sail rs1_val rs2_val
    hsetup hbytes

/-- **Sail-side SW reduction.**

The native Sail instruction is a single store step.  Under an explicit
successful `vmem_write` assumption, it reduces to the same canonical
`state_after_word_store` used by the Jolt-side theorem. -/
theorem execute_SW_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hwrite_word :
      vmem_write rs1 (sign_extend (m := 64) imm) 4
        (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0))) :
    (execute_STORE imm rs2 rs1 4).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  exact execute_STORE_word_eq_state_after_word_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm)
    (compute_aligned_dword_base_address rs1_val imm)
    hrs1_exists hrs2 hwrite_word

/-- **Jolt-side misaligned SW skeleton.**

The leading `VirtualAssertWordAlignment` stops the Jolt program before setup,
returning Sail's store/AMO alignment exception. -/
theorem swProgramAuto_concrete_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 3 ≠ 0) :
    (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js := by
  let tail : JoltISA.Program :=
    .instr (JoltISA.Encoded.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
    .instr (JoltISA.Encoded.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
    .instr (JoltISA.Encoded.LD .normal (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) <|
    .instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) 0) <|
    .instr (.ANDN (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.VirtualShiftDataW (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.ADD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (JoltISA.Encoded.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <|
    .done RETIRE_SUCCESS
  have h := StoreProgramBlocks.assertWordBlockMisaligned tail
    imm rs1 js rs1_val hrs1 hmis
  simpa [JoltISA.swProgramAuto, tail] using h

/-- **Sail-side misaligned SW skeleton.**

The native Sail store should fail at the same alignment check, producing the
same store/AMO alignment exception. -/
theorem execute_SW_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 3 ≠ 0) :
    (execute_STORE imm rs2 rs1 4).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  let ea := load_effective_address rs1_val imm
  unfold execute_STORE
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  have hmis' :
      access_causes_misaligned_exception (Virtaddr ea) 4 false = true := by
    simpa [ea] using access_misaligned_4_unaligned_true ea hmis
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrs1, hrs2,
        vmem_write_addr, hmis', ea]
  rfl

/-- Successful `SW` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem swProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs2 rs1 : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.swProgramAuto rs1 rs2 imm) := by
    unfold JoltISA.swProgramAuto
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true]
    repeat' apply And.intro
    all_goals exact JoltISA.not_protected_of_instructionTmp rfl
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main public SW theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
def swProgramEqSailStatement (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js) =
    (execute_STORE imm rs2 rs1 4).run js.sail

/-- **Main public SW theorem.**  The Jolt bytecode expansion matches Sail after
materializing Jolt's persistent CSR virtual registers. -/
theorem swProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    swProgramEqSailStatement imm rs2 rs1 js h := by
  unfold swProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have hwin := h.dwordWindowFacts
  let dword_orig := loaded_dword_at js.sail base
    (by simpa [base] using hwin.bytes)
    (by simpa [base] using hwin.aligned.no_ovf)
  let dword_new := swSplicedDword imm h.rs1_val h.rs2_val dword_orig
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases halign : ea &&& (3 : BitVec 64) = 0
  · have hsetup : StoreSplice.WordStoreFacts
        (load_effective_address h.rs1_val imm)
        (compute_aligned_dword_base_address h.rs1_val imm) :=
      StoreSplice.wordStoreFacts_of_effective_address
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
    have hstore_fits : offset + 4 ≤ 8 := by
      have hcases := write_word_offset_cases ea (by simpa [ea] using halign)
      rcases hcases with h0 | h4 <;> omega
    have hstore_access :=
      StoreProgramEqSailAssumptions.storeAccessFacts h 4
        (by simpa [ea, offset] using hstore_fits)
    have hwrite_word :
        vmem_write rs1 (sign_extend (m := 64) imm) 4
          (Sail.BitVec.extractLsb h.rs2_val 31 0)
          (Store Data) false false false js.sail =
        .ok (Ok true)
          (state_after_word_store js.sail
            (load_effective_address h.rs1_val imm)
            (Sail.BitVec.extractLsb h.rs2_val 31 0)) :=
      vmem_write_word_store_reduces imm rs1 js.sail h.cur_privilege h.mstatus_mprv
        h.rs1_val h.rs1_read (Sail.BitVec.extractLsb h.rs2_val 31 0)
        (by simpa [ea] using halign)
        (by simpa [ea] using hstore_access.store_pmp)
        (by simpa [ea] using hstore_access.write_mmio)
    rcases swProgramAuto_concrete_aligned imm rs2 rs1 js h.cur_privilege h.mstatus_mprv
        h.rs1_val h.rs2_val
        h.rs1_read h.rs2_read hsetup
        (by simpa [base] using hwin.aligned)
        (by simpa [base] using hwin.bytes)
        (by simpa [base] using hwin.load_pmp)
        (by simpa [base] using hwin.read_mmio)
        (by simpa [base, dword_orig, dword_new] using hwrite_dword) with
      ⟨js', hjolt, hjolt_sail⟩
    have hsail := execute_SW_reduces imm rs2 rs1 js h.rs1_val h.rs2_val
      h.rs1_read h.rs2_read hwrite_word
    have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
      swProgramAuto_preserves_projected_vregs imm rs2 rs1 hjolt
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
  · have hjolt := swProgramAuto_concrete_misaligned imm rs2 rs1 js h.rs1_val
      h.rs1_read (by simpa [ea] using halign)
    have hsail := execute_SW_misaligned imm rs2 rs1 js h.rs1_val h.rs2_val
      h.rs1_read h.rs2_read (by simpa [ea] using halign)
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    rw [h_project_initial]

end SW_main

end
