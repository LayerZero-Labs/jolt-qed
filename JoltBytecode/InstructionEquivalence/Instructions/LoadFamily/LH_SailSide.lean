import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LH_SailSide

/-- A failed leading halfword load-alignment assertion stops the structured
program with Sail's load-address-alignment exception. -/
theorem assertHalfwordBlockMisaligned (tail : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& (1 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertHalfwordAlignment rs1 imm
        (ExceptionType.E_Load_Addr_Align ())) tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm),
          ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm),
      ExceptionType.E_Load_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm
          (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.virtual_assert_halfword_alignment_run_misaligned
        (base := rs1)
        (imm := imm)
        (fault := ExceptionType.E_Load_Addr_Align ())
        (js := js)
        (baseValue := val)
        (h_read := hrx)
        (h_misaligned := by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertHalfwordAlignment rs1 imm
        (ExceptionType.E_Load_Addr_Align ()))
      tail js js e hassert)

/-- The halfword selected by an aligned load fits inside its enclosing
dword. -/
theorem halfword_offset_fits (base : BitVec 64) (imm : BitVec 12)
    (hAlign : load_effective_address base imm &&& (1 : BitVec 64) = 0) :
    (load_effective_address base imm &&& (7 : BitVec 64)).toNat + 2 ≤ 8 := by
  have hlt := addr_and_seven_halfword_lt_seven
    (load_effective_address base imm) hAlign
  omega

/-- Splitting an effective address into its aligned dword base and halfword
offset recovers the original address. -/
theorem aligned_base_add_halfword_offset
    (base : BitVec 64) (imm : BitVec 12) :
    compute_aligned_dword_base_address base imm +
        BitVec.ofNat 64
          (load_effective_address base imm &&& (7 : BitVec 64)).toNat =
      load_effective_address base imm := by
  simpa only [compute_aligned_dword_base_address] using
    addr_split_aligned_offset (load_effective_address base imm)

/-- The aligned halfword subaccess cannot wrap while locating its start inside
the enclosing dword. -/
theorem halfword_subaccess_no_overflow
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    (compute_aligned_dword_base_address h.rs1_val imm).toNat +
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat <
      2 ^ 64 := by
  have hbase := h.dwordWindowFacts.aligned.no_ovf
  have hfit := halfword_offset_fits h.rs1_val imm hAlign
  omega

/-- The enclosing Jolt dword window contains Sail's halfword-sized access. -/
theorem halfword_mem_present
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    MemBytesPresentAt js.sail (load_effective_address h.rs1_val imm) 2 := by
  simpa only [aligned_base_add_halfword_offset] using
    memBytesPresentAt_subaccess
      (s := js.sail)
      (base := compute_aligned_dword_base_address h.rs1_val imm)
      (baseWidth := 8)
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 2)
      h.dwordWindowFacts.bytes
      (halfword_offset_fits h.rs1_val imm hAlign)
      (halfword_subaccess_no_overflow imm rs1 js h hAlign)

/-- The enclosing Jolt load-PMP window authorizes Sail's halfword-sized
access. -/
theorem halfword_load_pmp_ok
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    Assumptions.LoadPmpOk
      (load_effective_address h.rs1_val imm) 2 js.sail := by
  simpa only [aligned_base_add_halfword_offset] using
    h.load_pmp.subaccess
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 2)
      (halfword_offset_fits h.rs1_val imm hAlign)

/-- The enclosing Jolt non-MMIO window contains Sail's halfword-sized
access. -/
theorem halfword_not_readable_mmio
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    Assumptions.NotReadableMmio
      (load_effective_address h.rs1_val imm) 2 js.sail := by
  simpa only [aligned_base_add_halfword_offset] using
    h.not_readable_mmio.subaccess
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 2)
      (halfword_offset_fits h.rs1_val imm hAlign)

/-- An aligned effective halfword address has room for both bytes. -/
theorem halfword_no_overflow
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    (load_effective_address h.rs1_val imm).toNat + 1 < 2 ^ 64 :=
  aligned_halfword_addr_no_ovf
    (load_effective_address h.rs1_val imm) hAlign

/-- Sail's alignment evidence for an aligned halfword load. -/
theorem aligned_access
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    AlignedAccess (load_effective_address h.rs1_val imm) 2 := by
  refine
    { misalign := ?_
      split := ?_ }
  · exact access_misaligned_2_aligned_false
      (load_effective_address h.rs1_val imm) hAlign
  · exact split_misaligned_aligned_2
      (load_effective_address h.rs1_val imm) hAlign

/-- The architectural value written by Sail's aligned `LH`. -/
abbrev writeValue
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    BitVec 64 :=
  sign_extend (m := 64)
    (loaded_halfword_at js.sail
      (load_effective_address h.rs1_val imm)
      (halfword_mem_present imm rs1 js h hAlign)
      (halfword_no_overflow imm rs1 js h hAlign))

/-- The architectural value written by Sail's aligned `LHU`. -/
abbrev writeValueUnsigned
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    BitVec 64 :=
  zero_extend (m := 64)
    (loaded_halfword_at js.sail
      (load_effective_address h.rs1_val imm)
      (halfword_mem_present imm rs1 js h hAlign)
      (halfword_no_overflow imm rs1 js h hAlign))

/-- Writing Sail's directly loaded halfword is the same as writing the
selected halfword of the enclosing loaded dword. -/
theorem stateAfterWrite_writeValue_eq_dword_halfword
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    let facts := h.dwordWindowFacts
    let dval :=
      loaded_dword_at js.sail
        (compute_aligned_dword_base_address h.rs1_val imm)
        facts.bytes facts.aligned.no_ovf
    let halfwordOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat
    stateAfterWrite js.sail rd (writeValue imm rs1 js h hAlign) =
      stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (halfword_of_dword dval halfwordOffset)) := by
  simp only
  unfold writeValue
  rw [loaded_halfword_in_dword
    (s := js.sail)
    (addr := load_effective_address h.rs1_val imm)
    (halign := hAlign)
    (hbytes_base := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.bytes)
    (h_no_ovf_base := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.aligned.no_ovf)
    (hbytes_addr := halfword_mem_present imm rs1 js h hAlign)
    (h_no_ovf_addr := halfword_no_overflow imm rs1 js h hAlign)]

/-- Writing Sail's directly loaded unsigned halfword is the same as writing
the selected halfword of the enclosing loaded dword. -/
theorem stateAfterWrite_writeValueUnsigned_eq_dword_halfword
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    let facts := h.dwordWindowFacts
    let dval :=
      loaded_dword_at js.sail
        (compute_aligned_dword_base_address h.rs1_val imm)
        facts.bytes facts.aligned.no_ovf
    let halfwordOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat
    stateAfterWrite js.sail rd (writeValueUnsigned imm rs1 js h hAlign) =
      stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (halfword_of_dword dval halfwordOffset)) := by
  simp only
  unfold writeValueUnsigned
  rw [loaded_halfword_in_dword
    (s := js.sail)
    (addr := load_effective_address h.rs1_val imm)
    (halign := hAlign)
    (hbytes_base := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.bytes)
    (h_no_ovf_base := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.aligned.no_ovf)
    (hbytes_addr := halfword_mem_present imm rs1 js h hAlign)
    (h_no_ovf_addr := halfword_no_overflow imm rs1 js h hAlign)]

/-- Sail-side aligned `execute_LOAD imm rs1 rd false 2` reduces to a register
write of the sign-extended loaded halfword. -/
theorem execute_LH_reduces
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (writeValue imm rs1 js h hAlign)) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  rw [vmem_read_halfword_reduces
    (imm := imm)
    (rs1 := rs1)
    (s := js.sail)
    (hpriv := h.cur_privilege)
    (hmprv := h.mstatus_mprv)
    (v := h.rs1_val)
    (hrx := h.rs1_read)
    (ha := aligned_access imm rs1 js h hAlign)
    (value := loaded_halfword_at js.sail
      (load_effective_address h.rs1_val imm)
      (halfword_mem_present imm rs1 js h hAlign)
      (halfword_no_overflow imm rs1 js h hAlign))
    (h_mem := mem_read_2_eq_loaded_halfword
      (addr := load_effective_address h.rs1_val imm)
      (s := js.sail)
      (hpriv := h.cur_privilege)
      (hmprv := h.mstatus_mprv)
      (h_no_ovf := halfword_no_overflow imm rs1 js h hAlign)
      (hbytes := halfword_mem_present imm rs1 js h hAlign)
      (hpmp := halfword_load_pmp_ok imm rs1 js h hAlign)
      (hmmio := halfword_not_readable_mmio imm rs1 js h hAlign))]

  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind,
    EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd (writeValue imm rs1 js h hAlign) js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side aligned `execute_LOAD imm rs1 rd true 2` reduces to a register
write of the zero-extended loaded halfword. -/
theorem execute_LHU_reduces
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (writeValueUnsigned imm rs1 js h hAlign)) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  rw [vmem_read_halfword_reduces
    (imm := imm)
    (rs1 := rs1)
    (s := js.sail)
    (hpriv := h.cur_privilege)
    (hmprv := h.mstatus_mprv)
    (v := h.rs1_val)
    (hrx := h.rs1_read)
    (ha := aligned_access imm rs1 js h hAlign)
    (value := loaded_halfword_at js.sail
      (load_effective_address h.rs1_val imm)
      (halfword_mem_present imm rs1 js h hAlign)
      (halfword_no_overflow imm rs1 js h hAlign))
    (h_mem := mem_read_2_eq_loaded_halfword
      (addr := load_effective_address h.rs1_val imm)
      (s := js.sail)
      (hpriv := h.cur_privilege)
      (hmprv := h.mstatus_mprv)
      (h_no_ovf := halfword_no_overflow imm rs1 js h hAlign)
      (hbytes := halfword_mem_present imm rs1 js h hAlign)
      (hpmp := halfword_load_pmp_ok imm rs1 js h hAlign)
      (hmmio := halfword_not_readable_mmio imm rs1 js h hAlign))]

  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ :=
    wX_shape rd (writeValueUnsigned imm rs1 js h hAlign) js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side misaligned `LH` stops with a load-address-alignment exception. -/
theorem execute_LH_misaligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) ≠ 0) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address h.rs1_val imm),
          ExceptionType.E_Load_Addr_Align ())) js.sail := by
  let ea := load_effective_address h.rs1_val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa only [ea] using access_misaligned_2_unaligned_true ea hMisaligned
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, ext_data_get_addr, h.rs1_read, vmem_read_addr, hmis, ea]
  rfl

/-- Sail-side misaligned `LHU` stops with the same load-address-alignment
exception as signed `LH`. -/
theorem execute_LHU_misaligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) ≠ 0) :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address h.rs1_val imm),
          ExceptionType.E_Load_Addr_Align ())) js.sail := by
  let ea := load_effective_address h.rs1_val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa only [ea] using access_misaligned_2_unaligned_true ea hMisaligned
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, ext_data_get_addr, h.rs1_read, vmem_read_addr, hmis, ea]
  rfl

end LH_SailSide
