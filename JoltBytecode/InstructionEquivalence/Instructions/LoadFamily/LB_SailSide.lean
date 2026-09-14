import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
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

namespace LB_SailSide

/-- The byte selected by `LB` fits inside its enclosing dword. -/
theorem byte_offset_fits (base : BitVec 64) (imm : BitVec 12) :
    (load_effective_address base imm &&& (7 : BitVec 64)).toNat + 1 ≤ 8 := by
  have hlt := addr_and_seven_lt_eight (load_effective_address base imm)
  omega

/-- Splitting an effective address into its aligned dword base and byte offset
recovers the original address. -/
theorem aligned_base_add_byte_offset (base : BitVec 64) (imm : BitVec 12) :
    compute_aligned_dword_base_address base imm +
        BitVec.ofNat 64
          (load_effective_address base imm &&& (7 : BitVec 64)).toNat =
      load_effective_address base imm := by
  simpa only [compute_aligned_dword_base_address] using
    addr_split_aligned_offset (load_effective_address base imm)

/-- The one-byte subaccess used by Sail cannot overflow when its enclosing
dword access is valid. -/
theorem byte_subaccess_no_overflow
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    (compute_aligned_dword_base_address h.rs1_val imm).toNat +
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat <
      2 ^ 64 := by
  have hbase := h.dwordWindowFacts.aligned.no_ovf
  have hfit := byte_offset_fits h.rs1_val imm
  omega

/-- The enclosing Jolt dword window contains Sail's byte-sized `LB` access. -/
theorem byte_mem_present
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    MemBytesPresentAt js.sail (load_effective_address h.rs1_val imm) 1 := by
  simpa only [aligned_base_add_byte_offset] using
    memBytesPresentAt_subaccess
      (s := js.sail)
      (base := compute_aligned_dword_base_address h.rs1_val imm)
      (baseWidth := 8)
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 1)
      h.dwordWindowFacts.bytes
      (byte_offset_fits h.rs1_val imm)
      (byte_subaccess_no_overflow imm rs1 js h)

/-- The enclosing Jolt load-PMP window authorizes Sail's byte-sized access. -/
theorem byte_load_pmp_ok
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    Assumptions.LoadPmpOk
      (load_effective_address h.rs1_val imm) 1 js.sail := by
  simpa only [aligned_base_add_byte_offset] using
    h.load_pmp.subaccess
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 1)
      (byte_offset_fits h.rs1_val imm)

/-- The enclosing Jolt non-MMIO window contains Sail's byte-sized access. -/
theorem byte_not_readable_mmio
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    Assumptions.NotReadableMmio
      (load_effective_address h.rs1_val imm) 1 js.sail := by
  simpa only [aligned_base_add_byte_offset] using
    h.not_readable_mmio.subaccess
      (offset :=
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
      (accessWidth := 1)
      (byte_offset_fits h.rs1_val imm)

/-- The byte at Sail's effective `LB` address is present. -/
theorem byte_present
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    MemBytePresentAt js.sail
      (load_effective_address h.rs1_val imm).toNat :=
  (byte_mem_present imm rs1 js h).single_byte

/-- The architectural value written by Sail's `LB`. -/
abbrev writeValue
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) : BitVec 64 :=
  sign_extend (m := 64)
    (loaded_byte_at js.sail
      (load_effective_address h.rs1_val imm)
      (byte_present imm rs1 js h))

/-- The architectural value written by Sail's `LBU`. -/
abbrev writeValueUnsigned
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) : BitVec 64 :=
  zero_extend (m := 64)
    (loaded_byte_at js.sail
      (load_effective_address h.rs1_val imm)
      (byte_present imm rs1 js h))

/-- 
TODO: Move to dword arithmetic
Writing Sail's directly loaded byte is the same as writing the selected
byte of the enclosing loaded dword. -/
theorem stateAfterWrite_writeValue_eq_dword_byte
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let dval :=
      loaded_dword_at js.sail
        (compute_aligned_dword_base_address h.rs1_val imm)
        facts.bytes facts.aligned.no_ovf
    let byteOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat
    stateAfterWrite js.sail rd (writeValue imm rs1 js h) =
      stateAfterWrite js.sail rd
        (sign_extend (m := 64) (byte_of_dword dval byteOffset)) := by
  simp only
  unfold writeValue
  rw [loaded_byte_in_dword
    (s := js.sail)
    (addr := load_effective_address h.rs1_val imm)
    (hbytes := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.bytes)
    (h_no_ovf := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.aligned.no_ovf)
    (hpresent := byte_present imm rs1 js h)]

/-- Writing Sail's directly loaded unsigned byte is the same as writing the
selected byte of the enclosing loaded dword. -/
theorem stateAfterWrite_writeValueUnsigned_eq_dword_byte
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let dval :=
      loaded_dword_at js.sail
        (compute_aligned_dword_base_address h.rs1_val imm)
        facts.bytes facts.aligned.no_ovf
    let byteOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat
    stateAfterWrite js.sail rd (writeValueUnsigned imm rs1 js h) =
      stateAfterWrite js.sail rd
        (zero_extend (m := 64) (byte_of_dword dval byteOffset)) := by
  simp only
  unfold writeValueUnsigned
  rw [loaded_byte_in_dword
    (s := js.sail)
    (addr := load_effective_address h.rs1_val imm)
    (hbytes := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.bytes)
    (h_no_ovf := by
      simpa only [compute_aligned_dword_base_address] using
        h.dwordWindowFacts.aligned.no_ovf)
    (hpresent := byte_present imm rs1 js h)]

/-- Sail-side `execute_LOAD imm rs1 rd false 1` reduces to a register write of
the sign-extended loaded byte. -/
theorem execute_LB_reduces
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (writeValue imm rs1 js h)) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  -- My one lemma that cuts through the memory reads
  -- TODO: (ari) Can I generalise this further?
  rw [vmem_read_byte_reduces
    (imm := imm)
    (rs1 := rs1)
    (s := js.sail)
    (hpriv := h.cur_privilege)
    (hmprv := h.mstatus_mprv)
    (v := h.rs1_val)
    (hrx := h.rs1_read)
    (ha := aligned_access_1 (load_effective_address h.rs1_val imm))
    (value := loaded_byte_at js.sail
      (load_effective_address h.rs1_val imm)
      (byte_present imm rs1 js h))
    (h_mem := mem_read_1_eq_loaded_byte
      (addr := load_effective_address h.rs1_val imm)
      (s := js.sail)
      (hpriv := h.cur_privilege)
      (hmprv := h.mstatus_mprv)
      (hbytes := byte_mem_present imm rs1 js h)
      (hpmp := byte_load_pmp_ok imm rs1 js h)
      (hmmio := byte_not_readable_mmio imm rs1 js h))]

  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind,
    EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd (writeValue imm rs1 js h) js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side `execute_LOAD imm rs1 rd true 1` reduces to a register write of
the zero-extended loaded byte. -/
theorem execute_LBU_reduces
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    (execute_LOAD imm rs1 rd true 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (writeValueUnsigned imm rs1 js h)) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure,
    EStateM.pure, EStateM.run, if_true]
  rw [vmem_read_byte_reduces
    (imm := imm)
    (rs1 := rs1)
    (s := js.sail)
    (hpriv := h.cur_privilege)
    (hmprv := h.mstatus_mprv)
    (v := h.rs1_val)
    (hrx := h.rs1_read)
    (ha := aligned_access_1 (load_effective_address h.rs1_val imm))
    (value := loaded_byte_at js.sail
      (load_effective_address h.rs1_val imm)
      (byte_present imm rs1 js h))
    (h_mem := mem_read_1_eq_loaded_byte
      (addr := load_effective_address h.rs1_val imm)
      (s := js.sail)
      (hpriv := h.cur_privilege)
      (hmprv := h.mstatus_mprv)
      (hbytes := byte_mem_present imm rs1 js h)
      (hpmp := byte_load_pmp_ok imm rs1 js h)
      (hmmio := byte_not_readable_mmio imm rs1 js h))]

  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd (writeValueUnsigned imm rs1 js h) js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end LB_SailSide
