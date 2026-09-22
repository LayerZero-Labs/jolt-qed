import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SD` equivalence statement. -/
def sdInstrEqSailStatement
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.SD (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_STORE imm rs2 rs1 8).run js.sail)

/-- The Jolt `SD` side reduces to the shared virtual-memory write spine. -/
theorem sdJolt_reduces_to_vmem_write_addr
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    System.systemProjectResult
      ((JoltISA.execInstr (.SD (.xreg rs1) (.xreg rs2) imm)).run js) =
    let ea := load_effective_address h.rs1_val imm
    match vmem_write_addr (Virtaddr ea) 8 h.rs2_val
        (Store Data) false false false js.sail with
    | .ok (.Ok _) s' => .ok RETIRE_SUCCESS s'
    | .ok (.Err e) s' => .ok e s'
    | .error e s' => .error e s' := by
  unfold JoltISA.execInstr JoltISA.readSrc liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run,
    h.rs1_read, h.rs2_read]
  by_cases halign :
      h.rs1_val + sign_extend (m := 64) imm &&& (7 : BitVec 64) = 0
  · let ea := load_effective_address h.rs1_val imm
    have halign_ea : ea &&& (7 : BitVec 64) = 0 := by
      simpa [ea, load_effective_address, Memory.effectiveAddr12] using halign
    have hfits :
        (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat + 8 ≤ 8 := by
      have hoff :
          (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat = 0 := by
        simpa [ea] using congrArg BitVec.toNat halign_ea
      simpa [hoff]
    have hstore_access := StoreProgramEqSailAssumptions.storeAccessFacts h 8 hfits
    have haligned_access : AlignedAccess ea 8 :=
      { misalign := access_misaligned_8_aligned_false ea halign_ea
        split := split_misaligned_aligned_8 ea halign_ea }
    have hwrite :
        vmem_write_addr (Virtaddr ea) 8 h.rs2_val
          (Store Data) false false false js.sail =
        .ok (Ok true) (state_after_dword_store js.sail ea h.rs2_val) :=
      vmem_write_addr_dword_store_reduces ea h.rs2_val js.sail
        h.cur_privilege h.mstatus_mprv haligned_access
        hstore_access.store_pmp hstore_access.write_mmio
    let js' : SailJoltState :=
      { js with sail := state_after_dword_store js.sail ea h.rs2_val }
    have h_project_final :
        System.systemProject js' = state_after_dword_store js.sail ea h.rs2_val := by
      have hregs : js'.sail.regs = js.sail.regs := by
        simp only [js', state_after_dword_store]
      have hprojected : Projection.ProjectedVRegsPreserved js js' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      simpa [js'] using
        Projection.systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
          js js' hregs hprojected h.linkedCSRs
    have hwrite_raw :
        vmem_write_addr
          (Virtaddr (h.rs1_val + sign_extend (m := 64) imm)) 8 h.rs2_val
          (Store Data) false false false js.sail =
        .ok (Ok true) (state_after_dword_store js.sail ea h.rs2_val) := by
      simpa [ea, load_effective_address, Memory.effectiveAddr12] using hwrite
    simp only [halign, if_true]
    rw [JoltISA.writeMemoryWord_ram _ _ hstore_access.write_mmio.ram]
    unfold liftSail
    unfold System.systemProjectResult
    simp only [hwrite_raw, EStateM.bind, EStateM.pure]
    rw [h_project_final]
  · have hmis :
        access_causes_misaligned_exception
          (Virtaddr (h.rs1_val + sign_extend (m := 64) imm)) 8 false = true := by
      exact access_misaligned_8_unaligned_true _
        (by simpa [load_effective_address, Memory.effectiveAddr12] using halign)
    have hwrite :
        vmem_write_addr
          (Virtaddr (h.rs1_val + sign_extend (m := 64) imm)) 8 h.rs2_val
          (Store Data) false false false js.sail =
        .ok
          (Err (ExecutionResult.Memory_Exception
            (Virtaddr (h.rs1_val + sign_extend (m := 64) imm),
              ExceptionType.E_SAMO_Addr_Align ())))
          js.sail := by
      unfold vmem_write_addr
      simp only [hmis, if_true]
      unfold SailME.run PreSail.PreSailME.run
      simp only [ExceptT.mk, ExceptT.run, bind, EStateM.bind, pure,
        EStateM.pure, ExceptT.pure]
    simp only [halign, if_false]
    rw [hwrite]
    unfold System.systemProjectResult
    simp only [EStateM.pure]
    rw [show System.systemProject { js with vregs := js.vregs } = js.sail by
      simpa using Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs]

/-- The Sail `execute_STORE ... 8` side reduces to the same virtual-memory
write spine as Jolt `SD`. -/
theorem sdSail_reduces_to_vmem_write_addr
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    ((execute_STORE imm rs2 rs1 8).run js.sail) =
    let ea := load_effective_address h.rs1_val imm
    match vmem_write_addr (Virtaddr ea) 8 h.rs2_val
        (Store Data) false false false js.sail with
    | .ok (.Ok _) s' => .ok RETIRE_SUCCESS s'
    | .ok (.Err e) s' => .ok e s'
    | .error e s' => .error e s' := by
  unfold execute_STORE
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind,
    pure, EStateM.pure, EStateM.run, if_true]
  rw [h.rs2_read]
  simp only
  set data : BitVec (8 * 8) :=
    BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb h.rs2_val
        ((((8 : Nat) : Int) * (8 : Int) - (1 : Int)).toNat) 0)
  have hdata : data = h.rs2_val := by
    subst data
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  rw [hdata]
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, h.rs1_read, load_effective_address,
    Memory.effectiveAddr12]
  cases hres :
      vmem_write_addr (Virtaddr (h.rs1_val + sign_extend (m := 64) imm)) 8
        h.rs2_val (Store Data) false false false js.sail with
  | ok res s' =>
      cases res <;> rfl
  | error e s' =>
      rfl

theorem sdInstr_eq_sail
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    sdInstrEqSailStatement imm rs2 rs1 js h := by
  unfold sdInstrEqSailStatement
  rw [sdJolt_reduces_to_vmem_write_addr imm rs2 rs1 js h]
  rw [sdSail_reduces_to_vmem_write_addr imm rs2 rs1 js h]

end Natives

end
