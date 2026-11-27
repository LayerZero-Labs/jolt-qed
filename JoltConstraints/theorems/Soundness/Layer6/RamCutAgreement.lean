import JoltConstraints.theorems.Soundness.Layer5.RamAgreement

open LeanRV64D

/-! One shared-memory agreement describes every word at a represented cut. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness JoltISA

/-- The final image reads each word directly from the final shared byte map.
For example, an output word needs no device-buffer overlay.
Jolt at `ff6fc6568`: `crates/jolt-witness/src/backend/trace/ram.rs`
(`final_ram_state`). -/
theorem finalRamWord_eq_ram_doubleword (trace : Trace) (index : Nat) :
    TraceWitness.finalRamWord trace index =
      Mmu.ram_doubleword (TraceWitness.finalTraceState trace).sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index) := by
  unfold TraceWitness.finalRamWord
  rw [MemoryLayout.get_lowest_address_toNat]
  rfl

/-- At a trace cut, full image agreement is exactly shared-map agreement.
For example, the same relation compares an input word and an ordinary RAM word. -/
theorem ramAgreement_iff
    {F : Type} [Field F] {size : Nat} (trace : Trace) (values : Fin size → F) :
    (∀ index, values index = ((TraceWitness.finalRamWord trace index.val).toNat : F)) ↔
      SharedRamAgreement trace.initialState.jolt_device.memory_layout values
        (TraceWitness.finalTraceState trace) := by
  simp only [SharedRamAgreement, finalRamWord_eq_ram_doubleword]

end JoltInstance
