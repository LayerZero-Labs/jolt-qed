import JoltConstraints.theorems.Soundness.Layer5.SharedMemoryChecks
import JoltConstraints.theorems.Soundness.Layer5.CodeRegionFrame
import JoltConstraints.theorems.Completeness.Helpers.RamHistoryProofHelpers
import JoltConstraints.theorems.Completeness.Helpers.RamOutputProofHelpers
import JoltConstraints.translation.honest_witness

open LeanRV64D JoltISA
set_option autoImplicit false
namespace JoltConstraints
open Soundness
open scoped BigOperators

/-- The honest witness has zero selected increment at every protected word.
For example, a same-value input store keeps the old word and contributes zero.
Jolt at `ff6fc6568`: RAM `unbatched_relation`, third claim. -/
theorem honestWitness_ramWriteProtected {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs) (fits : params.RamFits trace) (valid : ramAccessesValid trace) :
    ramWriteProtected (fun k => ramWriteProtectedMask trace.bytecode
      trace.initialState.jolt_device.memory_layout k.val)
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  symm
  apply Finset.sum_eq_zero
  intro k _
  change ramWriteProtectedMask trace.bytecode trace.initialState.jolt_device.memory_layout k.val *
    (TraceWitness.RamRa params trace k t * HonestWitness.RamInc params trace t) = 0
  by_cases zero : ramWriteProtectedMask (F := F) trace.bytecode
      trace.initialState.jolt_device.memory_layout k.val = 0
  · rw [zero, zero_mul]
  have masked : ramWriteProtectedMask (F := F) trace.bytecode
      trace.initialState.jolt_device.memory_layout k.val = 1 := by
    by_contra notOne
    apply zero
    unfold ramWriteProtectedMask at notOne ⊢
    dsimp only at notOne ⊢
    split_ifs with isProtected
    · exact False.elim (notOne (by rw [if_pos isProtected]))
    · rfl
  rw [masked, one_mul]
  by_cases inside : t.val < trace.rows.size
  · let row := trace.rows[t.val]'inside
    have setup := trace.protected_memory.1 t.val inside
    have built := (initial_state_device inst inputs trace.initialState trace.initialized).1
    unfold JoltInstance.memory_layout at built
    have code : row.preState.codeRegion =
        ramCodeRegion trace.bytecode trace.initialState.jolt_device.memory_layout :=
      (congrArg (fun guard => (Option.map CodeGuard.region guard).getD (0, 0)) setup.code).trans
        (initial_state_codeRegion trace.initialized trace.expands)
    have memory := JoltIOSetupFrame.execInstr_memory _ _ _ _ (trace.row t.val inside).executes
    have wordSame : Mmu.ram_doubleword row.postState.sail.mem
        (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * k.val) =
        Mmu.ram_doubleword row.preState.sail.mem
          (ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * k.val) := by
      apply ramImageWord_congr
      intro offset within
      exact memory.bytes _ (mask_one_protected_byte trace.bytecode
        trace.initialState.jolt_device.memory_layout _ built row.preState setup.layout code
        k.val offset within masked)
    have step := ram_history_word_step (F := F) params trace fits valid t inside k
    rw [wordSame] at step
    linear_combination -step
  · simp only [HonestWitness.RamInc, dite_eq_right inside, mul_zero]

end JoltConstraints
