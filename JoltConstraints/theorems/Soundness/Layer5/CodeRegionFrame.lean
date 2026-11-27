import JoltConstraints.theorems.program_facts
import JoltConstraints.translation.Constraints.RamWriteProtected
import JoltConstraints.theorems.Completeness.Helpers.IOSetupFrame
import JoltConstraints.theorems.Soundness.Layer5.TapeTrace
import JoltConstraints.theorems.layout_facts

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- The initialized code-word interval is the public protected-code interval.
For example, an expanded source protects the same words as its decoded source.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`CodeGuard::new`). -/
theorem initial_state_codeRegion
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {state : SailJoltState} (initialized : inst.initial_state inputs = some state)
    {bytecode : Array JoltInstructionRow} (expanded : expand_program inst.program = some bytecode) :
    state.codeRegion = ramCodeRegion bytecode state.jolt_device.memory_layout := by
  obtain ⟨layout, _, _, _, _, built⟩ := initial_state_build inst inputs state initialized
  obtain ⟨guard, guardBuilt, shape⟩ := initialState_shape _ _ _ _ _ _ built
  have regionBuilt := CodeGuard.new_region guardBuilt
  rw [shape]
  unfold ramCodeRegion
  rw [expand_program_source_extents inst.program bytecode expanded]
  simp only [SailJoltState.codeRegion, Option.map_some, Option.getD_some, codeRegionOf]
  change guard.region = (code_region _ layout.get_lowest_address.toNat).getD (0, 0)
  rw [show code_region (inst.program.instructions.toList.map
      fun row => (row.address, row.is_compressed)) layout.get_lowest_address.toNat =
      some guard.region from regionBuilt]
  rfl

/-- Every retained prefix keeps its initialized code-word interval.
For example, a prefix ending at an output store still protects the decoded code.
The proof uses its execution certificate and row links, including PC preparation. -/
theorem UntrustedAnswerRun.final_codeRegion
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) :
    (TraceWitness.finalTraceState run.toTrace).codeRegion =
      ramCodeRegion run.bytecode run.initialState.jolt_device.memory_layout := by
  have starts : ∀ first, run.rows[0]? = some first →
      first.preState.codeRegion = run.initialState.codeRegion := by
    intro first atFirst
    rw [(run.starts first atFirst).2.2]
    rfl
  have linked : ∀ i current next,
      run.rows[i]? = some current → run.rows[i + 1]? = some next →
      next.preState.codeRegion = current.postState.codeRegion := by
    intro i current next currentIs nextIs
    have link := run.linked i current next currentIs nextIs
    split at link
    · exact congrArg SailJoltState.codeRegion link.2
    · obtain ⟨_, _, _, _, nextState⟩ := link
      rw [nextState]
      rfl
  have preserved : ∀ step : Fin run.rows.size,
      (run.rows[step]).preState.codeRegion = (run.rows[step]).postState.codeRegion := by
    intro step
    exact execWithTapeAnswer_codeRegion _ _ _ _ _ (run.executes step)
  have fixed := Trace.finalTraceState_projection_relation run.toTrace
    SailJoltState.codeRegion Eq (fun _ => rfl) (fun _ _ _ a b => a.trans b)
    starts linked preserved
  exact fixed.symm.trans (initial_state_codeRegion run.initialized run.expands)

end JoltConstraints.Soundness
