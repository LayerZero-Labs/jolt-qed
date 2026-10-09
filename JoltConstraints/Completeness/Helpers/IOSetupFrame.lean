import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RamReadData
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

/-!
Execution never changes the device fields fixed when Rust builds its emulator:
the memory layout, the inputs and both advice buffers. Sail steps do not touch the device,
device stores only change `outputs` and `panic`, and HostIO only appends to the
advice tape. The trace-level result carries this from the program's initial
state to the final recorded state.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions


namespace JoltConstraints

open JoltIOSetupFrame

/-- Every recorded pre-state has the program's initial device setup. -/
theorem trace_preState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (hi : i < trace.rows.size) :
    Same trace.initialState.jolt_device (getElem trace.rows i hi).preState.jolt_device := by
  induction i with
  | zero =>
    rw [trace.startsAtInitial (by omega)]
    exact Same.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have hexec := execInstr_rule _ _ _ _ (trace.row i (by omega)).executes
    have hlink := trace.linkedState i (by omega) hi
    rw [hlink]
    split
    · exact hprev.trans hexec
    · exact hprev.trans hexec

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Same trace.initialState.jolt_device (TraceWitness.finalTraceState trace).jolt_device := by
  unfold TraceWitness.finalTraceState
  split
  · rename_i nonempty
    exact (trace_preState_ioSame trace _ _).trans
      (execInstr_rule _ _ _ _ (trace.row (trace.rows.size - 1) (by omega)).executes)
  · exact Same.refl _

end JoltConstraints
