import JoltConstraints.Constraints.RamReadData
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

/-!
Execution never changes the device fields fixed when Rust builds its emulator:
the memory layout and both advice buffers. Sail steps do not touch the device,
device stores only change `outputs` and `panic`, and HostIO only appends to the
advice tape. The trace-level result carries this from the program's initial
state to the final recorded state.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions


namespace JoltConstraints

open JoltIOSetupFrame

/-- Every recorded pre-state has the program's initial device setup. -/
theorem trace_preState_ioSame {program : JoltProgram} (trace : JoltTrace program)
    (i : Nat) (hi : i < trace.rows.size) :
    Same program.initialState.jolt_device (getElem trace.rows i hi).preState.jolt_device := by
  induction i with
  | zero =>
    rw [trace.startsAtInitial (by omega)]
    exact Same.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have hexec := execInstr_rule _ _ _ _ (getElem trace.rows i (by omega)).executes
    have hlink := trace.linked i (by omega) hi
    dsimp only at hlink
    rw [hlink]
    split
    · exact hprev.trans hexec
    · exact hprev.trans hexec

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {program : JoltProgram} (trace : JoltTrace program) :
    Same program.initialState.jolt_device (HonestWitness.finalTraceState trace).jolt_device := by
  unfold HonestWitness.finalTraceState
  split
  · rename_i nonempty
    exact (trace_preState_ioSame trace _ _).trans
      (execInstr_rule _ _ _ _ (getElem trace.rows (trace.rows.size - 1) _).executes)
  · exact Same.refl _

end JoltConstraints
