import JoltConstraints.theorems.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.theorems.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.theorems.trace_interface

open LeanRV64D

/-! The remaining HostIO restriction marks a boundary of the frozen bytecode model.

VirtualHostIO has no opcode circuit flags or lookup table, and selects no register
read or write. Its local constraints therefore do not describe host-side effects.
The bytecode model's `execHostIOWith` can fail on invalid event types and enables
pointer-overflow rejection only through `hostIO.overflowChecks`; the initialized
soundness run disables that setting.
At this pin Jolt's tracer instead logs and ignores invalid marker/print events and
rejects overflowing or unreadable host ranges before reading them.
The theorem below retains its existing modeled-success premise; it does not prove
unrestricted fidelity for Jolt's new checked and fallible HostIO behavior.
For example, an unknown print event is ignored by Jolt but fails in the frozen model.
Jolt at `ff6fc6568`: `tracer/src/instruction/virtual_host_io.rs` (`VirtualHostIO::exec`),
`tracer/src/emulator/cpu.rs` (`Cpu::handle_jolt_cycle_marker`, `Cpu::handle_jolt_print`),
and `tracer/src/emulator/host_io.rs` (`read_host_bytes`). -/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA in
/-- FIXME: Temporary program restriction for host calls whose failures are not
encoded by the local constraints. To raise with a16z together
with the other FIXMEs. Remove once Jolt either constrains host calls or makes
them unable to fail, the model reflects that, and the unrestricted proof is
established. This is not a verifier check.

For every private input and relaxed execution prefix, the next attempted
VirtualHostIO row executes without failing. This restriction
depends on the program's execution, not on a witness. -/
def JoltInstance.HostCallsSucceed (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
      match run.bytecode[next].instruction with
      | .VirtualHostIO => ∃ post, execHostIO pre = .ok RETIRE_SUCCESS post
      | _ => True

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- The program restriction supplies successful live HostIO execution for an
attempted row. HostIO can append to the advice tape, but cannot change Sail
registers, RAM bytes or virtual registers. The register-table increment still
needs a separate argument. For example, an advice-write call may append bytes
while preserving every register. -/
theorem host_call_exec_sail_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.HostCallsSucceed)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre)
    (answer : BitVec 64)
    (instruction : run.bytecode[next].instruction = .VirtualHostIO)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧ post.sail = pre.sail ∧
        post.vregs = pre.vregs := by
  have success := restricted privateInputs run next pre ready
  rw [instruction] at success
  obtain ⟨post, executes⟩ := success
  have frame := execHostIO_keeps_state pre post _ executes
  refine ⟨post, ?_, frame.1, frame.2⟩
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instruction]; rfl),
    instruction]
  simpa only [execWithTapeAnswer, execInstr] using executes

end JoltConstraints.Soundness
