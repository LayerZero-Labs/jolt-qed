import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer5.RuntimeAdvice

/-! Temporary program restriction for host calls (VirtualHostIO rows).

VirtualHostIO has no opcode circuit flags and no lookup table, so its local
constraints do not encode host-call failure or side effects. Its encoded `rd`
still participates in the register selectors. Jolt's tracer runs the call in
live mode, which a proved run uses, and there an invalid cycle-marker or print
event panics. The model's `JoltISA.execHostIOWith` keeps those failures. It
checks message-pointer overflow only when `hostIO.overflowChecks` is enabled;
the initialized soundness run has that setting disabled. A message that cannot
be read does not fail the call: the handler's trap is ignored. This is a
candidate found by reading the code; no satisfying witness has been built.
SDK guests pass only valid constant events.
At public pin 8bbb2357:
See : jolt/crates/jolt-riscv/src/instructions/virt/host_io.rs:3-6
See : jolt/tracer/src/instruction/virtual_host_io.rs:19-39
See : jolt/tracer/src/emulator/cpu.rs:1056-1105 -/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA in
/-- FIXME: Temporary program restriction for host calls whose failures are not
encoded by the local constraints. To raise with a16z together
with the other FIXMEs. Remove once Jolt either constrains host calls or makes
them unable to fail, the model reflects that, and the unrestricted proof is
established. This is not a verifier check.

For every private input and relaxed execution prefix, the next attempted
VirtualHostIO row executes without failing. Like `TracerAddressChecks`, it
depends on the program's execution, not on a witness. -/
def JoltInstance.HostCallsSucceed (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState),
    run.NextStep next pre →
      match run.bytecode[next].instruction with
      | .VirtualHostIO _ _ _ => ∃ post, execHostIO pre = .ok RETIRE_SUCCESS post
      | _ => True

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The program restriction supplies successful live HostIO execution for an
attempted row. HostIO can append to the advice tape, but cannot change Sail
registers, RAM bytes or virtual registers. The register-table increment still
needs a separate argument. -/
theorem host_call_exec_sail_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.HostCallsSucceed)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (ready : run.NextStep next pre)
    (dst : JoltISA.Dst) (src : JoltISA.Src) (imm answer : BitVec 64)
    (instruction : run.bytecode[next].instruction = .VirtualHostIO dst src imm)
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
