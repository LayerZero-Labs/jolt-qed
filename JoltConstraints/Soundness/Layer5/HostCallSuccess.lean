import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.RuntimeAdvice

open LeanRV64D

/-! Host calls (VirtualHostIO rows) always succeed.

VirtualHostIO has no opcode circuit flags and no lookup table, so its local
constraints do not encode host-call failure. Since a16z/jolt#2410 Jolt's tracer
never fails a host call: an unknown call or event is ignored, and a byte range
that ends past its limit or holds a byte the guest could not load is logged
and skipped. The model's `JoltISA.execHostIOWith` follows the tracer, so a
host call fails only if reading x10..x13 fails, and those registers are present
in every state the soundness induction reaches. For example, a print whose
string pointer is in the stack canary retires and changes no guest state.
Allocation failures of the host process are outside the model.
See : jolt/tracer/src/emulator/host_io.rs:50-85 (`read_host_bytes`)
See : jolt/tracer/src/instruction/virtual_host_io.rs:19-38 (`VirtualHostIO::exec`)
See : jolt/tracer/src/emulator/cpu.rs:1079-1192 (host-call handlers)
at 3cc6e7bd1. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- From any state whose Sail registers are all present, `action` succeeds with
a value satisfying `post` and keeps the Sail state. -/
private def SucceedsKeepingSail {α : Type} (post : α → Prop) (action : JoltMonad α) : Prop :=
  ∀ state : SailJoltState, AllRegistersPresent state.sail →
    ∃ value after, action state = .ok value after ∧ post value ∧ after.sail = state.sail

private theorem succeeds_pure {α : Type} {post : α → Prop} (value : α) (holds : post value) :
    SucceedsKeepingSail post (pure value) :=
  fun state _ => ⟨value, state, rfl, holds, rfl⟩

private theorem succeeds_bind {α β : Type} {post : β → Prop} {first : JoltMonad α}
    {next : α → JoltMonad β}
    (firstSucceeds : SucceedsKeepingSail (fun _ => True) first)
    (nextSucceeds : ∀ value, SucceedsKeepingSail post (next value)) :
    SucceedsKeepingSail post (first >>= next) := by
  intro state present
  obtain ⟨value, middle, runs, -, sail⟩ := firstSucceeds state present
  have presentMiddle : AllRegistersPresent middle.sail := by
    rw [sail]
    exact present
  obtain ⟨result, after, runsNext, holds, sailNext⟩ := nextSucceeds value middle presentMiddle
  refine ⟨result, after, ?_, holds, sailNext.trans sail⟩
  simp only [bind, EStateM.bind, runs, runsNext]

private theorem succeeds_readSrc (source : Src) :
    SucceedsKeepingSail (fun _ => True) (readSrc source) :=
  fun state present => ⟨_, state, readSrc_of_present source state present, trivial, rfl⟩

private theorem succeeds_get : SucceedsKeepingSail (fun _ => True) (get : JoltMonad SailJoltState) :=
  fun state _ => ⟨state, state, rfl, trivial, rfl⟩

private theorem succeeds_modify (change : SailJoltState → SailJoltState)
    (keeps : ∀ state, (change state).sail = state.sail) :
    SucceedsKeepingSail (fun _ => True) (modify change : JoltMonad Unit) :=
  fun state _ => ⟨(), change state, rfl, trivial, keeps state⟩

private theorem succeeds_readHostBytes {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    SucceedsKeepingSail (fun _ => True) (readHostBytes Mmu.hostLoad pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact succeeds_pure _ trivial
  | succ count ih =>
    dsimp only [readHostBytes]
    refine succeeds_bind (fun state _ => ⟨_, state, rfl, trivial, rfl⟩) (fun result => ?_)
    cases result with
    | none => exact succeeds_pure _ trivial
    | some byte => exact ih _ _

/-- A host call retires from any state whose Sail registers are all present.
For example, an advice write whose range ends past `u64::MAX` retires without
appending anything. -/
theorem execHostIO_succeeds (pre : SailJoltState) (present : AllRegistersPresent pre.sail) :
    ∃ post, execHostIO pre = .ok RETIRE_SUCCESS post := by
  have succeeds : SucceedsKeepingSail (fun value => value = RETIRE_SUCCESS) execHostIO := by
    unfold execHostIO execHostIOWith readHostRange
    refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
    split
    · refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
      refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
      refine succeeds_bind ?_ fun result => ?_
      · split
        · exact succeeds_readHostBytes _ _ _
        · exact (succeeds_pure _ (by trivial))
      · cases result with
        | none => exact (succeeds_pure _ (by trivial))
        | some _ => exact succeeds_bind (succeeds_modify _ (fun _ => rfl)) fun _ => (succeeds_pure _ (by trivial))
    · split
      · refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
        refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
        refine succeeds_bind (succeeds_readSrc _) fun _ => ?_
        refine succeeds_bind succeeds_get fun _ => ?_
        split
        · refine succeeds_bind ?_ fun _ => (succeeds_pure _ (by trivial))
          split
          · exact succeeds_readHostBytes _ _ _
          · exact (succeeds_pure _ (by trivial))
        · exact (succeeds_pure _ (by trivial))
      · exact (succeeds_pure _ (by trivial))
  obtain ⟨value, post, runs, retires, -⟩ := succeeds pre present
  exact ⟨post, retires ▸ runs⟩

/-- A host-call row executes and keeps Sail registers, RAM bytes and virtual
registers. HostIO can append to the advice tape. The register-table increment
still needs a separate argument. For example, an advice-write call may append
bytes while preserving every register. -/
theorem host_call_exec_sail_frame
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (answer : BitVec 64)
    (instruction : run.bytecode[next].instruction = .VirtualHostIO)
    (advice : run.bytecode[next].instruction.RuntimeAdvice) :
    ∃ post, execWithTapeAnswer
        (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre =
        .ok RETIRE_SUCCESS post ∧ post.sail = pre.sail ∧
        post.vregs = pre.vregs := by
  obtain ⟨post, executes⟩ := execHostIO_succeeds pre present
  have frame := execHostIO_keeps_state pre post _ executes
  refine ⟨post, ?_, frame.1, frame.2⟩
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice (by rw [instruction]; rfl),
    instruction]
  simpa only [execWithTapeAnswer, execInstr] using executes

end JoltConstraints.Soundness
