# VirtualHostIO after Jolt #2410

Date: 2026-11-24.
Jolt revision checked: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean baseline checked: `fdfd7891e9ba59d7ab2fae68c9ad8fa74c9e8fe6` on `split/b-bytecode`.
The changes are in `3cefd41` (model and first proofs), `9b9948c` (proof fixes), and `3b49f8a` (the validation record in this report).
`lake build JoltBytecode` is green; see Validation.
This is an ordinary source review, not the separate Claude audit required before Ari's approval.

## Pinned tracer behavior

I read the pinned files with `git show ff6fc6568:<path>` in the read-only Jolt checkout.
All paths in this section are relative to that checkout.

`tracer/src/instruction/virtual_host_io.rs`, `VirtualHostIO::exec`, lines 19–38, reads the low 32 bits of x10 as the call ID.
Advice calls use all 64 bits of x11 and x12 as pointer and length.
Other calls truncate x11, x12 and x13 to 32 bits for pointer, length and event.
Unknown call IDs do not invoke any handler or read memory.
The constants come from `jolt-platform/src/advice.rs`, `cycle_tracking.rs` and `print.rs`.

`tracer/src/emulator/host_io.rs`, `read_host_bytes`, lines 51–87, first computes `ptr.checked_add(len)` and requires the exclusive end to be at most `address_limit`.
A zero length succeeds only after that range-end check and performs no readability check or load.
For a nonempty range the tracer checks readability of the whole interval, then attempts to reserve its output capacity, then loads in ascending address order.
An unreadable or overflowing range appends no bytes.
If a load unexpectedly returns `None` after the preflight check, the tracer truncates the buffer to its original length.
The complete append is therefore all-or-nothing.
The string limit is `HOST_STRING_ADDRESS_LIMIT = 2^32`; advice passes `u64::MAX`.
In particular, the exclusive advice end cannot equal `2^64`.

`tracer/src/emulator/mmu.rs`, `HostMemory for Mmu`, lines 1076–1096, defines readability as normal guest-load return at every address in the range.
The pinned implementation checks identity translation and its effective-address range through `identity_loads_succeed`.
`load_host_byte` calls the guest `Mmu::load` and returns its byte on success.
The Lean model follows the requested abstraction through its own guest load, rather than introducing a second set of memory-region checks.

`tracer/src/emulator/cpu.rs`, lines 1116–1230, implements the paths below.

| Call/path | Memory access and host effect | Guest-visible effect |
| --- | --- | --- |
| Cycle marker during replay | Return before event processing or memory reads. | None. |
| Live cycle event other than 1 or 2 | Log and return before reading the label. | None. |
| Live cycle start, event 1 | Read the complete bounded label, convert lossy UTF-8, reserve marker storage, restart an existing marker or insert a new one. | None. |
| Live cycle end, event 2 | Read the complete bounded label, convert lossy UTF-8, remove/report an active marker or warn if absent. | None. |
| Print during replay | Return before event processing or memory reads. | None. |
| Live print event other than 1 or 2 | `print_terminator` returns `None`; log and return before reading the message. | None. |
| Live print event 1 | Read the complete bounded message, then write lossy UTF-8 with an empty terminator. | None. |
| Live print event 2 | Read the complete bounded message, then write lossy UTF-8 followed by a newline. | None. |
| Advice, live or replay | Read the complete u64-bounded range directly onto the advice tape; the handler has no replay guard. | Append precisely the accepted bytes, leaving the read cursor unchanged. |
| Rejected range | Log the error where applicable and return. | No tape append or other guest change. |

`Cpu::read_host_string` first calls `read_host_message`, then performs fallible lossy UTF-8 conversion.
`read_host_message` starts an empty buffer and uses the 32-bit string address limit.
Print failures from stdout and marker/log bookkeeping do not become guest exceptions.
Advice rejection warnings are suppressed in replay by `warn_ignored_host_call`; advice appending itself is not suppressed.

## Lean model and interfaces

`JoltBytecode/JoltISA/Core.lean:50`, `JoltHostIOConfig`, retains only `mode : JoltHostIOMode := .live`.
The former `overflowChecks : Bool := false` field is removed.
Both mode/config docstrings now describe advice's replay behavior.
No state restriction or new theorem hypothesis replaces the field.

`JoltBytecode/JoltISA/HostIO.lean:57`, `readHostBytes`, checks the mathematical exclusive end against both `2^64 - 1` and its explicit address limit before the zero-length case.
For a nonempty range, `List.all` queries load success at every address before `List.mapM` collects the bytes in ascending order.
A failed check or collection returns `none`, without exposing any partial array to a caller.
A successful result contains the original array followed by exactly the collected bytes.
The load operation is pure and explicit: `Nat → Option (BitVec 8)`.
Each query denotes guest-load acceptance and its result, rather than performing a stateful MMU operation.

`JoltBytecode/JoltISA/HostIO.lean:77`, `execHostIOWith`, reads the register arguments from the initial state with `sourceValue`.
It appends only a successful advice buffer and does so in either mode.
For print and cycle markers it checks replay, call ID and valid event before the bounded byte query.
The two accepted event sets coincide; their differing host output is outside Sail state.
Unknown calls, unknown events and rejected ranges all reach `RETIRE_SUCCESS`.
The caller passes an empty buffer, then appends it to the old tape; this equals the tracer's append directly into the tape because the buffer is accepted atomically.

`JoltBytecode/JoltISA/HostIO.lean:104`, `execHostIO`, supplies `Mmu.load?`.
In `DeviceMemory.lean`, `Mmu.load` succeeds with a byte and unchanged state exactly when `Mmu.load?` returns that byte.
Consequently host readability uses the model's complete traced guest-byte acceptance, including its containing-doubleword checks, not merely raw byte mapping.
No separate permissive host-memory predicate was added.

`JoltBytecode/JoltISA/HostIO.lean:111`, `execHostIO_result`, states the result shape: every host call retires successfully, and the post-state is either the pre-state or the pre-state with bytes appended to the advice tape (read cursor unchanged).

```lean
theorem execHostIO_result (state : SailJoltState) :
    execHostIO state = .ok RETIRE_SUCCESS state ∨
      ∃ bytes, execHostIO state = .ok RETIRE_SUCCESS
        { state with adviceTape :=
            { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }
```

`JoltBytecode/JoltISA/HostIO.lean:132`, `execHostIO_succeeds`, follows from it and exports the whole-run interface:

```lean
theorem execHostIO_succeeds (state : SailJoltState) :
    ∃ post, execHostIO state = .ok RETIRE_SUCCESS post
```

It has no register, address, event, mode or execution-prefix premise.
A whole-run proof can instantiate it with its next pre-state in place of the current `HostCallsSucceed` assumption.
This task does not remove that restriction or edit its consumers in JoltConstraints.

## Changed and removed statements

No retained theorem statement is weakened or acquires a premise.
The following public definition signatures change as part of the authorized model replacement.

Old `readHostBytes`:

```lean
def readHostBytes (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) : Nat → Array (BitVec 8) →
      JoltMonad (Option (Array (BitVec 8)))
```

New `readHostBytes`, `HostIO.lean:57`:

```lean
def readHostBytes (loadByte : Nat → Option (BitVec 8))
    (pointer count addressLimit : Nat) (bytes : Array (BitVec 8)) :
    Option (Array (BitVec 8))
```

Old `execHostIOWith`:

```lean
noncomputable def execHostIOWith
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult)) :
    JoltMonad ExecutionResult
```

New `execHostIOWith`, `HostIO.lean:77`:

```lean
noncomputable def execHostIOWith
    (loadByte : SailJoltState → Nat → Option (BitVec 8)) :
    JoltMonad ExecutionResult
```

`execHostIO : JoltMonad ExecutionResult` retains its signature and changes its behavior as described above.
The call-ID definitions retain their signatures and values.

The private `InstructionFrame.execHostIO_rule` moves from baseline `InstructionFrame.lean:290` to `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:264`.
Its statement is unchanged: `(rules : NonStoreRules relation) → StatePreservation.Preserves relation execHostIO`.
Its proof now cases on `execHostIO_result` and uses `rules.refl` or `rules.append`.

The following private helper statements are deleted because their only purpose was to frame the former stateful byte reader; there is no replacement stateful reader to frame.
Their consequences are covered by the retained host-call frame proofs.
Locations below refer to baseline `fdfd789`.

```lean
-- JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:264
private theorem load_rule (rules : NonStoreRules relation) (address : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.load address)

-- JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:271
private theorem readHostBytes_rule (rules : NonStoreRules relation)
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    StatePreservation.Preserves relation
      (readHostBytes Mmu.load overflowChecks incrementAfterLast pointer n bytes)

-- JoltBytecode/Step/Frame.lean:255
private theorem frames_load (address : BitVec 64) : Frames (JoltISA.Mmu.load address)

-- JoltBytecode/Step/Frame.lean:304
private theorem frames_readHostBytes
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (hload : ∀ address, Frames (loadByte address))
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Frames (JoltISA.readHostBytes loadByte overflowChecks incrementAfterLast pointer count bytes)
```

`Step.frames_hostIO` moves from baseline `Step/Frame.lean:340` to `JoltBytecode/Step/Frame.lean:317`.
Its statement remains `Frames JoltISA.execHostIO`, including error-result framing, and its proof no longer needs a byte-load induction.
It also cases on `execHostIO_result`: the unchanged state frames by reflexivity, and the tape append leaves Sail registers equal.
All exported generic instruction frame statements retain their types.
`execHostIO_result` and `execHostIO_succeeds` are the only newly added theorem statements.

### Changes made while fixing the build

`3cefd41` did not build. The fixes changed proofs and added one lemma; no theorem statement was weakened or changed.

- `execHostIO_succeeds`: the statement is unchanged. The original `simp only [...]; repeat' split` proof left `getThe` unfolded and could not split an `if` applied to the state. It now follows from `execHostIO_result`.
- `execHostIO_result`: new public theorem (statement above). Its proof unfolds the handler and case-splits on the advice call ID and the `readHostBytes` result.
- `execHostIO_rule` and `frames_hostIO`: statements unchanged. The `preservation_auto` and `jolt_frame` tactic proofs from `3cefd41` got stuck on the `let` bindings in the new handler; both proofs now case on `execHostIO_result`.

## Explicit modelling choices and limits

Host allocation succeeds in this model.
This includes byte-buffer `try_reserve`, the host's usize conversion for the u64 length on the 64-bit tracer host, lossy-string storage and marker-table storage.
Actual host-memory exhaustion can make the tracer ignore an otherwise valid advice write; the model chooses the successful allocation behavior.
The pinned host-I/O module also notes that host-memory exhaustion can abort memory-access bookkeeping or the tracing subscriber.
Those host failures are not represented as guest execution outcomes.

Stdout contents and write errors, logs, cycle counts, active marker tables and sparse-memory/checkpoint bookkeeping remain outside Sail state.
The pure range query therefore cannot model an independently failing load after a successful preflight on unchanged guest memory.
With `Mmu.load?`, preflight and collection use the same pure function on the same state, so they agree at every address.
If the supplied query returns `none`, collection still returns no partial buffer.
This is the guest-state projection requested here, not a specification of host resource availability or the emitted output stream.

Jolt's CPU has a full architectural register array.
The Lean state stores Sail registers in a potentially partial map.
Host ABI reads now use `sourceValue`, which agrees with successful operand reads and defaults absent entries to zero.
This makes totality unconditional even for partial maps that do not correspond to an initialized tracer CPU.
No ordinary instruction's register access is changed.

Changing the host-reader API requires the later JoltConstraints step to update its byte-reader frame and tape-swap helpers as well as remove `HostCallsSucceed`.
Those files are outside this task's writable scope and were not edited.

## Validation

`~/claude-work/track-t-build.sh lake build JoltBytecode` is green (log `.hostio-build-4.log`, untracked):

```
✔ [9364/9365] Built JoltBytecode (32s)
Build completed successfully (9365 jobs).
```

The touched files add no new warnings; `InstructionFrame.lean` keeps two older warnings at lines 141 and 211.
`#print axioms` on `JoltISA.execHostIO_succeeds` and `JoltISA.execHostIO_result` reports `[propext, Classical.choice, Quot.sound]`.
Against `fdfd789`, the diff touches only `JoltBytecode/` and `reports/`, adds no `sorry`, `admit`, `native_decide`, `bv_decide`, `decide +kernel`, `axiom` or `maxHeartbeats`/`maxRecDepth`/`synthInstance` option, and passes `git diff --check`.
