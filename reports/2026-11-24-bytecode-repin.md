# JoltBytecode re-pin to ff6fc6568

Date: 2026-11-24.
Jolt revision checked: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean baseline: `5d7d40eb7ca66229a5d3fc4c3e7438ce469dae0b`.
Lean code revision: `647463411983f4637e482ce83dab2486c38cc46a`, on `split/b-bytecode`.
The report commit changes documentation only.
I read the detached Jolt checkout, its three supplied specifications, and the affected Lean definitions and consumers.
This is an ordinary source review, not an independent blind review.

The complete `JoltBytecode` build passed in `.repin-propagation-13`.
The final post-commit harness checks passed with exit code 0 at 01:51:06 on 2026-11-24.
No files under `JoltConstraints/` or `LeanRV64D/` changed.

## Changes by file group

| Files | Result |
| --- | --- |
| `JoltISA/JoltDevice.lean` | Replaced flag-word layout and device-owned arrays with the pinned checked layout and shared-memory byte interfaces; added initial memory and final output extraction. |
| `JoltISA/Core.lean`, `DeviceMemory.lean` | Added the code-word interval and halt kind to CPU state; used layout-derived padded RAM bounds and value-preserving code/input/advice/canary protection. |
| `JoltISA/Instruction.lean`, `Semantics.lean`, `Expansions/System.lean` | Added success/panic rows, the side-effecting destination rewrite, one-row EBREAK lowering, link/PC effects and halt recording. |
| `Decode/Jolt.lean`, `Decode/Execute.lean` | Added exact success decoding and a standard/custom source result, executable source bodies and a guarded source tick. |
| `JoltISA/Values.lean`, `StoreFamily/Splice.lean` | Put shared splice definitions in one dependency location; defined actual containing-doubleword store values and width-polymorphic AMO values. |
| `Assumptions.lean`, `Bundles.lean`, `RiscvInstruction.lean`, `ProofSupport/BundleLemmas.lean` | Updated RAM acceptance to the padded bound and actual stored value; distinguished source store widths while checking the eight-byte lowered write. |
| `ProofSupport/Memory/MmuJolt.lean`, `Memory/Write.lean`, `InstructionLemmas/SD.lean` | Re-proved memory reductions with protected-value acceptance and transport through unchanged MMU setup and memory. |
| `ProofSupport/InstructionFrame.lean`, `DeviceFrame.lean`, `Basic.lean`, `ProtectedVRegWrites.lean` | Generalized the common frame to memory-preserving Sail effects, checked MMU stores and halt metadata; proved static setup and protected-memory invariants for every row and program. |
| `Instructions/StoreFamily/{ProgramBlocks,Sb_main,Sh_main,Sw_main}.lean`, `Instructions/Natives/Sd.lean` | Propagated acceptance of each actual merged store through the narrow-store reductions and native SD equivalence. |
| `Instructions/AtomicFamily/{Dword,Word,WordLane,WordProgram,WordSelectLane,WordSelectRust,Amoswapw}.lean` and the nine dword AMO exports | Propagated acceptance of the computed AMO result; converted lane/splice representations and transported layout, code guard and memory facts from execution certificates. |
| `Instructions/System/{Sc,ScDword,ScWord}.lean` | Checked acceptance of the actual selected SC doubleword, including the unchanged value written back by failed SC. |
| `Instructions/LoadFamily/{LB_main,LW_main}.lean`, `Step/Frame.lean` | Used padded load bounds and the common raw-store register frame. |

Paths in this table are relative to `JoltBytecode/`, except where a group already names its subdirectory.
The code commit changes 48 Lean files.

## Layout and shared memory

`MemoryLayout.new` (`JoltISA/JoltDevice.lean:139`) follows `common/src/jolt_device.rs` (`MemoryLayout::try_new`, lines 488–630).
It aligns capacities, admits advice sizes, reserves eight bytes after outputs before power-of-two padding, places the larger advice region first, computes stack/heap ends with checked arithmetic, and admits the result through `max_ram_k?`.
The no-I/O case reserves eight bytes below RAM, rather than the previous two flag words.
`io_end` is `output_end`.
The layout has no panic or termination address.
The device has exactly `memory_layout` and the Boolean `panic` claim.

The domain follows `MemoryLayout::max_ram_k` and `ram_size` (lines 650–765).
`Mmu.ram_backing_end` reads its bound from the device's layout.
Heap padding is part of the mapped RAM backing, and the gap between `io_end` and RAM is ordinary readable/writable memory.
The arithmetic models the 64-bit host sizing used by the pinned tracer; layout errors erase their diagnostic variants to `none`.

`JoltDevice.initialMem` (`JoltISA/JoltDevice.lean:255`) starts with a supplied program/RAM map, initializes the I/O window to zero, then writes actual input, trusted-advice and untrusted-advice bytes at their layout addresses.
Oversized arrays fail.
`JoltISA.initialState` (`JoltISA/Core.lean:100`) also installs the code interval and clears the halt and panic metadata.
`JoltDevice.outputsOf` (`JoltISA/JoltDevice.lean:269`) reads the full configured output capacity from final shared memory.
`outputsOf_size` proves that exact capacity.
Public-claim trailing-zero trimming remains a caller operation.

The code span is `SailJoltState.codeRegion`, outside `JoltDevice`.
`codeRegionOf` (`JoltISA/Core.lean:79`) follows `code_region` and `source_word_intervals` in `crates/jolt-program/src/preprocess/ram.rs`.
It ignores address-zero padding, checks source extents, rounds to full words, and protects the entire span between the first and last source instructions.
The other protected intervals derive from `memory_layout`; separate copies of those intervals are unnecessary.
`protected_byte` tests the containing word, including any word overlapping the canary.
`protected_store_ok` compares every touched protected byte with its previous zero-default shared-memory value.
This is the bytewise form of the pinned tracer's masked first/last-word comparison for its supported one-, two-, four- and eight-byte stores.

`protected_store_byte_iff` (`ProofSupport/Memory/MmuJolt.lean:97`) characterizes the one-byte check.
`store_raw_existing` (line 107) proves that an accepted address permits writing its existing byte, including protected addresses.
`store_raw_protected` and `store_doubleword_protected` derive preservation from successful checked stores.
`execInstr_memory` and `execProgram_memory` (`ProofSupport/DeviceFrame.lean:81,95`) preserve every original protected byte across successful execution.
The invariant uses shared memory, replacing claims about separate device arrays.

## Store-premise decision and statement inventory

The previous address-only acceptance premise was false for value-changing code stores at the new pin.
For example, an aligned address can be backed and lie before the canary while holding protected instruction bytes.
Writing zero there passes the address check but fails `assert_write_protected_store`.
The user's decision authorized replacing that premise with its actual value-dependent meaning.

The exact old and new declaration text, with source locations, is in [the statement inventory](2026-11-24-bytecode-repin-statements.md).
It includes 63 directly changed theorem headers, the changed bundle fields, and the declarations whose bundled or aliased premises changed without a textual header change.
It also identifies strengthened prelude conclusions, new interfaces and replaced array interfaces.
In particular, the inventory includes `Natives.sdInstrEqSailStatement`, the narrow-store statement definitions and equivalence theorems, the AMO exports, SC statements and the generic dispatch/step users of `equivAssumptions`.

The old `JoltRamStoreOk addr js` required a start below `heap_end` and `outside_canary`.
The new `JoltRamStoreOk addr js value width` requires a start below the padded backing end and `protected_store_ok js addr.toNat value width = true`.
The bundle is the RAM acceptance component; its existing callers still supply RAM membership, alignment, Sail access checks and populated Sail bytes separately.
The removed canary exclusion is replaced by the same value-preservation rule as code, inputs and advice.
No new exclusion of protected addresses was added.
For SB/SH/SW and word AMOs, the checked value is the complete merged doubleword that their rows actually write.
For SC it is the selected original or replacement doubleword.

The former device `Same` relation compared layout plus input/advice arrays.
Its non-memory part now compares layout, while `SetupSame` also compares the CPU code interval and `Mmu.ProtectedMemory` compares protected shared-memory bytes.
The general Sail frame now asks only for memory-preserving Sail effects, and its store obligation describes checked doubleword execution.
The frame includes a halt obligation because halt execution may change the device's panic claim.
Arbitrary-intermediate-state AMO helpers now require agreement of the code interval as well as layout; their concrete callers derive it from existing execution certificates.
No exported instruction-equivalence theorem acquired an unrelated assumption.

## Halt model

The model adds `halted : Option JoltHaltKind` to CPU state.
The two kinds are success and panic.
The decoder accepts success only as `0x0000305B`; `decodeJoltSuccess_some_iff` (`Decode/Jolt.lean:211`) proves that exact characterization, including zero reserved operands.
The ordinary Sail decoder and its existing agreement theorem retain their standard-instruction scope.
The new `SourceInstruction` result handles the custom success instruction separately.

The decoded success destination is x0, which the pinned expansion rewrites to instruction temporary v40.
Both halt row kinds perform the side-effecting destination rewrite.
EBREAK lowers to a single Panic row with that scratch destination.
`execHalt` (`JoltISA/Semantics.lean:58`) writes the already advanced PC as the link, sets nextPC to the source address, then records the halt kind and corresponding panic claim.
`execHalt_vreg_run` (`ProofSupport/DeviceFrame.lean:151`) proves those effects without a memory change.
This follows `Cpu::halt` (`tracer/src/emulator/cpu.rs:549`) and `tracer/src/instruction/jolt_success.rs`.

`JoltExecution.run` guards an instruction-body execution after a halt.
`Decode.SourceInstruction.tick` (`Decode/Execute.lean:470`) guards the entire source step, including Sail bookkeeping.
`SourceInstruction.tick_halted` (line 477) proves that every later tick leaves the complete state unchanged.
Raw `execInstr` and `execProgram` remain local interpreters for instruction proofs.
Their callers use admitted source expansions, which cannot contain a halt within a multi-row sequence.
The semantics module documents this boundary.

The Lean model records `panic` eagerly at the halt.
The tracer records the CPU halt kind immediately, then derives `JoltDevice.panic` when `Emulator::take_jolt_device` extracts final I/O (`tracer/src/emulator/mod.rs:137`).
Both yield the same final claim, backed by no memory word.

## Validation and trust

I ran only `track-t-build.sh lake build JoltBytecode` for compilation.
Build `.repin-propagation-13` succeeded with 9365 jobs, including the same-value raw-store theorem, halt execution theorem, all word/dword AMOs, SC, decoder and step consumers.
I removed the temporary axiom-print commands after that build; the final check rebuilt the committed files without them.
No proof, test or build target was bypassed to obtain the green result.

The temporary `#print axioms` checks gave:

| Declaration | Axioms |
| --- | --- |
| `JoltIOSetupFrame.execProgram_memory` | `propext`, `Classical.choice`, `Quot.sound` |
| `JoltISA.execHalt_vreg_run` | `propext`, `Classical.choice`, `Quot.sound` |
| `JoltISA.Mmu.store_raw_existing` | `propext`, `Classical.choice`, `Quot.sound` |
| `Natives.sdInstr_eq_sail` | `propext`, `Classical.choice`, `Quot.sound` |
| `Decode.decodeJoltSuccess_some_iff` | `propext` |
| `Decode.SourceInstruction.tick_halted` | `propext`, `Classical.choice`, `Quot.sound` |

There are no new admissions, axioms, prohibited decision procedures or resource-limit raises.
The final harness scan passed every check: the prohibited-token diff scan against `5d7d40e`, absence of removed flag identifiers in the two memory-model files, presence of success decoding, unchanged frozen directories, and a committed `JoltBytecode/` tree.
The same final command rebuilt `JoltBytecode` successfully (9365 jobs).
`git diff --check` also passed.
No push, branch switch or PR action occurred.

The build log reports module wall times rather than per-declaration timings.
In the successful run, changed modules exceeding about ten seconds were `JoltISA.Semantics` and `Memory.MmuJolt` (11 seconds each), `Step.Frame` (20 seconds), `AtomicFamily.Amoandd`, `Amomaxd`, `Amomaxud` and `Amomind` (14 seconds each), `Amominud` and `Amoord` (17 seconds each), and `Amoaddd` (22 seconds).
The root `JoltBytecode` module took 19 seconds.
These timings include import/loading and concurrent build effects; they do not identify an individual proof taking that long.
The new common frame and protected-memory frame modules took 8.2 and 4.1 seconds respectively.
I did not raise any limit or claim per-proof profiling from those module timings.

## Scope and remaining composition work

The requested RV64 data-access and halt semantics have no known fidelity gap against the inspected pin.
`none` in the optional byte helpers, or a monadic error in the existing instruction APIs, represents a tracer fault; diagnostic strings and state after a panicking partial access are not public run results.
The shared map uses zero defaults for untouched mapped bytes, matching the tracer's zero-filled storage.

The source-step API still takes a decoded instruction from its caller, as the existing step layer did.
It does not implement the tracer's fetch cache or store `CodeGuard.instructions`, the separate list of permitted source starts.
The next whole-run layer must supply the decoded instruction at the fetched PC and the admitted layout/program image, then use the guarded tick and final-memory extraction APIs.
This migration proves no whole-run soundness theorem and changes no constraints or Sail-generated files.

The closing report and statement inventory consolidate the superseded November 23 working and blocker reports.
Temporary build logs, completion markers and audit scripts were removed after their results were recorded here.
