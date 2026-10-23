# Device-memory staging report

Work was done on `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public` on 2026-10-23.
The new module stages `ld_device_step` and `sd_device_step`, each parameterized by seven disjoint device regions.
Both steps remain `sorry`; no step was proved.
The code audit found no counterexample under their current hypotheses and restrictions.
This is a staging result, not a proof that the restrictions suffice for all device steps.
No commit was made by this task.

## Claims checked before staging

I read `AGENTS.md`, `methods/layer6/reuse.md`, `methods/layer6/device-memory.md`, and the requested order-of-work and Layer 5b sections of `methods/soundness.md`.
The Jolt audit used `git show` and `git grep` at the pinned commit `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`.
I found no false claim in the device-memory plan.

| Plan claim | Checked code |
|---|---|
| Existing LD and SD steps cover ordinary RAM | `JoltConstraints/Soundness/Layer5/LoadDoubleword.lean:37`, `ld_ram_step`, and `Layer5/RamStoreAgreement.lean:18`, `sd_ram_step_agreement`, require `RAM_START_ADDRESS ≤ address.toNat` |
| The cut compares all table words except termination | `JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean:53`, `RepresentsPrefix.cutRam` |
| Termination has a separate pre-store zero invariant | `JoltConstraints/Soundness/Layer6/PrefixState.lean:125`, `ExpansionState.terminationWord` |
| The comparison image overlays the final device | `JoltConstraints/witness_helpers/ram_state.lean:87`, `TraceWitness.finalRamWord`, with `overlayRamBytes` at line 47 |
| Device reads and writes differ from ordinary RAM | `JoltBytecode/JoltISA/JoltDevice.lean:203` and `:221`, `JoltDevice.load?` and `store?`, checked against pinned `jolt/common/src/jolt_device.rs`, `JoltDevice::load` and `JoltDevice::store` |
| The restrictions cover attempted accesses, rather than only successful rows | `TracerAddressChecks`, `PanicStoresOne`, and `TerminationThenStall` quantify over `UntrustedAnswerRun.NextStep` |
| The known termination discrepancy remains | `JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean:68`, `:73`, and `:90` establish ignored stores, zero loads, and the differing selected-store table value |

One caller detail matters for staging: `ExpansionState.registers` provides `RegisterAgreementOn ExpansionLive`, not full register agreement.
The new steps therefore use a live-register predicate and require the base operand, and SD's value operand, to be live.
They do not copy the full `RegisterAgreement` premise from the ordinary-RAM steps.

## Source and execution paths

The pinned tracer paths are `jolt/tracer/src/instruction/ld.rs`, `LD::exec`, and `jolt/tracer/src/instruction/sd.rs`, `SD::exec`.
They call the MMU doubleword operations.
In `jolt/tracer/src/emulator/mmu.rs`, `Mmu::load_doubleword_raw` and `Mmu::store_doubleword_raw` process device doublewords through eight byte operations.
`Mmu::assert_effective_address` checks those device byte addresses, and `Mmu::load_raw` and `Mmu::store_raw` also perform peripheral dispatch before calling the device.
The table below refers to these functions and to `JoltDevice::load`, `JoltDevice::store`, and the `is_*` predicates in pinned `jolt/common/src/jolt_device.rs`.

The Lean path is `execWithTapeAnswer` in `JoltConstraints/Soundness/Layer5/TapeSemantics.lean:21`, which uses `execInstr` for LD and SD.
Their interpreter cases are `JoltBytecode/JoltISA/Semantics.lean:427` and `:439`.
The device doubleword operations, byte dispatch, and checks are in `JoltBytecode/JoltISA/DeviceMemory.lean`: `effective_address_ok` at line 41, `load_raw?` at line 75, `store_raw?` at line 90, `load_doubleword` at line 130, and `store_doubleword` at line 147.
These call `JoltDevice.load?` and `store?` at the locations above.
Independent tape answers and runtime advice do not change an LD or SD operation.

The restriction definitions are `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:86`, `TracerAddressChecks`; `Layer5/PanicRestriction.lean:63`, `PanicStoresOne`; and `Layer5/TerminationRestriction.lean:59`, `TerminationThenStall`.

## Per-region check

“Preserves” below describes the audited argument for the staged statement; these preservation proofs remain owed.
Buffer words are packed little-endian, with zero for missing bytes.
The `output` case means the output buffer before the panic word; the classifier tests panic first because Jolt's `is_output` also includes panic addresses.

| Region and operation | Pinned tracer behavior | Lean behavior | Restriction and agreement check |
|---|---|---|---|
| Trusted advice LD | `JoltDevice::load` reads trusted bytes, padding absent bytes with zero | `load?` reads the same array and defaults; the MMU packs eight bytes | Address checks apply; initialized buffer bounds and unchanged advice make the device word equal its final-image overlay; load has zero table update |
| Trusted advice SD | MMU store-address assertion rejects it | `effective_address_ok ... true` is false; `store?` provides no advice write | Excluded by `TracerAddressChecks` before execution; this specialization of the SD statement has inconsistent hypotheses |
| Untrusted advice LD | Reads untrusted device bytes with zero padding | Reads `device.untrusted_advice` with the same defaults | Preserves by the same buffer argument; these bytes are distinct from independent execution-tape answers |
| Untrusted advice SD | MMU store-address assertion rejects it | No permitted device-store branch | Excluded by `TracerAddressChecks` |
| Input LD | Reads public input bytes with zero padding | Reads `device.inputs` with the same defaults | Preserves the input overlay and all table words; input lengths are bounded at initialization |
| Input SD | MMU store-address assertion rejects it | No permitted input-store branch | Excluded by `TracerAddressChecks` |
| Output LD | Reads output bytes written so far; missing bytes are zero | Same buffer read and defaults | Preserves because the current output image equals the table, including any partial word and unwritten words |
| Output SD | Writes eight bytes, growing outputs and zero-filling gaps; enforces `output_end` | `store?` grows with zeros and writes bytes | Preserves the selected output word and all other words; generated layouts have `output_end = panic`, so the model's special panic handling and the tracer's output bound agree |
| Panic LD | Every byte is the panic flag, so a set flag yields `0x0101010101010101` | Identical repeated-byte read | `PanicStoresOne` excludes a panic load after any panic store; before a store the initialized reachable device has `panic = false`, so device and table both read zero |
| Panic SD | Writing the first byte sets the flag regardless of value; remaining panic bytes are ignored | Same flag update and ignored writes | `PanicStoresOne` forces the whole source word to be 1; table update and normalized final panic image are both 1; repeated permitted stores still agree |
| Termination LD | Always reads zero | Always reads zero | `TerminationThenStall` excludes loads after any termination store; before one, `terminationWord` supplies table zero |
| Termination SD | Ignores all eight writes | Leaves the state unchanged | May store any word; cut agreement excludes this index, and the zero obligation becomes vacuous once it is stored; later loads are excluded by `TerminationThenStall` |
| Unmapped LD | Some low addresses read zero; peripheral ranges panic; the I/O gap may fail byte checks | The same distinctions occur in `load_raw?`, beyond `load?` alone | Under the full staged hypotheses only address zero remains; its unselected RAM read is zero, and all table entries are unchanged; details below |
| Unmapped SD | No permitted device-store region, or an unsupported peripheral dispatch | Rejected by the corresponding checks or dispatch | Excluded by `TracerAddressChecks`; an address outside all six device regions cannot satisfy the write predicate |

### Unmapped addresses and peripheral dispatch

`TracerAddressChecks` alone does not exclude every unsupported peripheral load.
For example, the eight effective-address checks at `0x10000000` can all pass, while `Mmu::load_raw` and Lean's `load_raw?` reject the UART range.
This is not a counterexample to the staged step: it also needs the selected witness equations, actual operand agreement, and the generated layout.

`MemoryLayout::try_new` at the pin rounds I/O to a power of two and rejects a padded start at zero.
Lean's `MemoryLayout.new` and `adviceRegions` implement the same condition.
Consequently, every admitted layout's lowest address is at least `0x40000000`, above all five rejected peripheral ranges.
The RAM-address equation and selector facts force every nonzero actual address to be the layout base plus eight times an in-domain index.
The actual-word encoding comes from `ld_address_encoded` or `sd_address_encoded` with the existing `RamRegionFits` assumption; it must not be inferred from a field equality without this bound.
Thus nonzero low and peripheral addresses are excluded by the constraints.

Within the allocated device span, aligned words belong wholly to one buffer or one flag word.
An aligned word beginning at or after `io_end`, below ordinary RAM, fails the eight-byte address checks: even when its first byte equals the inclusive MMU limit, a later byte exceeds it.
Address zero lies outside every device region, passes the load checks, and returns zero.
Its zero RAM-address column selects no RAM index, so the constrained read is also zero.
No additional peripheral or unmapped-address restriction was added.

### Termination and panic invariants

The existing termination obstruction remains real: storing 1 leaves the table entry at 1 but readable device memory at zero.
The staged agreement deliberately excludes that word, just as `RepresentsPrefix.cutRam` does.
Before any termination store, `TerminationTableZero` expresses exactly the existing `terminationWord` field at the current cut.
After a nontermination step that condition persists; after a termination SD, the extended-prefix condition has a witnessed store and imposes no zero claim.
`TerminationThenStall` excludes every later termination LD and constrains later jumps for the separate stopping proof.
The SD statement does not assume termination stores write 1, nor that the next instruction is immediately a jump.

Panic uses the normalized image word, not readable memory after the flag is set.
The stored word 1 therefore agrees with `finalRamWord`'s panic value 1.
Later loads of that region are excluded by `PanicStoresOne`.
The run certificate matters here: a bare device with `panic = true` and no execution history would not justify the load-zero claim.

## New declarations

All names in this table are in namespace `JoltConstraints.Soundness` and in `JoltConstraints/Soundness/Layer5/DeviceMemory.lean`.

| Declaration | Line | Purpose |
|---|---:|---|
| `DeviceMemoryRegion` | 17 | Seven region cases, including unmapped addresses |
| `deviceMemoryRegion` | 27 | Classify an address with panic and termination precedence |
| `DeviceRamAgreement` | 46 | The below-RAM, nontermination part of the existing cut comparison |
| `TerminationTableZero` | 62 | Zero at the layout's termination index |
| `DeviceMemoryStepAgreement` | 77 | Shared next-cycle and final-column memory conclusions for an appended row |
| `ld_device_step` | 103 | Staged load theorem, universally quantified over the region |
| `sd_device_step` | 167 | Staged store theorem, universally quantified over the region |

`JoltConstraints.lean:55` imports the new module.
The region parameter gives seven specializations of each staged theorem without fourteen repeated signatures.
The LD conclusion explicitly distinguishes panic, termination and unmapped reads as zero.
The SD conclusion explicitly permits only output, panic and termination; panic forces source word 1 and the precise flag update, and termination forces `post = pre`.

### Exact agreement definitions

`DeviceRamAgreement values trace` states, for every in-domain index whose absolute address is below `RAM_START_ADDRESS` and whose index differs from termination:

```lean
values index = ((TraceWitness.finalRamWord trace index.val).toNat : F)
```

The absolute address is `ramLowestAddress trace.initialState.jolt_device.memory_layout + 8 * index.val`.
For initialized executions, generated layout geometry and the preserved bounds on device buffers prevent overlays from reaching ordinary RAM.
Under those execution facts, this device relation together with `OrdinaryRamAgreement` at the final state covers all nontermination words in `RepresentsPrefix.cutRam`.
No composition theorem was proved in this staging task.

`DeviceMemoryStepAgreement witness t trace step storedTermination` uses the trace with `step` pushed onto its rows.
At a successor cycle it requires ordinary-RAM agreement, device agreement, and termination-table zero if `storedTermination` is false.
At the last cycle it requires ordinary-RAM and device agreement with `RamValFinal`; the original invariant has no next-cycle termination-zero field there.
For LD, `storedTermination` is the existence of an earlier termination store.
For SD, it is that existence or the current address touching termination.

### Staged step statements and caller premises

Both steps take the selected bytecode row, a real `UntrustedAnswerRun`, bytecode equality, a cycle whose value is `run.rows.size`, and `run.NextStep next pre`.
Their register premise is `RegisterAgreementOn live witness t pre`, with explicit liveness of the operands read.
They take current ordinary-RAM agreement, current device agreement, and the conditional zero termination word.
The address must be below ordinary RAM; its `region` is identified by `deviceMemoryRegion`.
Neither theorem assumes that the attempted instruction succeeds.

Both use only `RamRegionFits`, `TracerAddressChecks`, and `PanicStoresOne` from the instance assumptions and restrictions.
LD additionally uses `TerminationThenStall` to exclude a termination read after a store.
SD needs no termination restriction for its local agreement result because the termination index is excluded and its post-store zero condition is vacuous.

LD concludes existence of a word equal to the actual device doubleword read, the actual-address encoding and `RdWriteValue` encoding, successful execution to `afterWriteDst`, next-cycle register agreement on the old live set plus the destination, and `DeviceMemoryStepAgreement`.
SD concludes existence of the successful post-state, the region-specific facts above, actual-address and `RamWriteValue` encodings, preservation of live-register agreement, and `DeviceMemoryStepAgreement`.

`row_step` can supply these premises as follows:

| New step premise | Existing caller evidence |
|---|---|
| `regionFits` | `assumptions.ramRegionFits` |
| Address, panic and termination restrictions | Corresponding fields of `restrictions` |
| Run, cycle, selected slot and next-row position | `ExpansionState.next` and `t = ⟨run.rows.size, bound⟩` |
| Bytecode equality | Determinism of `run.expands` and `context.expands` |
| `NextStep` | The ready clause in `state.next`, `state.noEarlierStop`, and the supplied honest-advice hypothesis |
| Live-register agreement in `pre` | `state.registers`, with `RegisterAgreementOn.advance_pc` when preparing a source boundary |
| Operand liveness | `expansion_sources_live`, `JoltConstraints/Soundness/Layer6/PlainRow.lean:163`, applied to the selected LD or SD operands |
| Device and ordinary memory agreement | Restrictions of `state.represents.cutRam`, with final-state/layout and buffer-frame facts for the ordinary portion |
| Conditional termination zero | `state.terminationWord` |
| Region equality | Choose the result of `deviceMemoryRegion` |

These are local proof obligations when wiring the caller; they were checked against its fields but not proved here.
The statements do not demand full agreement on dead instruction temporaries.
They retain actual initialization and execution certificates through the run, and use `RamRegionFits` for field-to-word address reasoning.
They introduce no inference from an isolated post-state, no per-row compression assumption, and no assertion that equal source addresses identify bytecode rows.

## Reuse for the future proofs

The address and selection chain is already available in `Layer5/MemoryAddress.lean`, `ld_address_encoded` and `sd_address_encoded`; `Layer5/RamAlignment.lean`, `ramAddress_mask_aligned`; and `Layer1/Ram.lean` and `Layer3/Address.lean`, the selected-address and remapping lemmas.
`Layer3/Access.lean`, `ram_write_effect_zero_of_load`, supplies LD's zero table effects.
`Layer3/Updates.lean`, `ramVal_succ_of_selected` and its final-column counterpart, supplies SD's table update.
`Layer5/LookupWrite.lean`, `registerWriteOn_step`, and `Layer5/Registers.lean`, `RegisterAgreementOn.noWrite`, provide the register conclusions.

Use `JoltIOSetupFrame` and the general device-relation preservation theorem in `Layer5/TapeSemantics.lean` for unchanged layout and buffers, and for the history argument that panic is false before any panic store.
The checked-layout geometry in `JoltConstraints/layout_facts.lean` covers aligned region boundaries, ordering, buffer capacities and word indices.
`finalTraceState_push` already exists in `Layer6/PlainRow.lean:450`; this task did not edit it.
Byte packing, output growth, the special flag words, and the synthesis of these facts into the staged postconditions remain to be proved.
The full cut-agreement and row-append wiring also remains for the caller's proof.

## Validation

The requested module build passed all 8640 jobs:

```text
lake build JoltConstraints.Soundness.Layer5.DeviceMemory
```

The new module built in 4.3 seconds and reported exactly its two intended `sorry` warnings.
No full-repository build was required by this staging plan or attempted in this task.
The other agents' unfinished modules were not edited.

A successful `lake env lean --stdin` check evaluated a concrete generated layout with advice capacities 8 and 8, input capacity 8, output capacity 16, program size 8, and zero stack and heap sizes.
Its trusted, untrusted, input, output, panic, termination and I/O-end addresses were respectively `0x7fffffc0`, `0x7fffffc8`, `0x7fffffd0`, `0x7fffffd8`, `0x7fffffe8`, `0x7ffffff0`, and `0x7ffffff8`.
The initial buffers were trusted `[5]`, untrusted `[6]`, input `[7]`, empty outputs and `panic = false`.
These were executable checks of the device functions and address predicates, not proofs of steps or constructed satisfying witnesses.

| Check | Observed result |
|---|---|
| Load each partial advice/input word | 5, 6 and 7 respectively |
| Store-address checks for advice/input | False |
| Store word 7 to the second output word | Sixteen output bytes: eight zeros, then `7,0,0,0,0,0,0,0`; reading the second word returns 7 |
| Store word 1 to panic | Flag becomes true; device word read is `72340172838076673 = 0x0101010101010101` |
| Store word 9 to termination | Outputs and flag unchanged; device read remains zero |
| Address-zero load checks and device word | True and zero |
| Eight-byte I/O-gap checks beginning at `io_end` | False |
| UART effective-address checks | True for LD, illustrating why the additional constraint/layout argument above is necessary |

In that successful check, `#print axioms` for each staged step returned `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
This is expected for unproved staged declarations.
There are no completed new step proofs or proof timings to claim.
No new `bv_decide`, `native_decide`, `decide +kernel`, explicit axiom, or proof-limit override was introduced.
Checks confirmed two staged `sorry` bodies, no trailing whitespace in the new module, and that `JoltConstraints.lean` differs from HEAD only by the new import.

Only the allowed new Lean file, the root import file, and this requested report were edited by this task.
No existing statement, core definition, restriction, or language predicate was changed.
The status documents are outside this task's allowed edits; their next authorized update should record the two staged device-step families and their invariants.
Work stops here for review, without proving the steps.

## Proofs

This follow-up was performed on `feat/soundness` on 2026-10-23 under `methods/layer6/device-memory-proofs.md`.
I read the required guidance and staging report, then checked the proof plan against the current Lean definitions, restrictions, witness lemmas, and the pinned Jolt sources at `5def437f`.
The audit found no false plan claim or counterexample to either staged step.
The successful builds below establish the caller proofs conditional on the five new staged semantic lemmas; their region proofs remain owed.

### Completed proof work

I replaced the body of `sd_device_step` first and built it successfully before starting the LD proof.
I then replaced the body of `ld_device_step`.
Both theorem statements, including every hypothesis and conclusion, were compared textually with HEAD and are unchanged.
Their proved bodies contain 50 and 47 lines respectively.
The original `atCut` hypotheses remain in both statements and are unused by these local proofs.

The SD proof derives canonical operands, source-column agreement, the actual address encoding and alignment, and the stored field value from existing lemmas and equations.
It applies `PanicStoresOne` to the attempted ready row to obtain word 1 in the panic case.
The semantic dispatcher considers output first, then panic, then termination.
Given the staged image effects, the proved column argument preserves every ordinary-RAM word and updates exactly the selected nontermination device word.
It preserves termination-table zero whenever neither the prefix nor the current store touches termination.
The same column argument is used for successor columns and `RamValFinal`.
Execution and live-register preservation follow from the semantic MMU result, the existing read and no-write lemmas, and the shared source-value frame lemma.

The LD proof derives the actual address encoding and alignment using `RamRegionFits` and the existing constraint lemmas.
Its address classification is shared with SD and proves that the address is zero or an actual selected grid word.
For address zero it uses `ram_zero_effects`; for a selected word it uses current device agreement, or `TerminationTableZero` at termination.
The common `read_doubleword_of_image_bytes` proves little-endian packing once and is applied to both device bytes and MMU bytes for all buffer regions.
The resulting `RamReadValue` determines `RdWriteValue`, and `registerWriteOn_step` supplies successful execution and the enlarged live set.
The existing zero load effects preserve both RAM columns, with the image frame supplied by the staged load lemma.
The output SD's byte-store growth and its image correspondence remain in its staged semantic lemma.

### New declarations

All declarations in this table are in namespace `JoltConstraints.Soundness` in `JoltConstraints/Soundness/Layer5/DeviceMemory.lean`.
Private helper declarations are included for review.

| Declaration | Line | Status and purpose |
|---|---:|---|
| `DeviceStoreResult` | 99 | New proposition packaging `stored`, `sail`, `vregs`, and `image`: successful MMU store, unchanged Sail/virtual registers, and the nontermination device-image update |
| `device_store_cases` | 119 | Staged region exclusion, nonzero address, panic touch, and termination-index identification |
| `device_output_store_image` | 142 | Staged output-store execution and image effect, including zero-filled growth |
| `device_panic_store_image` | 159 | Staged store of word 1, exact panic post-state, and normalized image update |
| `device_termination_store_image` | 175 | Staged ignored termination store and unchanged compared image words |
| `device_store_result` | 186 | Proved dispatcher over the three permitted store regions |
| `device_store_column` | 213 | Proved ordinary/device agreement for one updated table column |
| `device_store_agreement` | 241 | Proved successor/final-column agreement and conditional termination zero |
| `device_address_selection` | 283 | Proved shared zero-or-selected natural-address classification |
| `read_doubleword_of_image_bytes` | 305 | Proved common byte-packing lemma, with separate physical and image offsets |
| `device_load_image_bytes` | 325 | Staged byte dispatch, region/history facts, image correspondence, and image frame |
| `device_load_read` | 363 | Proved packing and transfer from device/termination agreement to `RamReadValue` |
| `device_load_agreement` | 419 | Proved successor/final memory agreement from zero effects and unchanged memory/image |
| `ld_device_step` | 472 | Existing statement; body now proved from the load helper chain |
| `sd_device_step` | 582 | Existing statement; body now proved from the store helper chain |

Every new helper is used by one of the two step proofs.
All new proved bodies are at most 50 lines.

### Staged obligations and their premises

The plan explicitly permits staging a missing substantial fact as a named lemma and continuing with the callers.
There are exactly five new `sorry` bodies, each the entire body of its named semantic lemma.
The top-level step proofs and the proved helper bodies contain no embedded gaps.

1. `device_store_cases` must recover the ready device's generated layout and show that checked below-RAM stores can only address output, panic, or termination.
   It also identifies a panic touch and converts equality with the initial layout's termination index into a current-device termination touch.
   Its premises are a real ready run, a below-RAM address, and the byte checks obtained from `sd_address_checks`.
2. `device_output_store_image` must prove the eight successful byte writes, output growth with zero padding, and the resulting single-word image effect.
   Its ready run is needed for the original image, unchanged layout/input/advice buffers, and reachable output bounds.
   Alignment, byte checks, and the output-region equation are established or supplied by the caller.
3. `device_panic_store_image` must prove the exact flag update and the normalized image value 1 while excluding termination from comparison.
   It takes stored word 1 explicitly; the caller proves that value from the existing `PanicStoresOne` restriction.
4. `device_termination_store_image` must prove that all eight writes are ignored and that every compared device image word is unchanged.
   The proved table argument separately handles the selected termination word and the now-vacuous zero obligation.
5. `device_load_image_bytes` must establish the shared buffer-byte correspondence, raw peripheral dispatch, panic history, termination history, address-zero behavior, and final-image preservation after the register write.
   Its `mapped` premise is proved from RAM selection and natural-number field injectivity, using the actual address encoding already obtained with `RamRegionFits`.
   It uses the existing `PanicStoresOne` and `TerminationThenStall` restrictions on the actual ready LD.
   In the termination case it must return both readable word zero and absence of an earlier termination store; those are what permit the caller to use `terminationWord`.

These semantic lemmas contain no witness or constraint-context parameter.
The checked run supplies execution history instead of assuming properties of an isolated device.
The existing summaries in `Layer5/TapeDeviceFrame.lean` take an `UntrustedAnswerTrace`; the staged run-level semantic proofs still need the corresponding frame reasoning for an `UntrustedAnswerRun`.
No existing frame theorem was weakened or given a new statement to bridge that distinction.
The audit supports the staged obligations, but this task has not proved their region arguments.

### Existing lemmas made public

| Declaration | File and line | Change |
|---|---|---|
| `sd_canonical` | `JoltConstraints/Soundness/Layer5/StoreDoubleword.lean:40` | Removed `private` and added a docstring; statement and proof unchanged |
| `sourceValue_of_host_frame` | `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:18` | Removed `private` and added a docstring; statement and proof unchanged |

No existing theorem gained a premise.
No approved statement, core definition, restriction, or language predicate changed.
`DeviceStoreResult` is the only new proposition definition.
The original four agreement/classification definitions in this module are unchanged.

### Build, axioms, and timing

Both requested builds succeeded:

```text
lake build JoltConstraints.Soundness.Layer5.DeviceMemory
Build completed successfully (8641 jobs).

lake build JoltConstraints
Build completed successfully (8814 jobs).
```

The final full build compiled `DeviceMemory.lean` in 4.9 seconds.
The module-only build with both completed caller bodies took 5.0 seconds for that module.
The modified `StoreDoubleword.lean` and `HostCallRegisterFrame.lean` modules also compiled in under ten seconds.
No new or changed proof exceeded about ten seconds.
The full build was not blocked by the other agents' edits.

The requested `#print axioms` checks for each step returned:

```text
[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

A transitive walk over declaration types and proof values identified the exact reachable declarations whose bodies contain `sorryAx`.
For `sd_device_step`, these are only `device_store_cases`, `device_output_store_image`, `device_panic_store_image`, and `device_termination_store_image`.
For `ld_device_step`, this is only `device_load_image_bytes`.
Thus the two caller proofs reach `sorryAx` exclusively through the five newly staged lemmas listed above.
`#print axioms read_doubleword_of_image_bytes` returned `[propext, Quot.sound]`.

There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, no explicit axioms, and no proof-limit changes.
`git diff --check` passed for all three edited Lean files.
Only `Layer5/DeviceMemory.lean`, the two Layer 5 files listed above, and this report were edited by this task.
No other agents' files or status documents were edited, and no commit was made by this task.
Work stops after this section for review of the five staged semantic obligations.

### Region-lemma follow-up: stopped at the shared-proof edit boundary

This follow-up on 2026-10-23 read `AGENTS.md`, `methods/layer6/reuse.md`, this report's "Proofs" section, and the proof plan's "Next: the five region lemmas" section.
The work began with `device_output_store_image`, as requested.
The code inspection found no counterexample to a staged statement, but none of the five region proofs was completed.
Their statements and bodies remain unchanged.

| Declaration in `JoltConstraints/Soundness/Layer5/DeviceMemory.lean` | Line | Status |
|---|---:|---|
| `device_output_store_image` | 142 | Still staged; local byte-store calculations checked, run/image argument unfinished |
| `device_load_image_bytes` | 325 | Still staged; proof not started |
| `device_store_cases` | 119 | Still staged; proof not started |
| `device_panic_store_image` | 159 | Still staged; proof not started |
| `device_termination_store_image` | 175 | Still staged; proof not started |

#### Goal and reason for stopping

The output proof needs the prefix's initial-to-final device frame and output-size bound, followed by a bridge from the final recorded state to the ready pre-state.
In particular, the outstanding run facts include:

```lean
JoltIOSetupFrame.Same run.initialState.jolt_device
  (TraceWitness.finalTraceState run.toTrace).jolt_device

(TraceWitness.finalTraceState run.toTrace).jolt_device.outputs.size ≤
  run.initialState.jolt_device.memory_layout.max_output_size.toNat
```

`UntrustedAnswerTrace.device_relation`, `UntrustedAnswerTrace.final_device_same`, and `UntrustedAnswerTrace.final_outputs_fit_layout` in `JoltConstraints/Soundness/Layer5/TapeDeviceFrame.lean:13`, `:52`, and `:64` already prove the corresponding completed-trace facts.
Inspection of their proofs shows that they use fields available on `UntrustedAnswerRun`, without using completion or verifier-acceptance fields.
Their current signatures nevertheless require `UntrustedAnswerTrace`.
An arbitrary ready prefix cannot be supplied as that argument: `UntrustedAnswerTrace` additionally requires acceptance, valid inputs, a nonempty trace, and a final stable stall, among other fields (`JoltConstraints/Soundness/Layer5/TapeTrace.lean:60`).

The plain-trace relation theorem and the relaxed instruction relation theorem are available, as the plan says.
Adapting them again inside `DeviceMemory.lean` would repeat the start/link/execution adapter already proved in `TapeDeviceFrame.lean`, and the output-bound argument would likewise repeat its existing proof.
`AGENTS.md`, "When stuck, discuss first" and "Making proofs general", requires stopping before copying an existing proof and extracting the shared proof instead.
The requested edit scope allows changes to other Layer 5 files only to expose private lemmas in place; these three declarations are already public.
I requested permission to refactor that shared proof, and stopped without treating the unanswered request as approval.
This is an edit-scope and proof-reuse blocker, not evidence that a region statement is false.

The proposed refactor is to add `UntrustedAnswerRun.device_relation`, `UntrustedAnswerRun.final_device_same`, and `UntrustedAnswerRun.final_outputs_fit_layout` in `TapeDeviceFrame.lean`, move the shared arguments to those run-level declarations, and derive the existing completed-trace declarations from them.
All three existing public statements would stay unchanged, as would the five region statements.
The ready-state bridge and region arguments would then remain in `DeviceMemory.lean`.
This proposal has not been implemented.

#### Calculations checked and retained changes

Temporary proofs in `DeviceMemory.lean` checked that a zero-extended array update changes exactly one observed byte, that a fold of successive updates changes exactly its byte interval, and that the MMU's eight-byte output-store fold produces the corresponding output array when explicit range and address-check premises hold.
These calculations did not establish the run invariants or the final-image correspondence, and therefore did not prove `device_output_store_image`.
The temporary helpers were removed because no retained proof used them, as `AGENTS.md` requires.
`git diff --exit-code -- JoltConstraints/Soundness/Layer5/DeviceMemory.lean` passed after removing them.
Only this report has a retained edit from this follow-up.
No statement, hypothesis, definition, restriction, or existing proof was changed, and no lemma was made public.
There are no new retained uses of `bv_decide`, `native_decide`, `decide +kernel`, axioms, or proof-limit overrides, and no retained new proof timing to report.

#### Validation

`lake build JoltConstraints` failed in the other agent's unfinished `JoltConstraints/Soundness/Layer6/DivisionAppend.lean:994`, where an array-prefix equality did not simplify to the expected indexed equality.
That file and `DivisionPrograms.lean` were not edited by this task.
The authorized fallback, `lake build JoltConstraints.Soundness.Layer5.DeviceMemory`, passed all 8641 jobs with the same five staged-lemma warnings.
Fresh `#print axioms` checks on all five region lemmas and both step theorems returned `[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]` for each declaration.
The staged obligations therefore remain outstanding; the successful module build does not discharge them.
No commit was made.
Work stops after recording this blocker and the proposed shared-proof refactor.

### Approved frame refactor and first region proof

This continuation on 2026-10-23 completes the approved run-level device-frame refactor and proves `device_output_store_image`.
It then reaches the next obligation, `device_load_image_bytes`, and stops at a further shared-proof edit boundary described below.
No counterexample to any of the five staged region statements was found.
The four remaining staged bodies are unchanged, and no additional gap was introduced.
The line numbers in this subsection describe the working tree after this continuation.

#### Run-level frame declarations

All declarations in this table are in `JoltConstraints/Soundness/Layer5/TapeDeviceFrame.lean`.
The shared arguments now live in the three `UntrustedAnswerRun` declarations.
Each existing `UntrustedAnswerTrace` declaration is a one-line application of the corresponding run declaration through `trace.toUntrustedAnswerRun`.

| Declaration | Line | Result |
|---|---:|---|
| `UntrustedAnswerRun.device_relation` | 17 | Carries a reflexive, transitive device relation preserved by successful byte stores through a prefix |
| `UntrustedAnswerRun.final_device_same` | 59 | Preserves the initial layout, trusted advice, untrusted advice, and inputs |
| `UntrustedAnswerRun.final_outputs_fit_layout` | 76 | Bounds final output length by the initial layout's output capacity |
| `UntrustedAnswerTrace.device_relation` | 131 | Existing statement unchanged; derived from the run theorem |
| `UntrustedAnswerTrace.final_device_same` | 147 | Existing statement unchanged; derived from the run theorem |
| `UntrustedAnswerTrace.final_outputs_fit_layout` | 158 | Existing statement unchanged; derived from the run theorem |

The three existing trace statements were compared textually against `HEAD` and are identical.
The new run declarations use the same relation obligations or initialized execution-prefix fields as the shared arguments previously required.
No acceptance, completion, or stable-stall hypothesis was added to a prefix theorem.

#### Region status, in the requested proof order

All declarations in this table are in `JoltConstraints/Soundness/Layer5/DeviceMemory.lean`.

| Declaration | Line | Result |
|---|---:|---|
| `device_output_store_image` | 557 | Proved; its axiom list contains no `sorryAx` |
| `device_load_image_bytes` | 778 | Still staged; panic-history proof needs the shared extension below |
| `device_store_cases` | 121 | Still staged; not attempted after the LD blocker |
| `device_panic_store_image` | 612 | Still staged; not attempted after the LD blocker |
| `device_termination_store_image` | 628 | Still staged; not attempted after the LD blocker |

The output proof transfers the initial layout, advice bounds, and input bound to the ready pre-state using the run frame and a shared observation lemma for `NextStep`.
It proves the generated layout lies above the MMU's peripheral ranges, then establishes the exact eight-byte output update, including zero-filled growth.
The image proof works on a generic trace with explicit device and buffer facts, compares zero-padded words once, and handles the unchanged panic image while excluding termination as the staged statement requires.
The existing `below` premise of `device_output_store_image` remains in its statement; the generated output range supplies the stronger end-of-word bound used in the proof.
All five region statements and both step statements were compared textually against `HEAD` and are unchanged.

#### Private helpers used by the output proof

These nineteen private theorems and one private definition are in `JoltConstraints/Soundness/Layer5/DeviceMemory.lean`.
Every helper is used by the retained output proof or another helper in its proof chain.
Each proved body is under sixty lines.

| Declaration | Line | Purpose |
|---|---:|---|
| `ready_observation` | 138 | Transfers any observation unchanged by PC advance from the prefix's final state to the ready pre-state |
| `power_padding_small` | 161 | Bounds power-of-two byte padding strictly below RAM |
| `advice_start_lower` | 177 | Bounds both advice starts using their actual placement equations |
| `layout_above_peripherals` | 194 | Shows a generated layout's lowest address is at least `0x40000000` |
| `io_grid` | 209 | Places output, panic, and termination on the layout's eight-byte grid |
| `remap_at_or_above` | 224 | Computes remapping for a nonzero layout and an address at or above its start |
| `output_address_range` | 232 | Gives peripheral exclusion and word bounds for an aligned output address |
| `run_inputs_fit` | 256 | Recovers the input-size bound from successful initialization |
| `padded_byte_store_read` | 270 | Proves the observed-byte effect of a zero-extended array update |
| `storeOutputBytes` | 294 | Defines a fold of successive zero-extended byte writes |
| `storeOutputBytes_read` | 300 | Proves the byte interval changed by that fold |
| `image_word_congr` | 321 | Transfers equality of eight bytes to equality of packed words |
| `image_word_extract` | 330 | Reconstructs a word from its extracted bytes using the existing RAM-store packing proof |
| `storeOutputBytes_word` | 341 | Proves the selected-word effect on zero-padded output bytes |
| `overlay_as_padded` | 361 | Identifies an overlay above a zero base with its zero-padded byte sequence |
| `overlay_store_word` | 384 | Transfers the selected-word effect to an overlay |
| `output_store_raw` | 399 | Computes one checked MMU output-byte store under explicit address bounds |
| `output_store_doubleword` | 421 | Composes the byte calculation over the eight-byte MMU fold |
| `input_overlays_zero_at_output` | 460 | Uses advice/input bounds to show preceding overlays are zero at output words |
| `output_image_update` | 488 | Proves the nontermination image update from explicit trace, layout, buffer, and post-device facts |

The new helper premises are local facts discharged by their callers: successful layout construction and initialization, ready-state observation preservation, byte/address bounds, buffer bounds, and the explicit output update.
No existing theorem gained a premise.
`storeOutputBytes` is the only new definition; no existing definition, restriction, or language predicate changed.

#### Existing private lemmas made public

| Declaration | File and line | Change |
|---|---|---|
| `ram_store_byte` | `JoltConstraints/Soundness/Layer5/RamStore.lean:18` | Removed `private` in place and added a docstring |
| `ram_store_word` | `JoltConstraints/Soundness/Layer5/RamStore.lean:31` | Removed `private` in place and added a docstring |

Both statements and both proof bodies were compared textually against `HEAD` and are unchanged.
They supply the byte-extraction and reconstruction argument reused by `image_word_extract`.

#### LD panic history: goal, failed invariant, and proposed extension

For an actual ready LD touching panic, `PanicStoresOne` excludes an earlier `StoresPanicAt` row.
The missing run-history fact is then:

```lean
(¬ ∃ i : Fin run.rows.size, run.StoresPanicAt i) →
  pre.jolt_device.panic = false
```

This fact needs the run's initialized false flag, execution certificates, links, and ready-state relation.
It cannot be obtained by directly applying the existing device-relation frame to the relation `fun a b => a.panic = false → b.panic = false`.
`execWithTapeAnswer_rule_of_device_relation` (`Layer5/TapeSemantics.lean:38`) requires preservation under every successful device byte store, independently of the instruction being executed.
The same unconditional obligation appears in `InstructionFrame.Rules.store` (`JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:31`) and `JoltIOSetupFrame.execInstr_rule_of_device_relation` (`JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:87`).

The exact failed primitive case is a device with `panic = false`, address `io.memory_layout.panic.toNat`, and stored byte zero.
The following calculation was checked by Lean:

```lean
example (io : JoltDevice) (notPanicked : io.panic = false) :
    io.store? io.memory_layout.panic.toNat 0 = some { io with panic := true } ∧
    ¬ ({ io with panic := true } : JoltDevice).panic = false := by
  simp [JoltDevice.store?]
```

This identifies a false side condition for that use of the frame theorem; it does not refute `device_load_image_bytes` or another staged region statement.
The plan's suggested relation-preservation route therefore needs an additional connection between a device change and the actual SD row.
The existing frame declarations alone do not supply that connection.

The proposed extension is a shared instruction-frame variant whose store obligation is needed only for an SD instruction, preserving all existing public statements through wrappers.
It would support a relaxed-execution theorem saying that a successful non-SD instruction preserves the entire device.
The actual SD case can then relate a false-to-true panic transition to `TouchesPanic`, and the run induction can produce a recorded `StoresPanicAt` witness.
This would require edits to `InstructionFrame.lean`, `DeviceFrame.lean`, and `Layer5/TapeSemantics.lean` beyond the currently authorized scope.

`AGENTS.md`, "When stuck, discuss first" and "Making proofs general", requires discussion before repeating the instruction proof or splitting over the instruction set for this case.
I requested approval for the shared extension and have not treated the unanswered request as approval.
No instruction-set case split, duplicate frame proof, out-of-scope edit, or new staged history lemma was made.
Work stops at this scope and reuse boundary.

#### Builds, axioms, timing, and retained scope

All requested builds succeeded in this continuation:

```text
lake build JoltConstraints.Soundness.Layer5.TapeDeviceFrame
Build completed successfully (8532 jobs).

lake build JoltConstraints.Soundness.Layer5.RamStore
Build completed successfully (3413 jobs).

lake build JoltConstraints.Soundness.Layer5.DeviceMemory
Build completed successfully (8651 jobs).

lake build JoltConstraints
Build completed successfully (8814 jobs).
```

The changed modules compiled in 4.0 seconds, 5.6 seconds, and 6.4 seconds respectively.
No new or changed proof was observed taking more than about ten seconds.
The latest full build succeeded with the other agent's concurrent edits present.

Fresh `#print axioms` checks for all six frame declarations and `device_output_store_image` returned:

```text
[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

Neither the frame refactor nor the completed output theorem depends on `sorryAx`.
The checks for `sd_device_step` (`DeviceMemory.lean:1035`) and `ld_device_step` (`DeviceMemory.lean:925`) still returned:

```text
[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

There are exactly four remaining `sorry` bodies in `DeviceMemory.lean`, each the whole body of one unchanged staged region lemma listed above.
There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, no explicit axioms, and no proof-limit changes.
`git diff --check` passed for the three edited Lean files.
This continuation retained edits only in `TapeDeviceFrame.lean`, `DeviceMemory.lean`, `RamStore.lean`, and this report.
It did not edit `DivisionAppend.lean`, `DivisionPrograms.lean`, `RegistersReadProofHelpers.lean`, or the proof-status documents.
No commit was made.
