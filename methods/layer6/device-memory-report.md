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
