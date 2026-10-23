# Remove `bv_decide`

Work is on `feat/soundness`, starting from `c612c9d`.
Part 1 is complete, and Ari subsequently authorized continuing directly into Part 2 without stopping.
All 21 uses have been replaced, and the final Part 2 rebuild and axiom audit passed.
This agent made no commits.
During the run, external commits recorded Part 1 as `b6949a7`, its audit notes as `a7a636e`, and Part 2 as `43624d4`.
The declarations and timings below describe that tested implementation; a concurrent follow-up edit is recorded at the end.

## Checks of the plan

The initial `#print axioms JoltInstance.soundness` matched the plan: `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
The two Part 1 uses proved the same 13-bit to 128-bit to 64-bit sign-extension identity.
The source search confirmed the stated distribution: two Part 1 uses, eight in `LookupEntryProofHelpers.lean`, ten in `Splice.lean`, and one in `Sd.lean`, plus the comment in `Interleave.lean`.
The code also confirms that the window entries read the same low address bits, the alignment statements concern low-bit masks, and the remaining lookup obligations concern clearing bit zero and byte reversal.
No incorrect mathematical claim was found.

## Part 1

`encoded_branch_offset` now proves bit equality using `BitVec.eq_of_getLsbD_eq`, `BitVec.getLsbD_setWidth`, and `BitVec.getLsbD_signExtend`.
For every `i < 64`, `omega` establishes `i < 128`, so both sign extensions select the same source bit or sign bit.
`branch_target_toNat` obtains its local `extended` fact from `encoded_branch_offset offset`.
No new Part 1 lemma was needed.
The proof bodies occupy 5 and 19 lines respectively.

| Declaration | Location | Elaboration time (seconds) |
| --- | --- | ---: |
| `encoded_branch_offset` | `JoltBytecode/JoltISA/Values.lean:142` | 0.004899 |
| `JoltConstraints.branch_target_toNat` | `JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean:98` | 0.097271 |

The Part 1 `lake build JoltBytecode JoltConstraints` passed (8830 jobs, 499.02 seconds wall time).
After that rebuild, `#print axioms JoltInstance.soundness` listed exactly `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
Both changed lemmas listed only `propext`, `Classical.choice`, and `Quot.sound`.
The Part 1 completeness audit listed the four baseline axioms, an existing `sorryAx`, and seven remaining `bv_decide` axioms from `LookupEntryProofHelpers.lean`.
The branch timing was recorded before proceeding with Part 2, as requested.

## Part 2: shared facts

Five general lemmas are added in `JoltBytecode/InstructionEquivalence/ProofSupport/BitVecMasks.lean`.
They mention only bitvectors, widths, masks, shifts, and the bounds needed by their proofs.
Their callers discharge the new lemmas' bounds with closed arithmetic checks or use alignment hypotheses already present in the callers.
No existing theorem acquired a hypothesis.

| New declaration | Line | Purpose | Elaboration time (seconds) |
| --- | ---: | --- | ---: |
| `BitVec.setWidth_setWidth_eq_and_mask` | 12 | Express truncation followed by zero extension as a low-bit mask; shared by byte, halfword, and word extraction. | 0.014452 |
| `BitVec.and_not_eq_self_of_and_eq_zero` | 20 | Clearing already-zero bits preserves the value; shared by aligned splice offsets and native SD. | 0.031907 |
| `BitVec.ofNat_ushiftRight_and_toNat` | 32 | A shifted mask reads the natural-number bits whenever the chosen width retains them. | 0.026196 |
| `BitVec.ofNat_umod_pow2_eq_zero_of_low_mask` | 54 | Derive remainder-zero alignment at one width from a low-bit mask at another width; shared by halfword and word alignment. | 0.025455 |
| `BitVec.ushiftRight_and_setWidth` | 74 | Preserve a shifted, masked value across truncation and zero extension; shared by all three window-mask entries. | 0.004138 |

The mask-width and alignment lemmas reuse `BitVec.ofNat_ushiftRight_and_toNat` rather than repeat its bit argument.
The existing `toNat_eq_of_setWidth` and `ofNat64_eq_setWidth` remain in use by the window-entry callers.

## Part 2: splice and SD replacements

In `JoltBytecode/InstructionEquivalence/Instructions/StoreFamily/Splice.lean`, the three low-value lemmas instantiate the shared truncation lemma.
`masked_add_eq_splice` uses core `BitVec.add_eq_or_of_and_eq_zero` and bit equality.
The fused splice proofs use core AND associativity and idempotence for containment, the shared zero-mask lemma for aligned offsets, and core shift distribution for the word-selection bit.

| Changed declaration in `Splice.lean` | Line | Elaboration time (seconds) |
| --- | ---: | ---: |
| `StoreSplice.lowByte_zeroExtend` (private) | 232 | 0.001996 |
| `StoreSplice.lowHalfword_zeroExtend` (private) | 237 | 0.001589 |
| `StoreSplice.lowWord_zeroExtend` (private) | 242 | 0.001589 |
| `StoreSplice.masked_add_eq_splice` (private) | 247 | 0.061923 |
| `StoreSplice.fusedByteSplice_eq` | 270 | 0.026600 |
| `StoreSplice.fusedHalfwordSplice_eq` | 305 | 0.030929 |
| `StoreSplice.fusedWordSplice_eq` | 345 | 0.058917 |

`Natives.sdJolt_reduces_to_vmem_write_addr`, at `JoltBytecode/InstructionEquivalence/Instructions/Natives/Sd.lean:27`, now derives its local `hclear` fact from the same zero-mask lemma.
Its complete proof elaborated in 0.164657 seconds.

## Part 2: lookup replacements

All changed declarations below are in `JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean`.
The three window entries instantiate the shared mask-width fact; the two alignment declarations instantiate the shared power-of-two remainder fact.
`lookupEntryCorrect_RangeCheckAligned` simplifies Sail's zero-bit update and uses core AND commutativity.
The byte-reversal declarations invoke the shared proofs described below.

| Changed declaration (namespace `JoltConstraints`) | Line | Elaboration time (seconds) |
| --- | ---: | ---: |
| `windowMaskB_entry` | 229 | 0.009255 |
| `windowMaskH_entry` | 241 | 0.009207 |
| `windowMaskW_entry` | 253 | 0.009351 |
| `halfword_aligned` | 263 | 0.001591 |
| `word_aligned` | 267 | 0.001461 |
| `lookupEntryCorrect_RangeCheckAligned` | 306 | 0.872850 |
| `rev8_32` | 476 | 0.000176 |
| `rev8w_eq` | 479 | 0.000178 |

## Part 2: existing byte-reversal proofs shared

The following proofs were moved from `JoltConstraints/Soundness/Layer5/UnaryWord.lean` to the new `JoltConstraints/Soundness/Layer4/ByteSwap.lean`.
Their statements and proof bodies are unchanged.
`append32_eq_add` remains private; `rev8w_eq_kernel` and `rev8_32_kernel` are now public and have docstrings with concrete examples.
Both `UnaryWord.lean` and `LookupEntryProofHelpers.lean` import the shared module.
No copy of the old proof bodies remains in either caller.

| Moved declaration (namespace `JoltConstraints.Soundness`) | New line | Elaboration time (seconds) |
| --- | ---: | ---: |
| `append32_eq_add` (private) | 12 | 0.047085 |
| `rev8w_eq_kernel` | 27 | 0.009149 |
| `rev8_32_kernel` | 36 | 1.025068 |

The moved `rev8_32_kernel` retains its existing `interval_cases` over 32 bit positions.
No new exhaustive bit-position split was written.
The new bit proofs use individual Boolean cases and arithmetic bounds.

## Statement preservation and proof checks

A comparison against the existing code verified that all 21 changed or moved existing theorem statements, including every hypothesis, are byte-for-byte unchanged.
No definition, restriction, or top-level theorem statement changed.
All five new lemmas are used, and all newly written proof bodies are under 60 lines.
No `sorry`, `bv_decide`, `native_decide`, or `decide +kernel` was added, and no resource limit was raised.
This agent did not edit `JoltConstraints/model_review.md` or `methods/soundness.md`.

Every edited module passed an individual Lean check, including `UnaryWord.lean` after extraction.
`git diff --check` passed.
`rg -n '\bbv_decide\b' JoltConstraints JoltBytecode -g '*.lean'` finds only the existing comment at `JoltConstraints/Soundness/Layer4/Interleave.lean:17`.
An unrestricted search also finds documentation mentions in `JoltConstraints/model_review.md`, which the task explicitly leaves to the auditor.
The generated `LeanRV64D` sources contain no `bv_decide` occurrences.

The table timings come from Lean's `Elab.async` proof-elaboration trace with `lake env lean -j1 -Dtrace.profiler=true`.
The first modules used `trace.profiler.threshold=0` or `1` milliseconds; the large lookup module used `trace.profiler.threshold=10000` with `trace.Elab.async=true` to retain proof timings without printing every tactic trace.
No changed or moved proof exceeded ten seconds; the maximum was 1.025068 seconds for the moved `rev8_32_kernel`.
An initial branch-profile attempt ran while a dependency object was being rebuilt, then passed when rerun after that dependency rebuilt.
An excessively verbose lookup-profile run was interrupted and replaced by the successful proof-level profiling run.

## Final rebuild and axiom audit

`lake build JoltBytecode JoltConstraints` passed (8832 jobs, 410.25 seconds wall time).
`git diff --check` passed after the rebuild.
The final `#print axioms` results are:

```text
'JoltInstance.soundness' depends on axioms:
  [propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
'JoltInstance.completeness' depends on axioms:
  [propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

Neither top-level theorem retains a `bv_decide` axiom.
Completeness retains the `sorryAx` already observed in the Part 1 audit; no new `sorry` was introduced.
The Part 1 lemmas, all five new mask lemmas, both shared byte-reversal lemmas, and all three fused splice lemmas were also audited; each uses only a subset of `propext`, `Classical.choice`, and `Quot.sound`.
The native SD lemma's audit lists `match_reservation`, `plat_term_write`, `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`, with no `bv_decide` axiom.

## Concurrent follow-up

After the final audit, another session removed the two wrapper declarations `JoltConstraints.rev8_32` and `JoltConstraints.rev8w_eq` and changed `lookupEntryCorrect_VirtualRev8W` (`LookupEntryProofHelpers.lean:476`) to call the shared `Soundness` lemmas directly.
This agent preserved that edit.
The auditor then rebuilt: `lake build JoltBytecode JoltConstraints` passed (8,832 jobs), and `#print axioms` gave the same results for `JoltInstance.soundness` and `JoltInstance.completeness` as above.
