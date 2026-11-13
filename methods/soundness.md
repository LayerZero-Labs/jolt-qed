---
title: Plan for deterministic, non-succinct soundness
updated: 2026-11-05
rust_pin: c97e93004fbf804409f0374fe8457c8f1562ce71
lean_head: e29949809bbf2c54c315c2ca55ae3b90c7fd37a6
---

Our goal is to make Jolt secure through formal verification. Each intermediate
claim should give us a reusable proof or expose an edge case we can investigate
and fix.

Read these before beginning work:

1. [The high-level account of Jolt](https://randomwalks.xyz/blog/jolt-qed/01-jolt-why/).
2. [The completeness proof and bug-finding workflow](./constraint_proving.md).
3. [Known model gaps and proof obligations](../JoltConstraints/model_review.md).
4. The current state, in the next section.
5. The constraints migration outline in [constraints.md](../JoltConstraints/constraints.md#migration-outline).

The issue writeups live in `LayerZero-Research/LZ-Notes` under `content/projects/jolt-qed/blog/`.

## Current state (2026-11-03)

The older sections describe the proof as it stood at Lean commit `7096dca`.
The Step 4 starting commit is `e29949809bbf2c54c315c2ca55ae3b90c7fd37a6`, on `review/audit-completeness-soundness`.
The Step 4 proof repairs are uncommitted and await review.

- On 2026-11-05 Ari moved the Jolt pin from `5def437f` to `c97e9300`, the merge of a16z/jolt#2250 (see [Current Jolt pin](#current-jolt-pin-2026-11-05)).
- Steps 1–3 are committed: migrated definitions, completeness repairs, and the approved extension of `TracerAddressChecks` to the containing doubleword of floor loads and stores.
- Step 4 repairs the six initial failing modules and their callers: destination-value input routing, ShiftData's signed immediate, retired alignment rows, plain-row classification, stall flags and tape replay addresses.
- Ari approved on 2026-11-03 extending `PanicStoresOne`, `TerminationThenStall`, `StoresPanicAt` and `StoresTerminationAt` to `VirtualLoadB/H/W` and `VirtualStoreB/H/W` at their containing doubleword `ea &&& ~~~7`; no other restriction or assumption changed, and the statements of `JoltInstance.soundness` and `InLanguage` are unchanged.
- `Soundness/Layer5/MemoryRows.lean` classifies LD, SD and the six floor rows once by width (`MemoryWidth`, `LoadRow`, `StoreRow`).
  `AccessRow.address_encoded` proves from constraint (01), the AddressOffset lookup, RAM selection and `RamRegionFits` that the RAM address is the accessed doubleword and that the effective address is naturally aligned for its width.
  The Layer 5 load and store steps, the Layer 6 row extension and the Layer 7 termination-store proofs now cover every memory row through this classification.
- `lake build JoltConstraints` passes (8,837 jobs), and `#print axioms JoltInstance.soundness` lists `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`, as at `7096dca`.
  No soundness proof has a `sorry`.
- Step 4 left the six completeness admissions and seven bytecode admissions unchanged.
  The bytecode admissions have since been removed; see [Proofs owed](../JoltConstraints/model_review.md#proofs-owed).
- The [Step 4 report](../reports/2026-11-03-constraints-migration-soundness.md) lists every repair, statement change and validation result.

Bytecode migration in the working tree:

| Change | Where |
| --- | --- |
| `VirtualLoadB/H/W` and `VirtualStoreB/H/W` access the containing doubleword (floor addressing) | `JoltISA/Instruction.lean`, `JoltISA/Semantics.lean` |
| `VirtualAlignAddr`, `VirtualAssertHalfwordAlignment` and `VirtualAssertWordAlignment` removed; their instruction-lemma files and imports deleted | `JoltISA/Instruction.lean`, `InstructionEquivalence/ProofSupport/` |
| `VirtualShiftDataB/H/W` take an immediate, used in the effective address | `JoltISA/Instruction.lean`, `JoltISA/Semantics.lean`, `ProofSupport/InstructionLemmas/VirtualShiftData.lean` |
| Shared width-indexed lane opening, extraction and merging | `JoltISA/Expansions/LaneWindow.lean` |
| Regenerated expansion rows | `JoltISA/ExpansionsAutomated.lean` |
| Load, store and word-AMO proofs use the new programs | `InstructionEquivalence/Instructions/LoadFamily`, `StoreFamily`, `AtomicFamily` |

These paths are relative to `JoltBytecode/`.
Jolt's expander for shared lane windows is `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow`).
Jolt's tracer implements floor accesses in `tracer/src/instruction/floor_access.rs`.

How to start, with no prior context:

1. This section, then the open proof obligations under [Proofs owed](../JoltConstraints/model_review.md#proofs-owed).
2. The migration order in [constraints.md](../JoltConstraints/constraints.md#migration-outline).
3. The proof method in [constraint_proving.md](constraint_proving.md).
4. The newest dated report in `reports/`, currently [`2026-11-03-constraints-migration-soundness.md`](../reports/2026-11-03-constraints-migration-soundness.md).

## Change of course: top-down (2026-10-20)

Ari decided to stop building the proof bottom-up. So far we proved about 75
Layer 5b step lemmas before Lean had any statement of what they are for. The
HostIO step showed the cost: it produces `RegisterAgreementExceptHostTemp`,
which no other step lemma accepts, and we found that only after writing it.

The plan below is unchanged: the same layers, argument and proved lemmas.
Only the order of work changes:

1. Close `JoltInstance.soundness` by proving it from helper lemmas, each
   stated with `sorry`.
   Done on 2026-10-20: the main proof reconstructs a relaxed trace, obtains output agreement, prover acceptance, and passing spoil asserts from four named helpers, then uses the reverse language inclusion to obtain an `HonestTrace`.
2. Prove each helper the same way: state the lemmas it needs with `sorry`,
   in exactly the form it uses them.
3. Continue downward until the statements reach the existing Layer 5b step
   lemmas, then see what goes wrong: which step lemmas fit their caller,
   which need their statements changed, and which expose a missing fact.

We will still add temporary FIXME premises if needed, with Ari's approval, as
before. Never write a theorem or `sorry`'d lemma that is known to be false
without Ari's permission: anything follows from a false `sorry`, so it would
hide new issues. When a statement has a counterexample, propose a FIXME
restriction that excludes it, and write up the counterexample for a16z.
Track every new `sorry` in `model_review.md` under "Proofs owed".

### The argument in brief

Read this before the layers below; the rest of this document fills it in.

- **The relation.** `AllConstraints joltInstance untrustedAdvice witness` is a predicate on the witness alone, a table of field elements indexed by cycle.
  The instance and the committed untrusted-advice words enter only as fixed data: the expanded bytecode, the initial RAM, the public I/O and the entry slot (`ConstraintContext`).
  No trace appears in it.
  Jolt's verifier holds only a commitment to the untrusted advice, so each advice word is an arbitrary field element (`committedInitialValue`).
- **From field words to bytes.** `onBytes_of_allConstraints` (`Soundness/UntrustedAdvice/Bytes.lean`) reduces the relation to the byte relation `AllConstraintsOnBytes joltInstance privateInputs witness`, where the untrusted advice is bytes, as the tracer receives it.
  Every load reads a 64-bit word (`load_ramReadValue_word`), so an advice word that is not a 64-bit word is never loaded before it is overwritten.
  The reduction replaces such a word by zero and shifts the witness's RAM value columns at the word's first access (`shiftWitness`).
  It needs the separate temporary premise `UntrustedAdviceBlockFits` (not a field of `TemporaryRestrictions`).
  The rest of this document proves `JoltInstance.soundness_onBytes` for the byte relation.
- **The language.** `JoltInstance.InLanguage` says there exist private inputs
  and an `HonestTrace` on them whose final device has the claimed outputs and
  panic flag (`matches_outputs`), which Jolt's prover accepts, and whose spoil
  asserts all pass. Stopping at the PC stall is part of `HonestTrace` itself.
- **The existential.** The private inputs are the given untrusted advice, a tape built from the values the witness records at its tape-read cycles, and the inline advice words the reconstructed run's inline advice steps record (`collectInlineAdvice`).
  The run is honest for those words (`honest_of_builtin`), and `JoltInstance.soundness_onBytes` moves it to private inputs that hold them.
  The given tape cannot be used: no constraint reads it (`AllConstraintsOnBytes.advice_tape_irrelevant`).
  The relaxed trace ends at the first stable stall, or at padding or the last witness cycle if neither comes first.
  The rebuilt tape then gives an honest trace with the same source-level results.
- **The connection, step 1.** For every retained cycle `t`, the witness's columns describe the relaxed trace's state before step `t`: the selected row, its live registers and its memory.
  The witness may repeat the stable source instruction after the cut before padding begins.
  Its final memory (`RamValFinal`) then equals the relaxed trace's final memory outside the synthetic termination word.
  The retained-prefix comparison is proved by induction on `t`, using the constraints; it is the `Agrees` invariant below.
- **The claim, step 2.** Constraint 26 (`ramOutputEqPublicIo`) says that in the public I/O region the witness's final memory equals the claimed I/O.
  With step 1, the relaxed trace's final memory holds the claim, which gives `matches_outputs`; the rebuilt honest trace inherits that result.
- **Why the witness is essential.** Constraint 26 is the only constraint that
  reads the claimed outputs. Take a true claim and its honest witness, then
  change only the claimed outputs, keeping them within the instance's output
  size: every other constraint still holds. So
  "an honest trace exists" alone is trivial; the content is that its outputs
  are the claimed ones.

The proof first runs with the witness's tape values fed in directly (the
relaxed semantics of Layer 5a), then shows the run on the built tape ends
every source instruction with the same registers and memory (Layer 7).

### Current top-level status (2026-10-23)

At Lean HEAD `7096dca` on 2026-10-23, `JoltInstance.soundness` was proved, under the temporary restrictions, with no `sorry`.
`lake build JoltBytecode JoltConstraints` passed then (8,832 jobs), and `#print axioms JoltInstance.soundness` listed only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
The theorem chains four helpers in `Soundness/TopLevel.lean` to get the relaxed language, then applies the reverse inclusion `untrustedAnswerLanguage_implies_inLanguage` (Layer 7) to get `InLanguage`.
Helper A returns an `UntrustedAnswerTrace` represented at every actual row, from execution-prefix agreement (Layer 6, `Soundness/Layer6/ExecutionPrefix.lean`) and the stopping theorem (`Soundness/Layer7/Stopping.lean`).
Helper B checks the output and panic words through constraint 26 and final RAM agreement, with no panic restriction; `Represents.finalRam` covers every RAM index except the termination word.
Helper C shows Jolt's prover accepts the trace, using the base verifier's 256-cycle floor (`ConstraintContext.traceLengthFloor`) and the approved `noMaxLengthTrace` restriction.
Helper D shows no spoil assert fails, using the checker's `noSpoilAsserts`.
Layer 6 proves execution-prefix agreement by strong induction over source instructions; inside an expansion, registers agree only where they are live.
The prefix cuts at the first stable stall, padding, or the last witness cycle and owns RAM agreement at that boundary; the stopping theorem carries it to final RAM.
The stopping rule mirrors a16z/jolt PR #2109 at merge commit `0249591a`; no additional restriction is used for the JALR self-jump case.
The audit `reports/2026-10-29-soundness-statement-audit.md` checks the statement against Jolt at `5def437f`.
It finds one serious gap: Lean requires untrusted-advice words to be 64-bit values, which Jolt's verifier does not check (its finding 1).
The axiom result and the remaining cleanup are under [Proofs owed](../JoltConstraints/model_review.md#proofs-owed).

### When the proof uncovers an issue

Proving top-down will uncover more issues.
When a statement cannot be proved, name the exact missing fact or counterexample, and stop to ask Ari before changing anything.
Do not add a restriction, change L, or keep a known-false statement without Ari's decision.
No currently staged statement is known false; stop and report any counterexample before proceeding.

First rule out a translation issue.
Our constraints, Jolt's tracer semantics, the device and the prover's sizing are Lean translations of Jolt's Rust code.
Compare every Lean definition the counterexample depends on with Jolt's code at the pin.
If they differ, the issue is ours: propose a model fix to Ari, and record it in `model_review.md` under "Gaps in our model".
For example, the code that builds the claimed I/O words suggests a panicked claim never checks the termination word; the verifier's check covers the whole I/O region, so it does check it, against 0.

If the Lean definitions match Jolt's code, decide which kind of issue it is:
- a Jolt bug, where a false claim is accepted, as in the panic-word and early-stop posts;
- a prover/verifier mismatch, where the claim is true but Jolt's prover would not prove it, so only L fails, as in the trace-length post.

An issue is confirmed only once reproduced against Jolt's actual prover and verifier; the write-up says whether it was.

Write each issue up as its own post in `LayerZero-Research/LZ-Notes` under `content/projects/jolt-qed/blog/`.
Posts go to a16z privately, never as public GitHub issues.
A post has: background with quoted Jolt code and a reference link; each constraint as one plain sentence followed by its formula, without references; an example in real RISC-V, with no pseudo-instructions, and made-up addresses in label, PC and instruction columns; the cheating witness; the constraints that matter checked one by one with the values filled in; the final check against the false claim; the false claim and the true claim; and the core issue.
Write plain prose, one sentence per line, with no status labels, and check every quoted line at the pin.
A FIXME restriction for the issue links to its post and says the bug must be fixed in Jolt.

### Register agreement must be over live registers

This is a design point for the induction in `soundness_execution_prefix_agreement`.
`RegisterAgreement` (`Layer5/Registers.lean`) compares every register; HostIO now has no operands and writes no register, so its local step preserves full agreement.
Scratch registers 40 to 47 can still differ between the witness and the honest run after a division expansion, because a division by zero accepts any quotient advice, so live-register agreement is still needed.
A scratch register can retain a different value across native rows that never write it.
`RegisterAgreementOn live` (`Layer5/Registers.lean`) is agreement on a set of live registers: each step requires its source operands to be live and adds its destination.
`BoundaryState` uses the registers that are not temporaries, and `ExpansionState` adds the temporaries already written in the unfinished source (`ExpansionLive`, `Layer6/PrefixState.lean`).
Temporaries 40–47 are dead at every source boundary, by `tempsReadAfterWrite`.

## Remaining work (2026-11-02)

0. Migrate the constraints to the `c6703570` ISA, as the eleven items in [constraints.md](../JoltConstraints/constraints.md#migration-outline) describe, then repair the dependent proofs and rebuild both libraries.
   Helper statements may change within the approved scope; the main statements do not.
1. The open findings of `reports/2026-10-29-soundness-statement-audit.md`: how to model untrusted-advice words (finding 1) and the HostIO END marker's missing read (finding 2).
2. The cleanup list under "Proofs owed" in `model_review.md`: long proofs, repeated unpacking, unused declarations and checker speed.
3. The closing report: restrictions split into static checks, run-time properties and the claim; assumptions; issues found; the SDK question.

Agents work in one checkout on disjoint files; each task's report goes in `reports/`, and Claude audits each report before the next task starts.
Do not add theorem premises without Ari's approval; do not use `native_decide`, `decide +kernel` or a larger `maxHeartbeats`.
The issue write-ups remain for the agreed batch; #2044 discussion waits for Michael's comments.

## Current Jolt pin (2026-11-05)

The current Jolt source pin is [`c97e93004fbf804409f0374fe8457c8f1562ce71`](https://github.com/a16z/jolt/commit/c97e93004fbf804409f0374fe8457c8f1562ce71), the merge of a16z/jolt#2250.
The constraints were migrated to `c6703570`.
Of the seven commits from `c6703570` to `c97e9300`, only #2250 changes modeled code (`crates/jolt-prover/src/config.rs` and `crates/jolt-program/src/preprocess/ram.rs`), and the model already followed it.
The others change CI, dependencies, Dory and GT arithmetic, and an optimized prover kernel, none of which is modeled.
The previous pin was `5def437f`; the statement was checked against it in `reports/2026-10-29-soundness-statement-audit.md`.

## Soundness statement

The current target is [`JoltInstance.soundness`](../JoltConstraints/Soundness/soundness.lean).
It concludes the fixed-tape language `JoltInstance.InLanguage`, and keeps it:
on 2026-10-15 Ari decided this is Jolt's language (see
[Choosing the private inputs](#choosing-the-private-inputs)). Layer 5a defines the
relaxed language in [TapeTrace.lean](../JoltConstraints/Soundness/Layer5/TapeTrace.lean),
used only inside the proof, and proves fixed-tape language inclusion.
Layer 5a is built and reviewed by reading. Ari approved the
instance-only RAM-region premise below; Layer 5b begins by deriving nonwrapping
addresses from it and the constraints.

**Source-language scope.** Both targets cover programs represented by [`SourceInstruction`](../JoltConstraints/expansion_helpers.lean): the modeled RISC-V instructions, the listed Jolt custom instructions at opcode `0x5B`, and twelve registered inlines at opcode `0x0B` (SHA256, SHA256_INIT, KECCAK256, KECCAK256_ABSORB_PERMUTE, BLAKE2, and the secp256k1 inlines MULQ, SQUAREQ, DIVQ, MULR, SQUARER, DIVR and GLVR_ADV; `JoltBytecode/Inlines/Keys.lean`).
Every other `0x0B` encoding, including the `rd = x0` encodings of the secp256k1 inlines, opcode `0x2B` and field-inline opcode `0x7B` are outside that type.
The SDK's `field_to_limbs!` and `field_from_limbs!` emit `0x7B` instructions.
Any guest containing these instructions is outside the theorem's scope by construction.
This is an existing language restriction, not an added soundness premise.

An instance is a claim about one program.
It gives the program, its public inputs and trusted advice, and the output bytes and panic flag the program is claimed to produce.
The private inputs are what the prover picks and Jolt's verifier never sees.
In the existing specification they are the untrusted advice, which is loaded into RAM, the advice tape, which the guest reads while the program runs, and the inline advice words (`inline_advice`), which the VirtualAdvice rows of the secp256k1 inlines write, in trace order.
Jolt's prover fills `inline_advice` with each inline's `build_advice` output, but the language allows any words that pass the inline's own assertions, including non-canonical ones (`JoltConstraints/language.lean`, decision D2 in `docs/inline-precompiles.md`).
The relaxed specification, used only inside the proof, supplies independent answers in the existentially chosen trace (Layer 5a).
It retains the tape state for exact inclusion, but the relaxed tape instructions do not consult its bytes or enforce exhaustion.
A step is one row of the expanded bytecode being run; an expandable instruction such as DIV takes several steps.
A witness `w` is a set of tables indexed by `params.traceLength` cycles.
The proof must establish which cycles describe execution steps and which are padding.
In the non-succinct model, the verifier receives `w` in the clear and checks every modeled constraint.

The theorem says: if some `w` satisfies every constraint, then there are private inputs, including one advice tape, and an `HonestTrace` on them whose final device holds the claimed output bytes, after trimming trailing zeros, and the claimed panic flag. Jolt's prover must also accept that trace (`prover_config.isSome`), and none of its spoil asserts may fail (`SpoilAssertsPass`). On 2026-10-15 Ari added these two to `InLanguage`, because Jolt's code says it proves only such runs; L is exactly what Jolt's code says, nothing more or less.
The existing `HonestTrace` describes Jolt's tracer running with a fixed tape: each step's bytecode row, its state before and after, the runtime advice Jolt's tracer computes (for a VirtualAdvice step of a registered inline, the next word of `inline_advice` instead), and the step where Jolt's tracer stops.
The proof first builds a relaxed trace, which allows independent tape answers while retaining the other execution, internal runtime-advice and stopping requirements. Its definition and the inclusion of fixed-tape traces are implemented in Layer 5a. Layer 7 then rebuilds one tape from the answers, giving an `HonestTrace`.
We aim to preserve the supplied untrusted advice in RAM and choose the tape answers and the inline advice words from the witness: `soundness_reconstruct_trace` reads the inline advice words off the run's inline advice steps (`collectInlineAdvice`).
The audit has found no constraint linking those answers to one tape; none is needed, because one tape can be rebuilt from them.

The premises are bundled in
[Soundness/Assumptions.lean](../JoltConstraints/Soundness/Assumptions.lean):
`JoltField F` (`2^128 - 2^64 < ringChar F`, with constraint (63) on below `2^128`); `JoltInstance.SoundnessAssumptions`
(`RamRegionFits`); and the temporary
`JoltInstance.TemporaryRestrictions` (`TracerAddressChecks`,
`HostCallsSucceed`, `NoMaxLengthTrace`, `TerminationThenStall`, `PanicStoresOne`,
`ClaimsNoPanic`).
On 2026-10-10, Ari approved `RamRegionFits`: for the instance's layout and
successfully computed maximum RAM size, `lowest + 8 * maxRamSize ≤ 2^64`.
**NOTE: to confirm with a16z.** The definition is in
[Layer3/Layout.lean](../JoltConstraints/Soundness/Layer3/Layout.lean).
This restricts the instance's maximum padded RAM region, not its execution runs.
Together with `ConstraintContext.ramSizeBounds`, it bounds all eight bytes of
every in-domain word. Layer 5b recovers integer address sums from satisfying
constraints, including the unselected address-zero case; the argument applies
to both fixed-tape and independent-answer execution. The former run-based
RAM no-wrap predicate and its next-step helper have been deleted.
On 2026-10-10, Ari approved excluding `SC.W` and `SC.D` from every source row while their advice mismatch was unresolved ([a16z/jolt#2037](https://github.com/a16z/jolt/issues/2037)).
PR #2039 fixed that mismatch, the SC rows go through the ordinary row steps, and no proof used the restriction, so Ari removed it on 2026-11-03.
No proof used the premise `CodeUnchanged`, so Ari removed it on 2026-11-03; that a program does not change its own code (a16z/jolt#1952) remains a modeling assumption, recorded in `model_review.md`.
Stopping is proved in Layer 7, and the panic cases are covered by the temporary `PanicStoresOne` and `ClaimsNoPanic` restrictions.
Ari approved `TracerAddressChecks`, a temporary program restriction for both
LD and SD. It covers the input/advice-store counterexample reported in
[a16z/jolt#2044](https://github.com/a16z/jolt/issues/2044), following
[#2041](https://github.com/a16z/jolt/issues/2041), and four separate candidates:
stores at zero, the I/O padding gap, stores to the stack canary, and accesses
at or above `heap_end`. Each remains individually tracked in Layer 5b below;
#2044 does not establish a counterexample for any of those four cases.
The definition is in
[Layer5/MemoryAccessRestriction.lean](../JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean).
The restriction covers LD and SD; Ari approved on 2026-11-02 extending it to the floor-row accesses as a temporary premise (constraints.md, migration item 10).
For every private input and initialized prefix under relaxed tape semantics,
with honest internal runtime advice and no earlier PC stall, the next attempted
LD or SD must pass `Mmu.effective_address_ok` at the addresses the tracer checks:
the starting address for ordinary RAM, every byte for device memory. This
includes accesses generated by narrower instructions and atomics. The attempted row need
not execute successfully; an abort therefore cannot make the restriction
vacuously true. The predicate contains no witness columns.

The restriction depends on the program and inputs of the instance; it is an
explicit theorem premise, not a new field of the instance or a verifier check.
Its FIXME links #2044 and the four candidates, and calls for narrowing or removal
as each case is resolved, the model reflects its resolution, and the corresponding
unrestricted proof is established. This replaces the earlier restriction on
input/advice stores alone; the theorem does not accumulate both premises.
It assumes precisely these address assertions, not successful LD/SD execution
or table agreement.
The proof derives alignment and excludes peripheral addresses separately, in Layer 5b.
The known panic, termination and stopping discrepancies are covered by the `PanicStoresOne`, `ClaimsNoPanic` and `TerminationThenStall` restrictions, and stopping is proved in Layer 7.
On 2026-10-10, Ari also decided to treat every advice-tape answer as untrusted for the planned soundness theorem, pending a16z's confirmation. Retain the fixed-tape specification for completeness and add the relaxed specification alongside it, as recorded in Layer 5a.
On 2026-10-15, Ari decided the theorem keeps the fixed-tape language. Jolt's tracer reads one tape, in order; "untrusted" means the prover chooses its contents, which the ∃ over private inputs already allows. The relaxed specification stays, as a proof device.
On 2026-10-10, Ari chose to model Akita separately. On 2026-11-10, after a16z/jolt#2403 made `p = 2^128 - 1780711455` Jolt's production field, the model took in Akita's one extra relation instead: the canonical lookup-address check, constraint (63), on when the characteristic is below `2^128`. The theorem now covers fields with characteristic above `2^128 - 2^64`, including BN254 and Akita's field. The audit in Layer 4 records the argument.
PCS security, commitments, and opening protocols are outside the current proof scope.
`reports/2026-10-29-soundness-statement-audit.md` checks that the modeled constraints are the ones Jolt's verifier checks.
They are, except that Lean requires untrusted-advice words to be 64-bit values (its finding 1).

## Key ideas

### The trace comes from running the program

`w` holds field elements, not machine states, so the steps of the relaxed trace `T` cannot be read off it.
`T` starts from the state the instance and the private inputs give.
Each step's state after follows the chosen execution semantics: the existing `execInstr` for fixed-tape runs, and `execWithTapeAnswer` for runs with independent tape answers.
Once the private inputs are chosen, nothing else is free: Jolt's tracer computes the runtime advice, such as a division's quotient, from the state.
The exception is a VirtualAdvice step of a registered inline, whose word comes from `inline_advice`.

### Choosing the private inputs

Keep the `untrusted_advice` from the `privateInputs` supplied to `AllConstraintsOnBytes`; the context already binds initial RAM to those inputs.
The witness gives one answer at each tape read, and no constraint ties the answers to a tape.
The proof runs on these answers under the relaxed semantics (Layer 5a), then rebuilds one tape from them (Layer 7):
- The tape is the answers' low bytes, laid end to end in read order: 1 byte for `AdviceLB`, 2 for `AdviceLH`, 4 for `AdviceLW`, 8 for `AdviceLD`. It holds exactly the bytes read, so no read runs out.
- A narrow answer may have high bits no tape can give, such as 300 for a 1-byte read. The expansion keeps only the low bytes. `AdviceLB rd` is `VirtualAdviceLoad rd 1`, then `VirtualMULI rd rd 2^56`, then `VirtualSRAI rd rd 56` ([ExpansionsAutomated.lean:1180-1190](../JoltBytecode/JoltISA/ExpansionsAutomated.lean)); `AdviceLH` and `AdviceLW` use 48 and 32. With the answer 300 = 0x12C, or with the tape byte 0x2C, `rd` holds 0x2C · 2^56 after the second row and 44 after the third.
- So the rebuilt run differs from the relaxed one only in the tape, and in the destination register (v40 when `rd` is x0) between the first and second rows of a narrow read. Every source instruction ends with the same registers and memory, so the outputs and panic flag are the same.

PR #2049 removed `bytes_remaining()`, the only instruction that could see the tape's length. Before it, the answers could disagree with every tape (Layer 5a, historical candidate).

The relaxed run uses the honest tracer's runtime advice at every advice step outside a registered inline (`BuiltinAdviceHonest`).
An inline's advice step keeps the word the witness records; the proof collects those words into `inline_advice` at the end (`collectInlineAdvice`, `honest_of_builtin`).
In a division expansion, the witness's advice may differ; the `*Program_sound` theorems still give the honest machine state after the expansion.
`RepresentsRows` does not compare instruction temporaries, so `rem a0, a1, zero` can use witness advice 5 and honest advice 0 while preserving the required observations.
At the previous model revision `43cc043`, SC.W could report failure where
Jolt's tracer reported success. The current model uses PR #2039's deterministic
comparison, and no restriction excludes the SC rows.

### The witness proves facts about the execution prefix

The main lemma extends an execution prefix while preserving `Agrees w t prefix state`, defined below.
It connects the prefix and its current state to these witness columns:

- **Bytecode selection:** `PC` and `BytecodeRaChunk`. A slot is an index into the bytecode as `w` sees it: slot `i + 1` holds `bytecode[i]`, and slot 0 and the trailing unused slots are no-ops.
- **Registers:** `RegistersVal r t`, the value `w` says register `r` holds before cycle `t`; the read selectors `Rs1Ra`, `Rs2Ra` and write selector `RdWa`; and the values `Rs1Value`, `Rs2Value`, `RdWriteValue`.
- **RAM:** `RamVal a t`, the value `w` says the memory word at RAM index `a` holds before cycle `t`; `RamAddress`, the selector `RamRa`, and the values `RamReadValue`, `RamWriteValue`. `RamValFinal a` is the claimed value at RAM index `a` after all cycles.

`OrdinaryRamAgreement` compares every ordinary-RAM table entry with the
interpreter's byte-map word. Device-region entries need a separate relation,
as described below.
The register table is compared over [live registers](#register-agreement-must-be-over-live-registers).
The columns not listed above need not be unique.
Individual helpers that accept a plain `Trace`, such as `TraceWitness.PC`, can be reused when stating agreement.

For a fixed-tape trace `T : HonestTrace`, `f(T) := T.honestWitness params` is the modeled extraction at `w`'s `params`. An analogous extraction for relaxed traces is optional; the soundness proof uses column agreement directly.

### Execution cycles and padding

Let `N := params.traceLength`.
Call cycle `t < N` a padding cycle when `w.InstructionFlags .IsNoop t = 1`.
The first pseudo Noop marks padding, but the retained execution prefix can end earlier at its first stable stall.
The prefix includes that stall row, or ends at padding or the last witness cycle if no stall occurs.

**Noop source audit:** rechecked at Jolt revision
`8bbb2357890928d8f83b00ca542879077c4d3d28`, the pseudo instruction
`jolt-riscv/src/instructions/i/noop.rs` does carry `IsNoop`. It is absent from
the modeled `JoltISA.Instr` constructors. No branch of
`jolt-program/src/image/decode.rs::decode_instruction` or its instruction-kind
helpers returns `SourceInstructionKind::NoOp`; the `NoOp` arm in `operands`
only handles an already-supplied kind. Nonzero compressed ELF instructions are normalized
and passed through that decoder too. Expansion's `expand/operands.rs::noop_for`
emits `ADDI x0, x0, 0`, which has `IsNoop = false`, rather than the pseudo Noop.
Preprocessing inserts pseudo Noops for slot 0 and trailing padding and maps a
pseudo Noop to slot 0. Thus the model's real-row/padding distinction matches
these decoded programs. If we later model manually supplied pseudo Noops or
additional inline instruction kinds, revisit this distinction. This source
audit resolves the TODO in `metadata.lean`; it is not the Layer 6 suffix proof.

This definition does not establish the shape of the suffix after the retained prefix.
Layer 6 proves that every retained cycle selects a real bytecode row, as part of `soundness_execution_prefix_agreement`.
Layer 7 (`Layer7/StallSuffix.lean`) proves that the witness may repeat the stable source instruction before padding begins, that repeated stall rows leave RAM unchanged, and that the retained run stops at its final row.
The case with no padding includes the last witness cycle in the retained prefix when no stable stall occurs earlier.

### Agreement is proved by induction on the step

Use the private inputs chosen above, including the tape answers taken from the witness, for the whole execution.
At the start of a source instruction, `advance_pc` sets `PC` to that instruction's address and `nextPC` to the address plus its length, 2 or 4 bytes.
Within an expansion, the next row instead starts directly from the previous row's post-state.

Use a predicate `Agrees w t prefix state` on a plain execution prefix under the untrusted-answer semantics and its current state, before constructing a completed relaxed trace.
Write `n` for the retained prefix length; here `0 ≤ t ≤ n`, and `prefix` contains exactly the `t` rows already executed.
For `t < n`, `state` is the pre-state for executing row `t`, with `advance_pc` already applied when that row starts a source instruction.
For `t = n`, `state` is the last post-state, or the initial state if `n = 0`; no further `advance_pc` is applied.
For `t < n`, `state.sail.regs.get? Register.PC = some selectedRow.address` for
the row selected at `t`. Jolt's tracer uses the row's own address for AUIPC,
while the Lean interpreter reads Sail's PC; JAL, JALR and branches need the
same equality.
The predicate records successful execution and linkage of the prefix, agreement with the witness columns for its executed rows, and the runtime-advice equality required by `advice_from_honest_tracer` for each of those rows.
State agreement is retained through the endpoint `t = n`:

- For `t ≤ n` and `t < N`, compare `RegistersVal r t` with the corresponding register value in `state` for every [live register](#register-agreement-must-be-over-live-registers) `r`. Compare `RamVal a t` with `state` for every ordinary-RAM index `a`; device indices need the separate relation below.
- At the cut, `RepresentsPrefix.cutRam` requires RAM agreement for every RAM index except the termination word, including input, advice, output and panic words.
- For `t = n = N`, compare `RamValFinal a` with the final state's RAM encoding for every RAM index `a` except the termination word. There is no `RegistersVal` column at cycle `N`.

Also retain `AllRegistersPresent state.sail`: agreement with `sourceValue`
alone would not ensure a successful read, because that function defaults missing
architectural registers to zero. `Layer5/Registers.lean` defines the register
portion as `RegisterAgreement`, proves it for the initialized state, and
preserves it through PC preparation and destination writes. Register presence
is a proved induction invariant, not an added soundness premise.

The RAM comparison must account for address remapping and the device regions.
Device indices cannot be compared by equality with readable device memory
after every store: termination ignores writes, and panic reads a flag rather
than the stored bytes. Its device cases need a separate invariant relating
table history, permitted reads and final public I/O; Layer 5b proves it
(`Layer5/DeviceMemory.lean`).
The predicate also records that the prefix's tape answers are the witness's answers at its tape-reading rows.
For `t < n`, it requires the slot `w` selects at cycle `t` to be:

- the entry slot when `t = 0`;
- the slot immediately after the previous row's slot when the previous row has rows of its expansion left (`virtual_sequence_remaining.getD 0 ≠ 0`);
- the first slot of the source instruction at the previous post-state's `nextPC` otherwise.

For example, suppose `n ≥ 2`, cycle 0 selects `ADDI x5, x0, 7`, and cycle 1 reads `x5`.
`Agrees w 1 prefix state` then says both that `state` holds 7 in `x5` and that `RegistersVal x5 1` is its field encoding; the register-read equation forces cycle 1's read to return that value.

There are two induction obligations:

1. **Initialization:** the constraints select the entry slot, zero the register table, and supply the initial RAM. Use `initial_state_sourceValue` to show that the initial state's general-purpose and virtual registers are also zero. For `n > 0`, apply the entry instruction's `advance_pc` and prove that it preserves these register and RAM values. For `n = 0`, keep the initial state. Establish agreement for the empty prefix.
2. **Extension:** for `t < n`, use agreement at `t` and the required advice compatibility to prove that the step succeeds under the untrusted-answer semantics and returns a post-state matching the step's writes. Prove the new row's runtime-advice equality and preserve those for earlier rows, together with the tape-answer facts. If `t + 1 < n`, use the next slot and pre-state specified above to establish agreement at `t + 1`. If `t + 1 = n`, retain the post-state and establish the endpoint table comparisons above.

At a tape-reading step, recover a 64-bit answer from the witness and use it directly; agreement with one tape comes later, when Layer 7 rebuilds it.
At an internal runtime-advice step (`VirtualAdvice`), the relaxed run uses the honest tracer's advice, which need not equal the witness's advice.
For division expansions, the `*Program_sound` theorems give agreement with the honest machine state after the expansion, and `RepresentsRows` omits temporary-register comparisons within it.
Local extension lemmas may take these facts as hypotheses; their application must justify them from the constraints, possibly using other rows of the same expansion.
These proofs work with the prefix and its state, before a completed relaxed trace exists.

## Workflow for each obligation

1. State the property and identify the exact constraints expected to enforce it.
   Start from an arbitrary satisfying witness. For model-dependent facts, check
   the Lean definitions against Jolt's code and record the checkout revision.
2. Try to prove the property with the existing premises. Examine boundary cases
   alongside the proof: field wraparound, unused address bits, absent reads or
   writes, padding, and the first and last cycles, as relevant.
3. If the proof stalls, distinguish a missing lemma, a model mismatch, an overly
   strong intermediate claim, and a constraint weakness. A free value is a
   security problem only if it permits behavior outside the claimed language.
   A counterexample to a subset of constraints need not satisfy `AllConstraints`.
4. For a suspected bug, construct the smallest counterexample, trace its effect
   on the claimed execution or outputs, and reproduce it against Jolt's code. Record
   whether the actual verifier accepted a proof. Preserve the reproducer; after
   a fix, rerun it and close the corresponding Lean obligation.

Use small lemmas and the default heartbeat limit; do not raise `maxHeartbeats`.
If an obligation is blocked, raise the exact missing fact or counterexample for discussion.
Do not add premises to the soundness theorem or instance without Ari's
permission, or change the language just to close a proof. Record each obligation
as proved, proof gap, model mismatch, intermediate claim to revise, or bug, with
its evidence and next step.
A proof counts as closed only after compilation and checking its dependencies
for remaining `sorry`s or unjustified axioms.
Run `#print axioms` on each layer's top lemmas and on the final theorem.
The axiom policy allows the three standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`, plus these named, uninterpreted Sail
constants declared in [`RiscvExtras.lean`](../LeanRV64D/RiscvExtras.lean):

| Constant | Role |
| --- | --- |
| `sys_enable_experimental_extensions : Unit → Bool` | Sail configuration flag |
| `load_reservation : Arch.pa → Nat → SailM Unit` | Reservation update hook |
| `match_reservation : Arch.pa → Bool` | Reservation query hook |
| `cancel_reservation : Unit → SailM Unit` | Reservation cancellation hook |
| `valid_reservation : Unit → Bool` | Reservation validity query hook |

These constants have inhabited types and impose no proposition about their
behavior. A proof that uses no additional assumptions about them holds for
every interpretation of them, with the semantics in its statement interpreted
accordingly. They cannot supply an unproved fact about execution, such as a
reservation hook preserving state or agreeing with Jolt's reservation model.
Such behavior still needs a proof; this policy does not authorize new soundness
premises or resolve the LR/SC equivalence gaps.

Forbid `sorryAx`, native-evaluation or compiler-trust axioms such as
`Lean.ofReduceBool` and `Lean.trustCompiler`, and every dependency outside this
list. A further Sail constant must be checked and explicitly named in this
policy before accepting a proof that depends on it; being declared with `axiom`
in a Sail file is not sufficient. Record the exact constants used by each layer
and by the final theorem. Prefer narrower lemmas when they avoid dependencies
the current proof does not need.

The `noEarlyNextPCChange` field of `expand_program_rows_valid` depends on
`sys_enable_experimental_extensions`. That dependency is acceptable under this
policy, and `#print axioms JoltInstance.soundness` lists it. Layer 2 uses the narrower row-validity and canonicality
facts and therefore still has only the standard three axioms.
Before using instruction-equivalence results in Layer 5b, check their actual
dependencies: `RiscvInstruction.lean` and `Mret.lean` contain unfinished cases,
and the LR/SC modules document the reservation hooks declared in
`RiscvExtras.lean`. The quoted `axiom` lines in those module comments are not
additional declarations. Importing a module alone does not introduce a proof
dependency, but using its results can.

## Proof layers

Proofs live in `JoltConstraints/Soundness/Layer0/` through `Layer8/`, matching the
layers below. Create each directory as its proofs are added. The final theorem
stays in `JoltConstraints/Soundness/soundness.lean`.
Algebraic helpers shared across layers live in `JoltConstraints/Soundness/Helpers/`.
Layer 5 has two parts: 5a adds the relaxed semantics for tape answers, used inside the proof, and
5b proves execution steps, one file per instruction family in `Layer5/`.
At Lean HEAD `7096dca`, all layers were proved and `JoltInstance.soundness` had no `sorry`.

Layers 0 to 4 prove field bounds, selection, table histories and lookup facts.
Layer 5a adds the untrusted-answer semantics alongside the fixed-tape semantics and proves inclusion; the execution-prefix induction in Layers 5b and 6 then takes tape answers from the witness.
Runtime-advice agreement is established when extending the prefix and retained in `Agrees`.
Layer 7 collects the execution and advice facts, proves the stopping obligations, assembles the relaxed trace and rebuilds one tape from its answers, giving an `HonestTrace`; Layer 8 proves `matches_outputs`.

### Layer 0: field elements to numbers

What: distinct natural numbers below the field's characteristic stay distinct in the field, and each comparison needs a bound showing both sides are below it.
Also derive `2^chunkBits < ringChar F` from the verifier's setup check and `charAbove2pow127`.
Why: constraints are equations over the field `F`, but registers and memory hold 64-bit words.
To conclude `a = b` from `(a : F) = (b : F)`, both must be below the characteristic.
The existing Layer 0–1 lemmas use only `charAbove2pow127 : 2^127 < ringChar F`, which covers 64-bit words but not every 128-bit integer. Their bounds stay unchanged; the base soundness theorem supplies `charAbove2pow128Minus2pow64 : 2^128 - 2^64 < ringChar F`, which with constraint (63) gives the 128-bit address bound needed in Layer 4 (`identityAddress_lt_char`). `two_pow_127_lt_char` in `Layer0/Field.lean` provides the bridge; Layer 2's zero-lookup and x0 proofs already use it.
The chunk-width bound ensures that one-hot Hamming-weight sums cannot wrap in the field, so their field values determine the number of selected entries.
Uses: `charAbove2pow127`, `ConstraintContext.oneHotFitsSetup`, bounds on parameters and expressions.

### Layer 1: selection

What: (a) at each cycle, the bytecode chunks and instruction-lookup chunks are one-hot, and the RAM chunks are one-hot or all zero as `RamHammingWeight` says.
(b) Every cycle selects exactly one bytecode slot, and each `InstructionRa` lookup selector selects exactly one address.
`InstructionRa` is not committed: it is rebuilt from small chunks and has an address domain of `virtualChunkBits` bits. This use of "virtual" in the parameter name is unrelated to virtual instructions.
For RAM, the full selector is all zero exactly when `RamAddress` is zero; otherwise it selects exactly one RAM index.
The all-zero RAM case has zero read and write values and zero per-word increments.
(c) Each sum of the form "table entry times selector" collapses to the selected entry, or to zero for an all-zero RAM selector.
The lookup equations use the product of the `InstructionRa` selectors over a full 128-bit address; reconstruct that unique address before collapsing their sums.
Why: this identifies the bytecode slot `w` selects at cycle `t`, including no-op slots, and its registers, immediate and flags.
Later layers use this selection.
Uses: Booleanity, Hamming weights, `oneHotFitsSetup`, address encoding.

### Layer 2: registers

What: the register table is all zero at cycle 0.
From cycle `t` to cycle `t + 1`, only cycle `t`'s destination register changes, and it changes to `RdWriteValue t`.
A register read at cycle `t` returns the table's value at cycle `t`.
Prove separately that the x0 table entry stays zero: for every cycle,
`RdWa x0 t * RdInc t = 0`. The selected bytecode destination can be x0, while
Sail discards writes to x0. Derive
`JoltInstructionRow.Valid.x0DestinationIsNoOp` through
`ExpansionRows.expand_program_rowOk` and `ExpansionRows.RowOk.valid`, then use
the canonical no-op's constraints to prove the increment is zero.
Both of these narrower lemmas have only the standard three axioms. Prefer them
to the larger [`expand_program_rows_valid`](../JoltConstraints/trace_interface.lean)
bundle for this fact: its `noEarlyNextPCChange` field depends on
`sys_enable_experimental_extensions`. That named Sail constant is allowed by
the axiom policy above, but Layer 2 does not need it.
Validity must be proved from the program, not assumed from an honest trace.

**Proof order:** prove the small lookup fact needed for x0 within Layer 2(b),
before its cycle induction; the general lookup semantics stay in Layer 4.
When the selected row is `ADDI x0, x0, 0` and the current x0 table entry is zero,
the source-read and instruction-input equations give
`RightLookupOperand = Rs1Value + Imm = 0`. This row has identity RAF, so Layer 1(c)
and `charAbove2pow128` force its selected 128-bit address to zero. Prove that
the `RangeCheck` entry there is zero; the row's `WriteLookupOutputToRD` flag
then gives `RdWriteValue = LookupOutput = 0`. The write-value equation and the
induction hypothesis imply `RdInc = 0`. Other destinations and padding leave
the x0 entry unchanged. These lookup facts use selection and the field bound,
not a general register-history or execution theorem, so this order avoids a
circular dependency. The current x0 value being zero is an induction hypothesis,
not a new soundness premise.

For initialization, connect the zero table to the initial state's registers using [`initial_state_sourceValue`](../JoltConstraints/execution_facts.lean).
This existing lemma takes an `initial_state` equation and a source register; it does not require an `HonestTrace`.
Prove the connection for every register-table index using the register-address map, and prove that `advance_pc` preserves these values.
Prove the required encoding/decoding identities and injectivity on **canonical**
source and destination operands, using
[`register_encoding.lean`](../JoltConstraints/register_encoding.lean) and
[`register_address.lean`](../JoltConstraints/witness_helpers/register_address.lean).
Architectural registers occupy indices 0–31, and canonical virtual registers
occupy 32–127. The raw constructors can alias (for example, x0 and virtual
register 0), so unrestricted injectivity would be false. Derive each row's
operand canonicality from `ExpansionRows.expand_program_rowOk`'s `canonical`
field via `context.expands`. This is the narrower route to the fact also bundled
in `ExpansionRowsValid.registerOperandsCanonical`. Use those identities when
transferring a table update to the corresponding execution-state register.
Why: this makes the register table behave like a register file, so it can be compared with the registers in the run's state.
Uses: `RegistersValEqPrefixRdInc`, the register read and write equations, Layer 1.

Part (a) contains field-valued initialization, reads, and updates in
`Layer2/Registers.lean`. Part (b) adds the zero-lookup fact in `ZeroLookup.lean`,
the x0 induction in `ZeroRegister.lean`, the canonical index map in
`RegisterMap.lean`, and initialization and `advance_pc` agreement in `State.lean`.
Both parts are proved and Ari's Layer 2 review corrections have been addressed.
Agreement after executing an instruction remains part of Layer 5b.

### Layer 3: RAM

What: the RAM table starts at the instance's initial memory, which includes the untrusted advice.
Each cycle changes at most the word it accesses, a read returns the table's value, and `RamValFinal` is the initial RAM plus every increment.
Reuse `sum_before_succ` from
[`Soundness/Helpers/PrefixSum.lean`](../JoltConstraints/Soundness/Helpers/PrefixSum.lean)
for the RAM prefix sums; Layer 2 already uses this shared lemma for registers.
Cycles that do not touch memory and the remapping of addresses to RAM indices must be accounted for.
Prove the last-cycle update into `RamValFinal`, as well as updates between `RamVal` columns.
If the per-word increments `RamRa a t * RamInc t` vanish for `n ≤ t < N`, prove `RamVal a n = RamValFinal a` when `n < N`; the Layer 7 stopping proof discharges that condition for stall replays and padding.
Also prove that `advance_pc` preserves the RAM encoding used in agreement.
The initial state's layout must equal the context's public layout, so the RAM
indices in the initial-state and address-remapping lemmas refer to the same base.
The proved state lemmas compare the initial image and preserve every observation
of the memory map and device under `advance_pc`. They do not identify later
device reads with the last stored word: that execution obligation remains in
Layer 5b, including the known panic and termination discrepancies.
`ram_zero_effects` now supplies the zero-address updates;
the unused overlapping `ram_read_of_address_zero` lemma was removed.
Why: this does for memory what Layer 2 does for registers.
`RamValFinal` is also where `w` holds the output bytes.
Uses: the RAM equations, `ConstraintContext.initialized`, Layer 1.

**Address wraparound, derived from `RamRegionFits` (NOTE: to confirm with a16z):**
the address lemmas take `encoded : RamAddress = raw.toNat`.
The load/store constraint adds `Rs1Value` and the signed immediate in the field,
while execution wraps the sum at 64 bits. The layout premise states
`lowest + 8 * maxRamSize ≤ 2^64`. The verifier's RAM-size check then bounds the
entire witness RAM domain, including every byte of its last word.

[Layer5/MemoryAddress.lean](../JoltConstraints/Soundness/Layer5/MemoryAddress.lean)
derives `encoded` as follows. Write `base` for a 64-bit base-register value,
`imm` for the immediate, and `S := base.toNat + imm.toInt`, an integer.

1. The selected LD/SD bytecode row supplies the active Load/Store flag and the
   signed immediate column. Given source-column agreement, the address
   constraint yields `RamAddress t = (S : F)` without assuming no wrap.
2. If RAM index `c` is selected, recover `S = lowest + 8 * c` as integers. If
   every RAM selector is zero, recover `S = 0`. In both cases, shift the two
   integers by `2^63` into `[0, ringChar F)` before applying cast injectivity.
   Word and signed-immediate bounds justify that interval even when `S` might
   initially be negative. Equality of field residues alone is not enough.
3. The layout bound gives `0 ≤ S < 2^64` for a selected word; the zero case
   has the same bounds. Thus `((base + imm).toNat : Int) = S`.
4. Substitute that integer equality into the field equation to obtain
   `encoded`. Since the `c6703570` migration, `AccessRow.address_encoded`
   (`Layer5/MemoryRows.lean`) does this for LD, SD and the floor rows,
   discharging the flag, immediate and AddressOffset facts from the selected
   row; source agreement remains an execution-induction obligation.

For example, base `2^64 - 8` with immediate 8 gives `S = 2^64`. Under the new
layout premise, no satisfying LD/SD cycle can have these operand values. The
premise imposes no condition on unconstrained execution runs. In the selected
case, `c < ramSize ≤ maxRamSize` also puts all eight bytes below `2^64`.
Proving the actual memory instruction succeeds, including at address zero,
remains separate from this arithmetic result.

`MemoryLayout.new` and `maxRamSize` alone do **not** imply
`lowest + 8 * ramSize ≤ 2^64`. The kernel-checked example in
[layout_check.lean](../bug-report/ram-address-wraparound/layout_check.lean)
uses zero I/O, advice and stack sizes, an 8-byte program, and heap size `2^63`.
The layout succeeds with `lowest = 2^31 - 16` and
`heap_end = 2^63 + 2^31 + 136`; `maxRamSize = 2^61`. Its padded domain contains
the aligned byte address `2^64`. A source value `2^64 - 8` plus immediate 8
would address that word in the field equations but wrap to zero in execution.
This refutes the proposed bound from those checks; it is **not** a witness
satisfying `AllConstraints` or a reproduction against Jolt's verifier.

The source recheck at `8bbb2357` finds the same relevant arithmetic in
`common/src/jolt_device.rs::MemoryLayout::try_new`,
`crates/jolt-program/src/preprocess/ram.rs::compute_max_ram_k`, and the RAM-size
checks in `crates/jolt-verifier/src/verifier.rs`.
The same wrap breaks completeness: [ram-address-wrap.md](../bug-report/ram-address-wrap.md) shows the honest witness failing the address constraint when the address wraps.
Soundness needs no run-level no-wrap premise: it uses the instance-only
`RamRegionFits` and derives no-wrap at satisfying LD/SD cycles (below).
Completeness still needs one: `honestWitness_ramAddrEqRs1PlusImmIfLoadStore`
is a `sorry` whose TODO calls for ruling out wrapping addresses.
For completeness, ask a16z to confirm that Jolt programs never compute a
wrapping load or store address.

### Layer 4: lookups

What: when a cycle uses a lookup table, recover the table and its operands from `w`, and show the lookup output is that table's operation on them.
Why: the constraints never compute an instruction's result directly; for example, ADDI's result reaches `rd` as a lookup output.
To match the run's state after a write with `RdWriteValue`, the lookup output must be the real operation.
Uses: the instruction read-raf equations, Layer 1, pure table identities.

Work in reviewable parts:

- **(a) Table selection and arithmetic RangeCheck:** identify the table from
  the selected bytecode slot (including absent tables and padding), recover an
  identity-RAF address, and interpret addition, biased subtraction and full
  multiplication followed by the low-64-bit RangeCheck table. The input-word
  agreement hypotheses are local obligations for Layer 5b; they are not added
  to the soundness statement. This part is proved.
- **(b) Interleaved operands:** recover the two 64-bit operands when the RAF
  flag is zero, then connect bitwise and comparison tables to their operations.
  Operand recovery, evaluation at the recovered address, and the bitwise and
  comparison table interpretations are proved and reviewed.
- **(c) Remaining tables and uses:** connect W operations, upper-word results,
  aligned addresses, shifts, rotations, extraction and assertion tables, and
  discharge the remaining instruction-input and lookup-output uses. Reuse pure
  table identities without assuming an already-executed trace. This part is now
  proved and reviewed. Shift-mask shape and agreement with the run's source
  values remain local obligations for Layer 5b, which composes these lookup
  lemmas with execution; they are not soundness or instance premises.

Advice rows need a different argument from arithmetic rows. Their `Advice` flag
sets identity RAF, but exempts the right lookup operand from equality with the
right instruction input. Choose the address supplied by
`instructionLookupRa_unique`, use `lookupOutput_of_selected_bytecode`, and apply
`rangeCheck_entry` to obtain its low 64 bits. This proves that the lookup output
encodes a word; no input-determined `encoded` hypothesis is available for
`lookupOutput_rangeCheck_of_identity`. At the lookup level, any 64-bit word is
possible; constraints elsewhere in the program may restrict it.
Layers 5–7 construct the relaxed run with honest runtime advice (`VirtualAdvice`), while the witness's division advice may differ.
The `*Program_sound` theorems give the honest machine state after each division expansion, and `RepresentsRows` does not compare instruction temporaries.
Tape answers (`VirtualAdviceLoad`) are untrusted under the Layer 5a decision.

**Field-scope audit before this layer:** an identity-RAF row
(`InstructionRafFlag = 1`) equates the full lookup address with the right operand
only in the field. For Akita's prime `p = 2^128 - 1780711455`, both `s` and
`s + p` fit in 128 bits when `s < 1780711455`; they have the same field encoding
but different `RangeCheck` outputs. The base equations alone therefore do not
support an injectivity argument from the former `2^127 < ringChar F` premise.
This is an obstruction to the proposed argument, not a constructed witness
satisfying every constraint.

Jolt revision `8bbb2357890928d8f83b00ca542879077c4d3d28` retains the guard addressing this
alias in its Akita build. In
`crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs`,
`CANONICAL_INSTRUCTION_ADDRESS = cfg!(feature = "akita")`, and
`upper_half_all_ones` is the product of the upper 64 address bits.
`crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs` adds the
`gamma^3` coefficient for this predicate times `InstructionRafFlag`; the input
claim has no corresponding coefficient. In the deterministic, non-succinct
relation this contributes a zero constraint for each cycle. At a selected
identity address it rules out an all-ones upper half, hence gives
`address < 2^128 - 2^64 < p`. Both prover and verifier Cargo features enable
`jolt-claims/akita`. This rules out the proposed alias in that build; this audit
read the code and did not run an end-to-end forged proof.

On 2026-10-10, Ari approved restricting this theorem to `2^128 < ringChar F` and
modeling Akita separately. On 2026-11-10 a16z/jolt#2403 made
`p = 2^128 - 1780711455` Jolt's production field, so the model now includes the
guard as constraint (63) of the [constraint checklist](../JoltConstraints/constraints.md)
(`Constraints/InstructionAddressCanonical.lean`). The constraint is on exactly when
`ringChar F < 2^128`, matching Jolt, whose `akita` feature both selects the fp128
field and turns the guard on. `JoltField` is now `2^128 - 2^64 < ringChar F`.
`identityAddress_lt_char` (Layer 1) puts every identity-RAF address below the
characteristic: at characteristic `2^128` or more trivially, and below it because
(63) rejects addresses at or above `2^128 - 2^64`. Layer 4 recovers a full lookup
address from a value below `2^128 - 2^64` (`instructionLookupRa_of_identity`'s
`valueBelow`); adds, subtracts, products of two words and widened words all are.
The upper-half guard alone would not cover every characteristic above `2^127`;
the `2^128 - 2^64` bound is the one it needs.
An audit of the `akita` build at `c97e9300` and at a16z/jolt `d2aacbe08` found no
other relation it drops or weakens: its fused increment and digit-zero
hamming-weight encodings only re-encode or add constraints. PCS security is outside
this scope.

### Layer 5: advice tape and execution

#### Layer 5a: untrusted advice-tape answers

**Where tape instructions come from.** No RISC-V instruction expands to a tape instruction.
`VirtualAdviceLoad` comes from Jolt's custom source instructions (opcode `0x5B`):
`AdviceLB`, `AdviceLH`, `AdviceLW` and `AdviceLD`
([`expansions.lean`](../JoltConstraints/expansions.lean)). These are the SDK reads
used by `#[jolt::advice]`. PR #2049 removes `bytes_remaining()` and the
`VirtualAdviceLen` source and final-row constructors.

**Advice contract.** Ari's decision of 2026-10-10 treats tape answers as
untrusted: the prover chooses the tape's contents. On 2026-10-15 Ari decided the
theorem keeps the fixed-tape language, which already allows any tape.
PR #2049's revised documentation explicitly states that the proof
does not authenticate a runtime tape length or require all supplied advice to
be consumed. Guest checks must establish the intended relation on every
successful path. The original question about `bytes_remaining()` is resolved
by removing that API and instruction, as recorded in
[Questions for a16z](#questions-for-a16z), item 1.

**Two specifications to retain.** Keep the existing fixed-tape execution, including its cursor and [`readAdviceTape`](../JoltBytecode/JoltISA/AdviceTape.lean), for Jolt's actual tracer and completeness.
The separate untrusted-answer execution, used inside the soundness proof, is
`execWithTapeAnswer`. `UntrustedAnswerRun.answers` supplies a finite sequence
indexed by executed rows; answers on non-tape rows are ignored. These answers
are private existential data in `UntrustedAnswerLanguage`. The induction will
take them from the witness. The original `JoltPrivateInputs` and initial state
are retained, including tape bytes and the cursor, so fixed-tape inclusion can
preserve every state exactly. The relaxed load rule advances the cursor but
does not read the tape bytes or enforce exhaustion.
A free answer must be allowed to be any 64-bit word, because the constraints only range-check the advice row's value; the honest `readAdviceTape` result has zero high bits for a narrow read.
Check that each narrow-load expansion uses only the low bytes of that row's value, so the guest still sees a value of the declared width.
Prove that every fixed-tape run gives an untrusted-answer run by taking its actual read values as the answers, preserving the executed rows, register and RAM values, outputs and stopping behaviour.
This proves inclusion of the fixed-tape language in the relaxed language.
The reverse direction, rebuilding one tape, is proved in Layer 7 (`untrustedAnswerLanguage_implies_inLanguage`).

**Shared trace requirements.** `UntrustedAnswerRun` and `UntrustedAnswerTrace`
currently duplicate the linkage, initialization, preprocessing, internal-advice
and stopping requirements of `ValidRun` and `HonestTrace`. A change to either
original structure must be reviewed in its relaxed counterpart, especially a
future fix to Jolt's stopping rule. Fixed-tape inclusion alone does not
detect every divergence: weakening a relaxed requirement could leave inclusion
provable. A later refactor may share these fields through a structure
parameterized by the execution rule; this review does not require that refactor.

**Premise decision, 2026-10-10.** Ari approved replacing the run-based RAM
no-wrap assumption with `RamRegionFits`, the instance-only bound
`lowest + 8 * maxRamSize ≤ 2^64`. **NOTE: to confirm with a16z.**
The former predicate and next-step helper are removed. This avoids quantifying
over either fixed-tape or relaxed runs: the no-wrap fact is derived only at
satisfying LD/SD cycles, by the integer argument in Layer 3 above.
The bound and its use in the proof are recorded in `model_review.md`.

Both trace specifications execute the expanded bytecode rather than fetching instructions from memory.
That a program does not change its own code is what relates this to Jolt's tracer; it is a modeling assumption, not a premise.
After reviewing Layer 5a, Ari approved this premise replacement and continuing
with Layer 5b. The later approved device-store restriction is recorded above
and in Layer 5b below.
The two execution specifications and the updated upstream contract are recorded
in `model_review.md`. The main theorem targets the fixed-tape language;
this ISA update does not change that statement. The inclusion lemma alone
cannot establish soundness for that target; Layer 7 also rebuilds one tape.

**Why one tape can be rebuilt.** No tape need give the witness's exact
answers: a relaxed narrow load admits high bits that the finite-tape read cannot
return. The generated post-processing removes them from the guest-visible
result, so the tape of the answers' low bytes gives the same registers and
memory at the end of every source instruction
([Choosing the private inputs](#choosing-the-private-inputs)). With
`bytes_remaining()` removed, no instruction can see the tape's length.
The [modeled metadata](../JoltConstraints/metadata.lean) still gives
`VirtualAdviceLoad` the `Advice` flag and a `RangeCheck` lookup.
[`rightLookupEqRightInputOtherwise`](../JoltConstraints/Constraints/RightLookupEqRightInputOtherwise.lean)
still leaves its right lookup operand unconstrained by the instruction input.

**Historical length-query candidate, removed by PR #2049.** At revision
`43cc043332762034b5f65379441576e06e7a3890`, two `bytes_remaining()` queries with
no intervening read could apparently answer 3 and then 100: no cross-query
constraint was found, but no complete satisfying witness was constructed.
No fixed tape gives those answers. The audit checked the Advice flags,
RangeCheck lookups, R1CS exemption and native expansion of `VirtualAdviceLen`.
PR #2049 acknowledges that its answer was not tied to tape contents or reads
and removes the instruction; it does not add a tape-consistency constraint.
The current source type cannot express this example. Advice-load expansions,
including their sign extension and x0 temporary-register branch, are unchanged.

#### Layer 5b: one execution step

Files: one per instruction family in `JoltConstraints/Soundness/Layer5/`; the
dispatcher that composes them is `row_step` (`Layer6/RowStep.lean`).

What: for `t < n`, given `Agrees w t prefix state` and the step's advice compatibility facts, prove that the step succeeds under the untrusted-answer semantics and returns a post-state matching the witness's writes.
When `t + 1 < n`, combine this with Layer 6's next-row selection and `advance_pc` rule to extend agreement.
At `t + 1 = n`, prove the endpoint table comparisons using Layer 3's update equations, including the update into `RamValFinal` if `n = N`.
This is proved one instruction family at a time, with the bounds needed to interpret register and RAM values as 64-bit words.
Use `RegisterAgreement.read` for a canonical operand's successful read and
table encoding. After deriving an instruction's successful destination write
and the equality of its value with `RdWriteValue`, use
`RegisterAgreement.write` to obtain the next cycle's register agreement.
It derives destination canonicality from the selected bytecode row and handles
x0 with Layer 2's zero-table invariant. These local execution and value facts
remain obligations of each instruction family; the shared write lemma does
not establish them. It applies when `t + 1 < N`, since there is no register
table at cycle `N`.
[AddImmediate.lean](../JoltConstraints/Soundness/Layer5/AddImmediate.lean)
now discharges these local obligations for ADDI. Its `addi_step` derives
source/immediate encodings, the addition and write flags, and the RangeCheck
table from the selected row, then proves execution and next-cycle register
agreement. The result is the wrapped 64-bit sum; no arithmetic no-wrap premise
is needed. Its execution and write-value conclusions also apply at the last
cycle. Every other instruction family has a local step too, and Layer 6
composes them.

**Device-memory obligations.** These are three cases of a broader obligation:
derive both successful memory access and the device's value from the RAM
constraints. Consistent RAM history alone does not establish either one.
The source audit below records the findings first made at Jolt revision
`43cc043332762034b5f65379441576e06e7a3890`; the device and memory-unit
behaviour was rechecked at `5def437f` in `reports/2026-10-29-soundness-statement-audit.md`.
Layer 5b proves both from the constraints and the restrictions below (`Layer5/DeviceMemory.lean`).

**Termination-device restriction.** Banning
all termination accesses would exclude normal SDK exits: the SDK writes byte 1,
whose SB expansion loads the enclosing word before storing it.
`JoltInstance.TerminationThenStall` now checks every private input and ready
relaxed prefix after a completed store touching termination. An attempted LD
must avoid all eight termination bytes, an attempted JAL must have offset zero,
and JALR is excluded. The generated return path in
`jolt-sdk/macros/src/lib.rs:882–887` writes that byte and then stalls; its
load-before-store expansion is `sbProgramAuto` in
`JoltBytecode/JoltISA/ExpansionsAutomated.lean`. This checks compatibility of
that exit sequence, not the property for every SDK guest: the guest body,
panic paths and other exit paths must also be checked. The RAM invariant
distinguishes the termination table entry from readable device memory.
`termination_next_jal_stalls` proves a zero-offset JAL actually leaves
`nextPC` at its own address.
The last-real-row argument is proved in `Layer7/LastJump.lean` and `Layer7/TerminationStore.lean`.

Any proposed restriction must be a property of the program under every allowed
private input and every reachable prefix of relaxed execution, including
arbitrary tape answers. It must describe the program's accesses, not witness
flags. A restriction intended to ensure access succeeds must cover the
attempted next access as well: quantifying only over successfully completed
runs would miss a store that aborts. The load/store address restriction below
and the termination restriction follow this rule, and the soundness proof uses
both.
Any such temporary premise must carry a comment of this form:

```text
FIXME: Temporary workaround for the termination-device mismatch tracked in
https://github.com/a16z/jolt/issues/1950 and
https://github.com/a16z/jolt/issues/1951 (item 2).
Remove this restriction once the upstream mismatch is resolved, the Lean model
reflects that resolution, and the unrestricted proof is established.
This is a temporary theorem restriction, not a verifier check or intended
permanent requirement on guest programs.
```

The local store/load discrepancy does not by itself demonstrate an accepted
cheating proof. No complete satisfying witness for that consequence has been
constructed.
This restriction does not resolve the panic or input/advice-store obligations, or stopping for "panicked" claims; those are covered by `PanicStoresOne`, `TracerAddressChecks` and `ClaimsNoPanic`.

**Panic word.** In
`common/src/jolt_device.rs:121–155`, a write to the first panic byte sets the
flag regardless of the value, and writes to the other panic bytes are ignored.
Every byte load in the panic region returns the flag. The RAM table instead
retains the stored bytes. Even storing the word 1 leaves different later word
reads: the device returns `0x0101010101010101`, while the table holds 1.
Separately, storing zero still sets the device flag; final public I/O represents
that flag as the word 1. Thus forbidding later panic reads alone would not
settle final panic agreement. The Lean `JoltDevice.load?` and `store?` match
these rules. Layer 5b handles both the read invariant and the final flag,
using the temporary `PanicStoresOne` restriction (write-up:
`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`).

**Input/advice stores: reproduction reported in #2044; temporary restriction added.** Jolt's
`tracer/src/emulator/mmu.rs:143–157` permits device stores only to output,
panic or termination. Stores to input, trusted-advice or untrusted-advice
regions abort. Lean's `Mmu.effective_address_ok` and `Mmu.store_raw?` enforce
the same restriction. These are memory regions, distinct from relaxed
runtime tape answers; relaxing those answers does not permit these stores.

We found no constraint ruling out these stores in the audited RV64 constraints
(`crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`), RAM read/write and value relations,
or public-output relation (`crates/jolt-claims/src/protocols/jolt/relations/ram/`).
`RamOutputEqPublicIo` fixes only final input values. Advice regions lie below
the public-I/O mask, as in `crates/jolt-program/src/preprocess/public_io.rs:23–24`.
The initial report was [#2041](https://github.com/a16z/jolt/issues/2041).
Ari's follow-up [#2044](https://github.com/a16z/jolt/issues/2044) reports an
accepted-proof reproduction at `00508a09`: the unchanged tracer aborts at the
first input store, while a modified tracer permits stores to input and both
advice regions, reads the new values back, restores the original bytes, and
outputs 7, 9 and 11. The unchanged verifier accepts in clear/Dory mode.
This report has been read, including its patch; it has not been independently
rerun in this proof session. Relative to the tracer's semantics, acceptance of
that claim is a soundness failure: no valid completed execution produces it.

**Four further candidates from the same address-check mismatch.** These are
separate from #2044 and from one another. The original local code audit was at
`43cc043`; the relevant MMU checks and device behavior were rechecked unchanged
at `5def437f` in `reports/2026-10-29-soundness-statement-audit.md`.
None has a constructed witness satisfying all constraints or an accepted-proof
reproduction. The temporary premise must not be used as evidence that these
cases are impossible under the constraints.

1. **Store zero at address 0.** In layouts where zero is outside the writable
   device regions, the tracer rejects the store. A witness address of zero
   selects no RAM word; Layer 1's `ram_zero_effects` forces both read and write
   values to zero and leaves the RAM table unchanged. Thus storing zero is a
   local candidate for an aborting instruction represented as a no-op in the
   witness. A load at zero is a different case: the modeled tracer can return
   zero there, so the temporary premise permits that load when its checks pass.
   Next check: a fixed zero-store instruction followed by a normal exit; verify
   the full constraint bundle, including source values, bytecode and stopping.
2. **The I/O padding gap `[io_end, RAM_START_ADDRESS)`.** Rounding the I/O
   allocation up to a power of two can leave unused words in this interval
   inside the witness's RAM domain. Device access checks reject bytes strictly
   above `io_end`. The check uses `≤ io_end`, so an LD starting exactly at
   `io_end` fails on a later byte; an SD there fails the writable-region check
   already at its first byte. Next check: choose a generated layout with a
   nonempty gap and test the first gap word as separate load and store cases
   against all constraints, including the final public-I/O mask.
3. **Stores to the stack canary `[stack_end, stack_end + STACK_CANARY_SIZE)`.**
   The tracer rejects a RAM store whose starting address lies in this interval;
   loads are allowed. The RAM table treats it as ordinary memory, and no
   corresponding store prohibition was found in the audited constraints.
   Next check: select an aligned word starting inside the canary, establish
   that its RAM index is in-domain, and test a complete store witness.
4. **Loads or stores starting at or above `heap_end`.** The tracer rejects
   them, but the maximum padded witness domain can extend beyond `heap_end`.
   The RAM domain bound alone therefore does not establish the tracer's bound.
   Next check: compute an allowed witness size with an aligned in-domain word
   starting at or above `heap_end`, then check complete load and store witnesses.
   Keep this distinct from a word that starts below `heap_end` but straddles it:
   ordinary RAM doubleword accesses check only the start, and the backing
   allocation is rounded to whole words.

**Approved workaround:** `JoltInstance.TracerAddressChecks` excludes attempted
LD/SD accesses failing the modeled address assertions while the remaining proof
proceeds. `UntrustedAnswerRun.NextStep`
describes a prefix and the row about to execute, including the empty-prefix,
within-expansion and next-source-instruction cases. It requires honest internal
runtime advice and rules out continuing after a PC stall, but imposes no
success condition on the next row. `DoublewordAddressChecks` calls the existing
`Mmu.effective_address_ok`: once at the starting address for ordinary RAM,
and at each of eight byte addresses for device memory. This is the distinction
in `Mmu.load_doubleword` and `Mmu.store_doubleword`, matching Jolt's
`mmu.rs:619–635,729–748`. Requiring all eight ordinary RAM bytes to pass would
strengthen the tracer's rule at an unaligned heap or canary boundary.
`LoadRow.address_checks` and `StoreRow.address_checks` (`Layer5/MemoryRows.lean`)
extract these facts before their respective execution proofs. They do not take
successful execution as a hypothesis.

The SDK's
generated return stores byte 1 to termination (`jolt-sdk/macros/src/lib.rs:882`),
and its panic handler stores byte 1 to panic (`:903`); their expanded stores
remain allowed by the address checker. This checks compatibility with those
generated paths, not a proof of the premise for every SDK guest. Guest code
using advice as an address must meet the checks for every allowed answer.

**Limits of the premise.** `effective_address_ok` is the tracer's address-assertion
check, not its whole memory interpreter. The proof derives alignment and
register access separately. Below RAM, `load_raw?` and `store_raw?` also reject
hard-coded unsupported peripheral ranges; `Layer5/DeviceMemory.lean` shows the
constraints never select them, using the layout, the RAM-address constraints and
`RamRegionFits`. The premise does not resolve the panic/termination value
mismatch or stopping. Narrow or remove the premise as each case above is
resolved and proved; both its definition and the main theorem carry that FIXME.

For a runtime-advice step, justify the local lemma's advice hypotheses using the relevant expansion constraints; a tape-reading step takes its answer from the witness.
For `AdviceLB`, `AdviceLH` and `AdviceLW`,
[AdviceExpansion.lean](../JoltConstraints/Soundness/Layer5/AdviceExpansion.lean)
now proves the source expansion shapes and full execution of their
`VirtualAdviceLoad`, `VirtualMULI` and `VirtualSRAI` rows in order. Both the
ordinary-destination and x0 temporary-register branches are covered. The
proofs derive the shift constants from the generated programs, establish
register-value linkage, and apply `narrowAdvice_value` at widths 8, 16 and 32.
`execProgramWithTapeAnswers` composes the existing per-row execution rule,
using local expansion row indices. Layer 6 establishes that the witness
selects these rows in order, relates its answer to the first row, and keeps
register and RAM table agreement through their intermediate states.
For a load or store row (LD, SD or a floor row), use `AccessRow.address_encoded`
with the approved `RamRegionFits` premise and the source-column agreement
from the induction. It derives the signed integer equality, nonwrapping bound,
natural alignment and the accessed doubleword's encoding. For ordinary RAM,
`load_ram_step` and `store_ram_step_agreement` then prove the access succeeds and
matches the RAM table; device accesses are proved in `Layer5/DeviceMemory.lean`
(`load_device_step`, `store_device_step`).
Preserve the tape-answer facts and the runtime-advice equalities in `Agrees`; prove that appending a row leaves the earlier rows' `honestTracerAdviceAtStepN` values unchanged.
Why: this supplies the transition for the induction step and the proof required by the eventual `executes` field.
Uses: Layers 0 to 4, Layer 5a, instruction semantics, runtime-advice compatibility.

Before each family's execution lemma, prove a small metadata lemma from the
selected bytecode row and its instruction constructor. It should identify the
lookup table, RAF value, input-source flags and relevant output flags. Derive the
operand words separately from `Agrees`, Layers 2–3 and the input-selection lemma;
metadata alone cannot establish agreement with the run's state.

| Instruction family | Local Layer 4 obligations to discharge |
|---|---|
| Arithmetic, including W operations and MULHU | Derive the arithmetic flag, table and RAF one from the row; recover the two input words and use `rightLookupOperand_add/sub/mul` to derive the wide `encoded` address |
| Bitwise, XOR rotations, comparisons, conditional operations and extraction | Derive the table and RAF zero; use `lookupOperands_eq_inputs_of_raf_zero` and source agreement to obtain both lookup-operand encodings |
| Powers, shift masks, alignment, byte reversal and window masks | Derive the table and addition mode; recover the source/immediate words and derive the identity address before applying the word-table lemma |
| Immediate and register shifts | Derive the table and RAF zero; prove mask shape from `immShiftOk` for an immediate, or expansion linkage and the preceding mask-producing row for a register shift |
| Advice rows | Derive the RangeCheck table and Advice flag; recover a word with `lookupOutput_rangeCheck_word`, then handle tape answers or internal runtime-advice correctness under the appropriate execution rule |
| Assertions, register writes and branches | Derive the Assert, WriteLookupOutputToRD or Branch flag from the row; apply the corresponding output-consumption lemma after interpreting the lookup |

These are lemmas to prove within Layer 5b, not premises to add to the soundness
statement or the instance. Keep the metadata lemmas grouped by family and split
further when a family has different operand modes. Compose those proved facts
with the state-transition lemma.

**Layer 5b was closed at `7096dca`.** It uses these restrictions for suspected Jolt bugs:
- `TracerAddressChecks` supplies the address checks for attempted LD/SD rows.
  Narrow or remove it as the address cases documented above are resolved.
- Host calls that fail in Jolt's tracer but pass the constraints as no-op
  rows: `HostCallsSucceed`.
- The termination word, where the device ignores stores and loads 0 while the
  RAM table keeps the stored bytes: `TerminationThenStall`, whose load clause
  forbids loading that word after storing to it.
- The panic word, where Jolt's tracer sets its flag on any store and loads the flag in every byte, while the RAM table keeps the stored bytes: `PanicStoresOne` (added 2026-10-20).
  Every store to the panic word stores 1, and no load reads the panic word after such a store.
  Before any store, the device and the table both read 0.
  Write-up: `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`.
- Stopping early on a "panicked" claim, where the witness's last cycle before the padding can be any JAL or JALR: `ClaimsNoPanic` (added 2026-10-20), which limits the theorem to "no panic" claims.
  Write-up: `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md`.
- Both are Jolt bugs that must be fixed in Jolt; neither may remain a restriction.

SC.W and SC.D go through the ordinary row steps, so no restriction excludes them.
The global register-agreement induction uses the per-expansion write-before-read fact `ExpansionFacts.expand_temps_ok`; Jolt's allocator gives instruction temporaries 40–47, disjoint from the reservation registers 32 and 33.

Runtime advice honesty must not become a restriction.
The relaxed run uses the honest tracer's advice, but a witness may use different division advice with the same architectural result: for example, every quotient advice value passes `rem a0, a1, zero`.
This non-uniqueness is not a soundness bug.
The bytecode project's eight `*Program_sound` theorems establish advice uniqueness for DIV, DIVU and DIVW, and the final Sail state for REM, REMU, REMW, REMUW and DIVUW.
`RepresentsRows` excludes instruction-temporary comparisons; expansion liveness ensures that a later expansion overwrites each temporary before reading it.

Do not add a new FIXME restriction for unfinished proof work.

### Layer 6: control flow

What: prove entry selection and the two next-slot rules in `Agrees` for every retained cycle up to and including the first stable stall, or up to padding or the final witness cycle when no stall occurs.
After the cut, the witness may repeat the stall's whole source expansion before padding begins.
That stall-replay suffix, padding persistence and the zero per-word RAM updates `RamRa a t * RamInc t = 0` after the cut are proved in Layer 7 (`Layer7/StallSuffix.lean`, using `padding_persists` and `padding_from` in `Layer6/BytecodePC.lean`).
Handle `n = 0` and `n = N` explicitly.
Why: Layer 5b handles the state; this handles which bytecode row runs next.
It supplies the `starts` and `linked` fields; Layer 7 connects the cut boundary to stall replays and then the no-op suffix.
Uses: the PC and sequence constraints, Layer 5b.
Layers 5b–6 are proved; see [Current top-level status](#current-top-level-status-2026-10-23).

**Entry and interior slots.**
[BytecodePC.lean](../JoltConstraints/Soundness/Layer6/BytecodePC.lean)
proves that cycle zero selects the preprocessed entry slot, including the
address-zero case. A nonlast virtual row selects the following bytecode slot
on the next cycle: the proof uses constraint (18), the shifted expanded PC,
the unique bytecode selector and injectivity of slot encodings below the field
characteristic. For an interior next row, the shifted virtual/first flags and
constraint (19) force `DoNotUpdateUnexpandedPC` on the previous cycle. After
excluding a padding predecessor by selecting a real row, this supplies the
nonlast-virtual condition. Finally `selected_registerShift_fed` combines that
adjacency with the checked expansion's `ShiftPairs` fact, proving the previous
selected instruction feeds the register shift's mask.

**Entry address zero:** neither the [program image type nor entry preprocessing](../JoltConstraints/program.lean) excludes it; `get_first_pc` maps it to slot 0.
The earlier tracer initialized `prev_pc` to 0 and could produce no rows at entry address 0.
PR #2109, merged as `0249591a`, starts `Cpu.stalled` as false (`jolt/tracer/src/emulator/cpu.rs:441-453` at `5def437f`), but a first fetch at address 0 may still fail because address 0 is not program memory.
`get_first_pc` still maps address 0 to the no-op entry, as checked in `crates/jolt-program/src/preprocess/bytecode.rs:224-232`.
We have not established whether `AllConstraints` admits such an instance.
Soundness does not need to rule it out: the cut allows a zero-row prefix, and the completed run's nonemptiness comes from the proved `soundness_termination_store_exists`.
The proof does not assume a positive entry address; a completed soundness run has at least one row because its termination store executes.

### Layer 7: the relaxed trace and the rebuilt tape

What: use the prefix constructed on the supplied untrusted advice and the tape answers from the witness.
Take the successful execution, linkage and runtime-advice equalities from `Agrees w n prefix state` for the relaxed trace's counterparts of the `HonestTrace` fields.
L also requires two facts about the rebuilt trace: Jolt's prover accepts it (it ends in a jump, its RAM addresses are at or above the lowest address, and its padded length is at most the maximum), and none of its spoil asserts fails.
The required stopping obligations are `stops` (the final source instruction is a stable self-jump), `runs_until_stop` (no earlier source instruction is a stable self-jump), and unconditional `nonempty`, derived from the termination store.
The rule follows a16z/jolt PR #2109 at merge commit `0249591a`: a self-jumping JALR with destination equal to its nonzero base register continues if re-execution would jump elsewhere.
The execution prefix is cut at its first stable self-jump, or at padding or the last witness cycle if no stable stall occurs.
The stopping proof `soundness_stopping` (`Layer7/Stopping.lean`, with `StallSuffix.lean`, `LastJump.lean` and `TerminationStore.lean`) proves the cut ends at a stable stall and that later witness rows stay on its source instruction with zero RAM updates; it does not depend on `sorryAx`.
The execution-prefix lemma owns RAM agreement at the cut, and the stopping lemma owns the final RAM comparison.
The temporary `TerminationThenStall` and `ClaimsNoPanic` restrictions address the separate case of a witness that stops early at a jump (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md`).
Take the instance facts, including `initialized`, from the context; Layer 5a left `JoltPrivateInputs` unchanged. `accepted` follows from `expands` and `entryIsRust`.
Then rebuild one tape from the answers' low bytes, in read order, and run the program on it. Prove that this run is an `HonestTrace` with the same bytecode rows, ending every source instruction with the same registers and memory ([Choosing the private inputs](#choosing-the-private-inputs)).
Why: once all these obligations are resolved, the constructed prefix can be packaged as a relaxed trace, and the rebuilt tape turns it into an `HonestTrace`, the form the theorem concludes.
Uses: the context, Layers 5 and 6, stopping proofs.

`rebuild_rows` (`Layer7/TapeRebuild.lean`) constructs all six fields directly, using a shared masking proof for every narrow width.
`narrow_load_shape` is proved from the expansion checker's `advicePairsOk` and the generic adjacent-row lift (`Layer7/AdjacentRows.lean`), which also proves register-shift pairs.

### Layer 8: outputs

What: use `Represents.finalRam`, which the Layer 7 stopping proof obtains by carrying the cut RAM comparison to `RamValFinal` across stall replays and padding.
Helper B (`soundness_matches_outputs`) proves this layer without `sorryAx`.
Translate the agreed RAM encoding on the public I/O region into the final device's output bytes and panic flag.
Then use `RamOutputEqPublicIo` to prove that the final device has the instance's output bytes, after trimming trailing zeros, and its panic flag.
For an empty trace, use the initial device.
In the panic-store discrepancy, a store of 0 to the panic word sets Jolt's tracer's flag but leaves 0 in the RAM table, so a false "no panic" claim passes (`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`).
It no longer blocks this step: B needs no panic restriction, and the burden now sits in the execution prefix's `cutRam` at the panic word, where the temporary `PanicStoresOne` restriction excludes it.
Why: this gives `matches_outputs` for the relaxed trace. The rebuilt run has the same final device, so it carries over to Layer 7's `HonestTrace`, which proves the theorem's existential conclusion.
Uses: endpoint agreement from Layers 5b–6, Layer 3's suffix lemma, `RamOutputEqPublicIo`, device semantics.

### Obligations that need particular care

- **Chunk selection alone does not establish address selection.** With 5-bit addresses and
  two 4-bit chunks, one-hot digits `(2, 0)` encode 32, outside the domain `0…31`.
  The full selector is then zero throughout that domain. Layer 1(b) now rules
  this out for bytecode. For RAM, it proves that an all-zero selector forces
  `RamAddress`, read and write values, and all per-word increments to zero.
  Layer 5b justifies execution of zero-address instructions separately; the
  RAM-table facts alone are not a soundness proof for those instructions.
  This example alone is not a satisfying witness for `AllConstraints`.
- **Field-valued histories are not machine states.** Layers 2–3 prove update
  equations; Layer 5b establishes and preserves their interpretation as machine
  words. This relies on every initial RAM word being a 64-bit value, which
  Jolt's verifier does not check for untrusted advice
  (`reports/2026-10-29-soundness-statement-audit.md`, finding 1).
- **Lookup reuse must not assume execution.** `lookupEntryCorrect_*` takes an
  `HonestTraceRow`, which already includes a proof of execution. Reuse pure identities such
  as `and_entry`; separately prove the connection to arbitrary witness operands.
- **Local execution does not establish honest advice or termination.** Running a
  `VirtualAdvice` row with a supplied value does not show that the honest tracer
  supplies that value.
  The shape of padding and the stopping rule, needed before interpreting the witness as a complete relaxed trace, are proved in Layer 7.

## Questions for a16z

Collected here so they can be sent together. Soundness findings go to a16z
privately, as Markdown files over a Slack channel, not as public GitHub issues
(decided 2026-10-16). Each item states what we assume meanwhile.

1. **Resolved by removal: the guarantee of `bytes_remaining()`.**
   Michael's [PR #2049](https://github.com/a16z/jolt/pull/2049) removes the API
   and `VirtualAdviceLen`, acknowledging that its result was only range-checked
   and not tied to reads. The revised documentation says tape length and
   exhaustion are tracer bookkeeping, not proof guarantees. Our ISA now
   includes that removal. The original 3-then-100 example remains historical
   audit evidence, without a complete satisfying witness.
   Fixed-tape and relaxed execution remain separate specifications; both language inclusions between them are proved.
2. **Can we assume the RAM region `[lowest, lowest + 8·maxRamSize)` fits below `2^64`?**
   This bounds the verifier's maximum padded RAM domain, including every byte
   of its last word. We use it with the RAM-size check and the address
   constraints to derive nonwrapping addresses for satisfying LD/SD cycles,
   independently of the tape specification.
   Assumed meanwhile: `RamRegionFits`, approved by Ari on 2026-10-10.
   NOTE: to confirm with a16z.
3. **Will the constraints enforce the MMU's input/advice write permissions?**
   Asked in [#2041](https://github.com/a16z/jolt/issues/2041); Ari's
   [#2044](https://github.com/a16z/jolt/issues/2044) now reports an accepted
   proof despite the tracer's rejection. If these permissions are instead only
   a tracer restriction, the intended verified execution semantics needs to
   state that explicitly. This is separate from termination (#1950/#1951 item 2)
   and the panic-store case.
   Also open: whether and how the verifier enforces the separate zero-store,
   I/O-gap, canary-store and heap-boundary cases listed above. These four remain
   code-reading candidates, without complete witnesses.
   Assumed meanwhile: the approved temporary `TracerAddressChecks` premise,
   with a FIXME to narrow or remove it as each case is resolved and proved.
4. **Temporary restrictions added since, each needing a write-up for the batch.**
   - `HostCallsSucceed`: host calls that fail in Jolt's tracer pass the
     constraints as no-op rows.
   - `TerminationThenStall`: a witness that stops early at a jump, and the
     termination word's device/table mismatch.
   - `PanicStoresOne`: a store of 0 proved as "no panic", and loads of the panic word after a store.
     Written up in `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md`.
   - `ClaimsNoPanic`: stopping early on a "panicked" claim.
     Written up in `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md`.
   - `NoMaxLengthTrace`: Jolt's verifier accepts a full-length witness that Jolt's prover cannot produce.
     Written up in `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/prover-verifier-trace-length/index.md`.
   - Each finding gets its own post under `LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/`.
