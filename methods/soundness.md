---
title: Plan for deterministic, non-succinct soundness
---

Our goal is to make Jolt secure through formal verification. Each intermediate
claim should give us a reusable proof or expose an edge case we can investigate
and fix.

Read these before beginning work:

1. [The high-level account of Jolt](https://randomwalks.xyz/blog/jolt-qed/01-jolt-why/).
2. [The completeness proof and bug-finding workflow](./constraint_proving.md).
3. [Known model gaps and proof obligations](../JoltConstraints/model_review.md).

The local `blog/` is stale; use the published article for background.

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
Track every new `sorry` in `model_review.md` under "Proofs owed". This
replaces the order agreed on 2026-10-16 in
[Order of the remaining work](#order-of-the-remaining-work).

### The argument in brief

Read this before the layers below; the rest of this document fills it in.

- **The relation.** `AllConstraints joltInstance privateInputs witness` is a
  predicate on the witness alone, a table of field elements indexed by cycle.
  The instance and private inputs enter only as fixed data: the expanded
  bytecode, the initial RAM, the public I/O and the entry slot
  (`ConstraintContext`). No trace appears in it.
- **The language.** `JoltInstance.InLanguage` says there exist private inputs
  and an `HonestTrace` on them whose final device has the claimed outputs and
  panic flag (`matches_outputs`), which Jolt's prover accepts, and whose spoil
  asserts all pass. Stopping at the PC stall is part of `HonestTrace` itself.
- **The existential.** The private inputs are the given untrusted advice and a tape built from the values the witness records at its tape-read cycles.
  The given tape cannot be used: no constraint reads it (`AllConstraints.advice_tape_irrelevant`).
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

### Current top-level status

`JoltInstance.soundness` chains four named helpers in `Soundness/TopLevel.lean` to get the relaxed language, then applies the reverse inclusion from Layer 7 to get `InLanguage`.
Helper A returns an `UntrustedAnswerTrace` represented at every actual row.
`Represents.finalRam` covers every RAM index except the termination word.
Helper B checks the output and panic words through constraint 26 and final RAM agreement, with no panic restriction.
Its relaxed-trace frame, output-bound and decoder support statements are proved.
The plain-`Trace` final RAM overlay and byte-store output bound are proved.
The generic pre-state frame and shared trace and instruction frames are proved.
The word-index geometry is proved.
The ten Ari-approved trace-independent refactor statements are proved.
Step (a) shares the output, prover-acceptance and spoil-assert predicates on the plain `Trace` between both languages.
Its fixed-tape inclusion is proved, and the reverse inclusion `untrustedAnswerLanguage_implies_inLanguage` in Layer 7 is proved without `sorryAx`.
Helper A is proved from execution-prefix agreement and the assembled stopping theorem.
Layer 8 and Layer 7's stopping and tape rebuild are proved; Layer 7's helpers C and D are not.
`plain_row_step_other` is proved for scalar, branch and tape-load rows without `sorryAx`; see the [completion report](layer6/plain-row-other-report.md#completion-after-the-tape-load-correction).
`division_expansion_layout` is proved in `Layer6/DivisionLayout.lean` with its statement unchanged, and `division_block` now has no `sorryAx` dependency; see the [division layout report](layer6/plain-steps-and-layout-report.md#completion-after-the-module-placement-correction).
Layer 6 proves `soundness_execution_prefix_agreement` by strong induction over source instructions; the step between two sources, `expansion_finish`, and the start of the run are proved.
Helper C remains `sorry` but is no longer known false: the base verifier floor excludes short witnesses, and the approved `noMaxLengthTrace` restriction excludes a run that fills the largest permitted power-of-two domain.
The exact obligations and validation are under [Proofs owed](../JoltConstraints/model_review.md#proofs-owed).
Step (c)'s five original stopping gaps are proved after Ari approved the checker integration.
The four sequence checks, native JALR guard and singleton advice check are integrated, and the materialization lift is proved.
`Emission.lean` has been deleted; stopping uses the single expansion checker.
The approved shared helper `expand_program_source_of_row` is proved; row validity and JALR operand forms both use its source-expansion certificate.
The final axiom audit finds no `sorryAx` in `soundness_stopping`; A reaches it only through execution-prefix agreement.
The [integration report](step_c_closing_report.md) records the completed proofs, validation and declaration timings.
The execution-prefix statement is in `Soundness/Layer6/ExecutionPrefix.lean`, and the stopping statement is in `Soundness/Layer7/Stopping.lean`.
The prefix cuts at the first stable stall, padding, or the last witness cycle and owns RAM agreement at that boundary.
The stopping theorem obtains nonemptiness from the proved termination-store lemma, obtains the final stall from the cut or the proved last-jump and termination lemmas, and carries cut RAM agreement to final RAM through the suffix proof.
Step (c) is complete, with `lake build JoltBytecode JoltConstraints` passing 8800 jobs.
The checker elaboration increase from about 11 s to 44 s is deferred cleanup under “Proofs owed.”
The stopping rule mirrors a16z/jolt PR #2109 at merge commit `0249591a`; soundness obtains unconditional nonemptiness from the termination store.
No additional restriction is used for the JALR self-jump case.
The prover-acceptance helper C will use `ConstraintContext.traceLengthFloor` and `JoltInstance.NoMaxLengthTrace` to exclude its two former counterexamples; its last-jump, RAM-address and padded-length proof remains open.
The [handoff](#layer-5b-handoff-updated-2026-10-23) records what already exists at the bottom.

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

Write each issue up as its own post; `blog/README.md` says where posts live.
Posts go to a16z privately, never as public GitHub issues.
A post has: background with quoted Jolt code and a reference link; each constraint as one plain sentence followed by its formula, without references; an example in real RISC-V, with no pseudo-instructions, and made-up addresses in label, PC and instruction columns; the cheating witness; the constraints that matter checked one by one with the values filled in; the final check against the false claim; the false claim and the true claim; and the core issue.
Write plain prose, one sentence per line, with no status labels, and check every quoted line at the pin.
A FIXME restriction for the issue links to its post and says the bug must be fixed in Jolt.

### Register agreement must be over live registers

This is a design point for the induction in `soundness_execution_prefix_agreement`.
`RegisterAgreement` (`Layer5/Registers.lean`) compares every register; HostIO now has no operands and writes no register, so its local step preserves full agreement.
Scratch registers 40 to 47 can still differ between the witness and the honest run after a division expansion (see `methods/advice_fix_report.md`), so live-register agreement is still needed.
A scratch register can retain a different value across native rows that never write it.
`RegisterAgreementOn live` (`Layer5/Registers.lean`) is agreement on a set of live registers: each step requires its source operands to be live and adds its destination.
`BoundaryState` uses the registers that are not temporaries, and `ExpansionState` adds the temporaries already written in the unfinished source (`ExpansionLive`, `Layer6/PrefixState.lean`).
Temporaries 40–47 are dead at every source boundary, by `tempsReadAfterWrite`.

## Running the Layer 6 agents (for Ari)

Layers 5b–6 are done in stages.
Each stage has its own plan, `methods/layer6/stage-N.md`, written only after the previous stage's report has been reviewed, and Claude gives Ari the prompt for the agent.
Up to three agents run at once: agents 2 and 3 are strong models and take the unknown and hard work; agent 1 is a medium model and takes work that follows a known pattern.
Agents work in one checkout on disjoint files, and Claude audits agent 1 most closely.
Each stage ends with a report, `methods/layer6/stage-N-report.md`; read it, with Claude's audit, before the next stage starts.

## Order of the remaining work (2026-10-23)

Unknown areas come first, so that a false statement or a missing restriction shows up early, while there is time for Ari to decide on it.

1. `row_step` for LD and SD on device memory: the input, advice, output, panic and termination words, under the temporary restrictions.
   The restrictions' sufficiency for this is not yet established (see the Layer 5b checklist).
   Stage one step statement per device region, check each against Jolt's device code at the pin, and only then prove them.
2. Helper C's RAM-address part (every RAM address is at or above the lowest address) and padded-length part (with `NoMaxLengthTrace` and the 256-cycle floor).
   Its last-jump part reuses `soundness_last_row_is_jump` (`Layer7/LastJump.lean`).
3. Then the work that follows known patterns: helper D, the three remaining division lemmas, `plain_row_step_other` (the stage 6b port, the branch and `VirtualAdviceLoad` steps, and the wiring), and `row_step`'s other rows (ordinary-RAM LD and SD, HostIO, JAL, JALR).
4. Last, the cleanup list under "Proofs owed" in `model_review.md`.

## Layer 5b handoff (updated 2026-10-23)

This records the step lemmas at the bottom of the proof, one file per instruction family in `JoltConstraints/Soundness/Layer5/`.
They are used top-down by Layer 6's `plain_row_step` and `row_step`.
Local steps exist for most row kinds, counting LD and SD for ordinary RAM only and HostIO under the restrictions.
Missing steps: JALR, the six branches and `VirtualAdviceLoad`.
`VirtualAdvice` has `advice_step` (`Advice.lean`), which writes the witness's range-checked word and makes no honesty claim.
Device-memory LD and SD, and the dispatcher that `row_step` needs, remain open.

Steps take `RegisterAgreementOn live` (`Registers.lean`): each needs its source registers live and adds its destination.
The shared helpers (`RegisterAgreementOn.read`, `.write`, `.noWrite`, `.registerInputs`, `.immediateInputs`, `registerWriteOn_step`) are general, and the full-agreement versions are derived from them.
The eight families the division expansions use are ported (stage 4a); the families for the other plain rows are being ported (stage 6b); LD, SD, HostIO and JAL port with `row_step`.

`Auipc.lean` and `Jal.lean` take local PC and `nextPC` hypotheses; the execution-prefix induction supplies them, and `Jal.lean` uses the approved next-PC no-wrap fact.
HostIO has no operands and writes no register, so `host_call_selected_step` preserves agreement, using `HostCallsSucceed` for successful execution.

Do not add theorem premises without Ari's approval; do not use `native_decide`, `decide +kernel` or a larger `maxHeartbeats`.
`bv_decide` is accepted temporarily under `AGENTS.md`; every use is tracked in the `bv_decide` list under "Proofs owed" in `model_review.md` and must be removed before the proof is final.
Split difficult proofs into smaller lemmas.
The issue write-ups remain for the agreed batch; #2044 discussion waits for Michael's comments.

## Current Jolt pin (2026-10-22)

The current Jolt source pin is [`5def437f21a0006e13c063a03f0b5a7c9b93cd6f`](https://github.com/a16z/jolt/commit/5def437f21a0006e13c063a03f0b5a7c9b93cd6f).
The source-only audit is in [the pin update report](./pin_update_report.md); the prior pin's validated migration remains below as historical evidence.

## Historical Jolt pin and migration (2026-10-15)

Ari selected the latest pulled version on 2026-10-15. That migration used the public
upstream pin [`8bbb2357890928d8f83b00ca542879077c4d3d28`](https://github.com/a16z/jolt/commit/8bbb2357890928d8f83b00ca542879077c4d3d28).
The local merge `1c8aaff2` and generator commit `7dfe8a0f` are unpublished;
their separate tooling provenance and a reproducible generator patch are in
the [migration checklist](./model_update.md), together with all 36 upstream
commits, the six migration chunks and their validation. The migration was
reviewed and adopted. Completeness still uses the corrected sizing policy;
the unused Rust-sizes corollary and its supporting lemmas were subsequently
removed, as recorded in the migration follow-up.
This migration does not discharge the existing proof gaps or native-proof
axioms, whose repair Ari deferred.
The PR sections below describe the previous model's incremental updates.

The earlier warning about removing bytecode chunks was too broad: upstream
removed precommitted program-table chunking, while the bytecode selector chunks
used by Layer 1 remain.
Stopping before the PC stall and fixed-tape reconstruction are now proved in Layer 7; device-memory agreement remains a separate open proof obligation.
New premises still require Ari's approval.

## PR #2049 ISA update (2026-10-15)

The model now also includes the advice-length removal from
[PR #2049](https://github.com/a16z/jolt/pull/2049), audited at production-change
commit `7b311c939eb63bdd6cbb243b432e55023d2b68e9`. This is that specific change
on top of `43cc043` plus PR #2039, not an update to all of current Jolt.

| Operation | Before | After |
|---|---|---|
| `VirtualAdviceLoad dst byteCount` | Reads 1, 2, 4 or 8 bytes in the tracer; fails on exhaustion | Unchanged |
| `VirtualAdviceLen dst src imm` | Writes the unread byte count in the tracer; gives an independent word in the relaxed semantics | Removed from both instruction types and both interpreters |
| `AdviceLB/LH/LW/LD` expansions | Tape load followed by the existing narrow-load processing where needed | Unchanged |

The source dispatch, metadata, witness helpers and exhaustive proof cases lose
the removed instruction's branch. Its dedicated native-row validity lemma is
deleted. No soundness premise, constraint equation or read-width rule changes.
The generated programs are unchanged. Lean starts from decoded source
instructions; it does not model the ELF decoder or serialized instruction tags.
Upstream removes the old decoder case and retires tag `0x0062`, so guests using
`bytes_remaining()` and persisted traces using the old format need updating.

The revised [runtime advice documentation](https://github.com/a16z/jolt/blob/7b311c939eb63bdd6cbb243b432e55023d2b68e9/book/src/usage/runtime_advice.md#security-model)
explicitly distinguishes the tracer's finite tape and exhaustion check from
the proof's untrusted answers. The fixed-tape interpreter remains in place for
completeness, and the relaxed interpreter remains separate. This removal alone
does not prove the fixed-tape soundness target or change it to the relaxed one.

Validation: `lake build` passes for both libraries (8746 jobs). An axiom audit
of 13 declarations covers expansion validity, the completeness lookup-write
lemma, fixed-tape inclusion, narrow-advice execution and the ADDI/XOR/SLTIU
steps. It reports only `propext`, `Classical.choice`, `Quot.sound` and the
allowed Sail constant `sys_enable_experimental_extensions`. Six scratch
examples checked by kernel reduction cover little-endian reads, cursor
increments, an exact-boundary read, exhaustion and invalid widths. No new
`sorry`, axiom, premise or heartbeat override was added. The main soundness
theorem retains its existing `sorry` and fixed-tape target.

## PR #2039 model update (2026-10-10)

Ari reviewed the experiment and approved merging it into `feat/soundness`.
Merge `c42f8f0` preserves both the SC update and the memory-access restriction.
The temporary Lean branch and worktree have been removed. This model includes [PR #2039](https://github.com/a16z/jolt/pull/2039) at
`2a924239c1f99f2e4f2c94a5dae5e403b182b27c`, applied without conflicts to
Jolt `43cc043332762034b5f65379441576e06e7a3890`. It does not import the
other changes on the PR's newer base. That experiment used a generation
checkout at `43cc043` with the applied patch; the current reference pin is above.
PR #2039 has since merged upstream (2026-10-12, `0dad0d9e`) and is in the
current pin `8bbb2357`; migration item 2 found that the merged SC fix agrees
with these expansions ([model_update.md](./model_update.md)).

The reviewed update regenerates all 57 expansion programs with LR/SC
support enabled in `jolt-lean-gen`. Before the patch, all 57 definitions
matched the existing Lean definitions exactly. After the patch, only SC.W
and SC.D change. SC.W goes from 30 to 26 rows in each destination branch;
SC.D goes from 16 to 12 rows in each destination branch (`rd = x0` and
`rd ≠ x0`). Both replace success advice and its one-way
assertions with XOR followed by SLTIU. LR.W, LR.D and the other 53 programs
are unchanged. `honestTracerAdvice` no longer supplies an SC answer, matching
the PR's tracer change. The row-validity proofs take the regenerated programs
without extra assumptions.

The separate commit `e3a34fc` only moves the unchanged LR/SC definitions into
the generated module; it is independent of the proposed SC semantics.
The experiment recorded generator change `cf450ba2` and applied PR `1bac0a87`
in `/private/tmp/jolt-pr2039-rust`. That temporary checkout is no longer
available. Migration item 2 has since added LR/SC coverage to the generator;
all 57 regenerated programs match `JoltBytecode/JoltISA/ExpansionsAutomated.lean`.

Validation for this chunk: `lake build JoltConstraints` passed (8739 jobs).
The existing unfinished theorems remain unfinished; no `sorry`, axiom, premise
or heartbeat override was added. `#print axioms` for `scw_ok`, `scd_ok`,
`expand_ok`, `lookupOutput_xor` and `lookupOutput_unsignedLessThan` lists only
`propext`, `Classical.choice` and `Quot.sound`. `expand_program_rows_valid`
also lists the already-approved Sail constant `sys_enable_experimental_extensions`.
The Rust `jolt-program` and `tracer` suites passed
all 260 tests (nextest marked the canonical-padding-row test as leaky; no test
failed). `cargo +1.95 clippy -p jolt-lean-gen --offline --all-targets -- -D warnings`
and `cargo +1.95 fmt --check -p jolt-lean-gen` passed. This checks the expander
and tracer; no new verifier-acceptance experiment was run.

**Remaining proof work.** `NoStoreConditional` is currently retained.
A successful build of the still-sorried main theorem would not establish
soundness after deleting a premise. Ari has approved removing the premise
for this updated model. The constraint-to-execution proof needs:

1. **Proved in `Layer5/RuntimeAdvice.lean`:** neither destination branch of
   either SC expansion contains a `VirtualAdvice` row. The generic lemma
   `runtimeAdvice_agrees_of_noAdvice` gives `none = none` for any such trace
   row. Applying it during the whole-trace induction remains to be done.
2. Cover the rows SC uses through the ordinary Layer 5b instruction proofs.
   Every SC.W and SC.D row kind now has a local step lemma, with LD and SD
   covered for ordinary RAM only. These proofs
   are also needed for other source programs. Register agreement already
   compares virtual registers 32 and 33 with the run's state, so the XOR/SLTIU
   rows compute the same success bit on both sides without any interpretation
   of LR/SC history. Check both destination branches and source-register aliases
   through these row proofs.
   Composition into the whole SC expansion, and LD/SD on device memory,
   remain open.
3. Remove `NoStoreConditional` and use that ordinary instruction coverage for
   SC's rows. The memory-device and stopping obligations remain separate.

**5b advice bridge and shared steps, 2026-10-15; implemented:**

- `withRuntimeAdvice_eq_of_noAdvice` in `Layer5/RuntimeAdvice.lean` proves
  that supplying runtime advice leaves a row unchanged when
  `instruction.adviceValue? = none`. It is used by both runtime-advice
  agreement and the shared step lemma. `ordinary_withRuntimeAdvice` alone
  would not suffice: it preserves the ordinary flag, not instruction equality.
- `Layer5/LookupWrite.lean` supplied four small lemmas; `RegisterAgreement.rs1Value`
  and `rs2Value` have since moved to `Layer5/RegisterInputs.lean`. They recover selected source-column values using canonical operands
  and register agreement. `lookupWrite_value_of_raf_zero` derives RAF, write and
  table selection from the row, connects input columns to lookup operands, and
  applies the caller's proved Layer 4 rule. `registerWrite_step` proves a
  canonical destination write succeeds and extends register agreement.
- XOR and SLTIU use all of that shared argument; ADDI also uses the final write
  step. Each caller still proves its operand facts, metadata and interpreter
  read/write equation. The shared lemma does not assume successful execution.
  Its local proof obligations are all discharged in these callers, with no new
  soundness or instance premise.

The three public step lemmas now take `advice : row.instruction.RuntimeAdvice`
after the tape `answer`, and their execution conclusion runs
`row.instruction.withRuntimeAdvice advice`, exactly as `UntrustedAnswerRun.executes`
does. They retain the exact post-state, alias coverage and last-cycle execution;
only next-column register agreement requires a following cycle. This changes
the step-lemma API; it does not change either interpreter or the main theorem.

ADDI, XOR, SLTIU, LUI, XORI and VirtualAssertLTE now have step lemmas; ADD,
SUB and MUL share `arithmetic_step`. The other SC.W rows,
`VirtualAssertWordAlignment`, `VirtualAlignAddr`, `ANDI`, `LD`,
`VirtualWindowMaskW`, `VirtualPextSigned`, `ANDN`, `VirtualShiftDataW` and `SD`,
now have local steps too, recorded in the instruction-family chunks below.
SC.D uses rows from both lists. `ld_ram_step` and `sd_ram_step` cover
ordinary RAM; device accesses remain open. Whole-expansion composition, RAM/PC
agreement and the induction remain open.

Relating registers 32 and 33 to Jolt's emulator reservation is a separate
obligation about the model, recorded under **LR/SC reservation correspondence**
in [model_review.md](../JoltConstraints/model_review.md). It is not a prerequisite
for removing `NoStoreConditional` from the constraint-to-execution theorem.

No additional soundness or instance premise is authorized by this model update.
The reviewed SC changes are now part of `feat/soundness`, with Ari's approval.
PR #2039 has since merged upstream and is in the current pin.

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

**Source-language scope.** Both targets cover programs represented by
[`SourceInstruction`](../JoltConstraints/expansion_helpers.lean): the modeled
RISC-V instructions and the listed Jolt custom instructions at opcode `0x5B`.
Jolt's inline/precompile opcodes `0x0B` and `0x2B`, including the SHA-256 and
Keccak inlines, and field-inline opcode `0x7B` are outside that type. The SDK's
`field_to_limbs!` and `field_from_limbs!` emit `0x7B` instructions; the migration
record documents the source check. Any guest containing these instructions is
outside the theorem's scope by construction. This is an existing language restriction,
not an added soundness premise.

An instance is a claim about one program.
It gives the program, its public inputs and trusted advice, and the output bytes and panic flag the program is claimed to produce.
The private inputs are what the prover picks and Jolt's verifier never sees.
In the existing specification they are the untrusted advice, which is loaded into RAM, and the advice tape, which the guest reads while the program runs. The relaxed specification, used only inside the proof, supplies independent answers in the existentially chosen trace (Layer 5a). It retains the tape state for exact inclusion, but the relaxed tape instructions do not consult its bytes or enforce exhaustion.
A step is one row of the expanded bytecode being run; an expandable instruction such as DIV takes several steps.
A witness `w` is a set of tables indexed by `params.traceLength` cycles.
The proof must establish which cycles describe execution steps and which are padding.
In the non-succinct model, the verifier receives `w` in the clear and checks every modeled constraint.

The theorem says: if some `w` satisfies every constraint, then there are private inputs, including one advice tape, and an `HonestTrace` on them whose final device holds the claimed output bytes, after trimming trailing zeros, and the claimed panic flag. Jolt's prover must also accept that trace (`prover_config.isSome`), and none of its spoil asserts may fail (`SpoilAssertsPass`). On 2026-10-15 Ari added these two to `InLanguage`, because Jolt's code says it proves only such runs; L is exactly what Jolt's code says, nothing more or less.
The existing `HonestTrace` describes Jolt's tracer running with a fixed tape: each step's bytecode row, its state before and after, the runtime advice Jolt's tracer computes, and the step where Jolt's tracer stops.
The proof first builds a relaxed trace, which allows independent tape answers while retaining the other execution, internal runtime-advice and stopping requirements. Its definition and the inclusion of fixed-tape traces are implemented in Layer 5a. Layer 7 then rebuilds one tape from the answers, giving an `HonestTrace`.
We aim to preserve the supplied untrusted advice in RAM and choose the tape answers from the witness. The audit has found no constraint linking those answers to one tape; none is needed, because one tape can be rebuilt from them.

The premises are bundled in
[Soundness/Assumptions.lean](../JoltConstraints/Soundness/Assumptions.lean):
`JoltField F` (`2^128 < ringChar F`); `JoltInstance.SoundnessAssumptions`
(`NextPCNoWrap`, `CodeUnchanged`, `RamRegionFits`); and the temporary
`JoltInstance.TemporaryRestrictions` (`NoStoreConditional`, `TracerAddressChecks`,
`HostCallsSucceed`, `HostCallRdZero`, `TerminationThenStall`, `PanicStoresOne`,
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
On 2026-10-10, Ari approved excluding `SC.W` and `SC.D` from every source row,
including unreachable rows, while their advice mismatch was unresolved
([a16z/jolt#2037](https://github.com/a16z/jolt/issues/2037)). PR #2039 has
since fixed that mismatch. `LR.W` and `LR.D` remain allowed.
`NoStoreConditional` is a restriction on this theorem, not a check made by
Jolt's verifier. Its `FIXME` now calls for removal after the remaining SC
device-memory cases and global expansion composition are proved.
The language and instance are unchanged by it.
Stopping is proved in Layer 7, and the panic cases are covered by the temporary `PanicStoresOne` and `ClaimsNoPanic` restrictions; using `PanicStoresOne` for the panic word's cut RAM agreement in the execution-prefix proof is still owed.
This restriction only excludes the SC cases.
Ari approved `TracerAddressChecks`, a temporary program restriction for both
LD and SD. It covers the input/advice-store counterexample reported in
[a16z/jolt#2044](https://github.com/a16z/jolt/issues/2044), following
[#2041](https://github.com/a16z/jolt/issues/2041), and four separate candidates:
stores at zero, the I/O padding gap, stores to the stack canary, and accesses
at or above `heap_end`. Each remains individually tracked in Layer 5b below;
#2044 does not establish a counterexample for any of those four cases.
The definition is in
[Layer5/MemoryAccessRestriction.lean](../JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean).
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
Alignment and raw peripheral dispatch remain separate proof obligations.
The known panic, termination and stopping discrepancies are covered by the `PanicStoresOne`, `ClaimsNoPanic` and `TerminationThenStall` restrictions, and stopping is proved in Layer 7.
On 2026-10-10, Ari also decided to treat every advice-tape answer as untrusted for the planned soundness theorem, pending a16z's confirmation. Retain the fixed-tape specification for completeness and add the relaxed specification alongside it, as recorded in Layer 5a.
On 2026-10-15, Ari decided the theorem keeps the fixed-tape language. Jolt's tracer reads one tape, in order; "untrusted" means the prover chooses its contents, which the ∃ over private inputs already allows. The relaxed specification stays, as a proof device.
On 2026-10-10, Ari chose to model Akita separately. The current theorem covers the base constraint relation over fields with characteristic above `2^128`, including BN254. Akita's prime is smaller and its extra lookup-address guard is outside this relation. The audit in Layer 4 records that distinction.
The separate Akita work will model its field and deterministic, non-succinct constraint relation, including that guard. PCS security, commitments, and opening protocols are outside the current proof scope.
Whether the modeled constraints are the ones Jolt's verifier checks is a separate question.

## Key ideas

### The trace comes from running the program

`w` holds field elements, not machine states, so the steps of the relaxed trace `T` cannot be read off it.
`T` starts from the state the instance and the private inputs give.
Each step's state after follows the chosen execution semantics: the existing `execInstr` for fixed-tape runs, and `execWithTapeAnswer` for runs with independent tape answers.
Once the private inputs are chosen, nothing else is free: Jolt's tracer computes the runtime advice, such as a division's quotient, from the state.

### Choosing the private inputs

Keep the `untrusted_advice` from the `privateInputs` supplied to `AllConstraints`; the context already binds initial RAM to those inputs.
The witness gives one answer at each tape read, and no constraint ties the answers to a tape.
The proof runs on these answers under the relaxed semantics (Layer 5a), then rebuilds one tape from them (Layer 7):
- The tape is the answers' low bytes, laid end to end in read order: 1 byte for `AdviceLB`, 2 for `AdviceLH`, 4 for `AdviceLW`, 8 for `AdviceLD`. It holds exactly the bytes read, so no read runs out.
- A narrow answer may have high bits no tape can give, such as 300 for a 1-byte read. The expansion keeps only the low bytes. `AdviceLB rd` is `VirtualAdviceLoad rd 1`, then `VirtualMULI rd rd 2^56`, then `VirtualSRAI rd rd 56` ([ExpansionsAutomated.lean:1180-1190](../JoltBytecode/JoltISA/ExpansionsAutomated.lean)); `AdviceLH` and `AdviceLW` use 48 and 32. With the answer 300 = 0x12C, or with the tape byte 0x2C, `rd` holds 0x2C · 2^56 after the second row and 44 after the third.
- So the rebuilt run differs from the relaxed one only in the tape, and in the destination register (v40 when `rd` is x0) between the first and second rows of a narrow read. Every source instruction ends with the same registers and memory, so the outputs and panic flag are the same.

PR #2049 removed `bytes_remaining()`, the only instruction that could see the tape's length. Before it, the answers could disagree with every tape (Layer 5a, historical candidate).

The relaxed run uses the honest tracer's runtime advice.
In a division expansion, the witness's advice may differ; the `*Program_sound` theorems still give the honest machine state after the expansion.
`RepresentsRows` does not compare instruction temporaries, so `rem a0, a1, zero` can use witness advice 5 and honest advice 0 while preserving the required observations.
At the previous model revision `43cc043`, SC.W could report failure where
Jolt's tracer reported success. The current model uses PR #2039's deterministic
comparison. `NoStoreConditional` remains pending the SC device-memory cases
and global expansion composition; both must be proved before removing it.

### The witness proves facts about the execution prefix

The main lemma extends an execution prefix while preserving `Agrees w t prefix state`, defined below.
It connects the prefix and its current state to these witness columns:

- **Bytecode selection:** `PC` and `BytecodeRaChunk`. A slot is an index into the bytecode as `w` sees it: slot `i + 1` holds `bytecode[i]`, and slot 0 and the trailing unused slots are no-ops.
- **Registers:** `RegistersVal r t`, the value `w` says register `r` holds before cycle `t`; the read selectors `Rs1Ra`, `Rs2Ra` and write selector `RdWa`; and the values `Rs1Value`, `Rs2Value`, `RdWriteValue`.
- **RAM:** `RamVal a t`, the value `w` says the memory word at RAM index `a` holds before cycle `t`; `RamAddress`, the selector `RamRa`, and the values `RamReadValue`, `RamWriteValue`. `RamValFinal a` is the claimed value at RAM index `a` after all cycles.

`OrdinaryRamAgreement` compares every ordinary-RAM table entry with the
interpreter's byte-map word. Device-region entries need a separate relation,
as described below.
The register table is compared over [live registers](#register-agreement-must-be-over-live-registers); this supersedes leaving out a HostIO row's rewrite temporary until its next write.
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
Layer 6 must prove that every retained cycle selects a real bytecode row; this is part of `soundness_execution_prefix_agreement`.
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
table history, permitted reads and final public I/O. That invariant remains
open; see the device-memory obligations in Layer 5b below.
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
policy and may be needed in Layers 5b or 6; it is not yet established that the
final proof needs it. Layer 2 uses the narrower row-validity and canonicality
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
Layers 0–4, 5a and 8 are proved.
Layer 7 is proved except its two acceptance helpers, C (`soundness_prover_accepts`) and D (`soundness_spoil_asserts_pass`).
Layers 5b–6 remain, as `soundness_execution_prefix_agreement`.

Layers 0 to 4 prove field bounds, selection, table histories and lookup facts.
Layer 5a adds the untrusted-answer semantics alongside the fixed-tape semantics and proves inclusion; the execution-prefix induction in Layers 5b and 6 then takes tape answers from the witness.
Runtime-advice agreement is established when extending the prefix and retained in `Agrees`.
Layer 7 collects the execution and advice facts, proves the stopping obligations, assembles the relaxed trace and rebuilds one tape from its answers, giving an `HonestTrace`; Layer 8 proves `matches_outputs`.

### Layer 0: field elements to numbers

What: distinct natural numbers below the field's characteristic stay distinct in the field, and each comparison needs a bound showing both sides are below it.
Also derive `2^chunkBits < ringChar F` from the verifier's setup check and `charAbove2pow127`.
Why: constraints are equations over the field `F`, but registers and memory hold 64-bit words.
To conclude `a = b` from `(a : F) = (b : F)`, both must be below the characteristic.
The existing Layer 0–1 lemmas use only `charAbove2pow127 : 2^127 < ringChar F`, which covers 64-bit words but not every 128-bit integer. Their bounds stay unchanged; the base soundness theorem supplies `charAbove2pow128 : 2^128 < ringChar F`, the stronger bound needed in Layer 4. `two_pow_127_lt_char` in `Layer0/Field.lean` provides the bridge; Layer 2's zero-lookup and x0 proofs already use it.
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
   `encoded`. `ld_address_encoded` and `sd_address_encoded` discharge the flag
   and immediate facts from the selected row; source agreement remains an
   execution-induction obligation.

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
  to the soundness statement. This first part is proved below.
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
only in the field. For Akita's prime `p = 2^128 - 2^32 + 22537`, both `s` and
`s + p` fit in 128 bits when `s < 4294944759`; they have the same field encoding
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

Our [constraint checklist](../JoltConstraints/constraints.md) explicitly leaves
this Akita condition outside the current base model. On 2026-10-10, Ari approved
restricting this theorem to `2^128 < ringChar F` and modeling Akita separately.
Layer 4 must use that stronger bound to recover full lookup addresses. The
separate Akita relation must include the guard and its actual field: merely
adding the upper-half guard would still not cover every characteristic above
`2^127`. That modeling work is pending and does not include PCS security.

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
future fix to B6's stopping specification. Fixed-tape inclusion alone does not
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

`CodeUnchanged` needs no relaxed counterpart for this proof. Both trace
specifications execute the expanded bytecode rather than fetching instructions
from memory, and no proved soundness lemma uses `CodeUnchanged`. The premise
justifies relating the model to Jolt's tracer; it does not block the relaxed
bytecode-execution proof. Its existing definition and place in the main theorem
are retained. Whether it belongs in that theorem is a separate scope question.
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
dispatcher that composes them is not yet written.

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
cycle. Most other instruction families now have local steps too (see the
status list below); PC agreement and the composition remain open.

**Device-memory obligations.** These are three cases of a broader obligation:
derive both successful memory access and the device's value from the RAM
constraints. Consistent RAM history alone does not establish either one.
The source audit below records the historical findings at Jolt revision
`43cc043332762034b5f65379441576e06e7a3890`. The current device/MMU source
was rechecked at `8bbb2357` in [migration chunk 6](./model_update.md#chunk-6-source-recheck-and-historical-citations);
the existing discussion is unchanged.
The address-check and termination restrictions discussed there have since been added, and the panic restrictions `PanicStoresOne` and `ClaimsNoPanic` were added on 2026-10-20.

**Termination-device restriction added; execution proof still open.** Banning
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
panic paths and other exit paths must also be checked. The RAM invariant would
need to distinguish the termination table entry from readable device memory.
The restriction and its application lemmas build through `JoltConstraints`
(8782 jobs). `termination_next_jal_stalls` proves a zero-offset JAL actually
leaves `nextPC` at its own address. `#print axioms` for that lemma and
`termination_next_ld_disjoint` lists only `propext`, `Classical.choice`,
`Quot.sound`, and the existing `sys_enable_experimental_extensions`.
The execution-prefix induction remains open; the last-real-row argument is proved in `Layer7/LastJump.lean` and `Layer7/TerminationStore.lean`.

Any proposed restriction must be a property of the program under every allowed
private input and every reachable prefix of relaxed execution, including
arbitrary tape answers. It must describe the program's accesses, not witness
flags. A restriction intended to ensure access succeeds must cover the
attempted next access as well: quantifying only over successfully completed
runs would miss a store that aborts. The load/store address restriction below
and termination restrictions are now added. Their sufficiency for the full
soundness proof remains to be established.
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

**Panic: known B6 case, also an obstacle in Layer 5b.** In
`common/src/jolt_device.rs:121–155`, a write to the first panic byte sets the
flag regardless of the value, and writes to the other panic bytes are ignored.
Every byte load in the panic region returns the flag. The RAM table instead
retains the stored bytes. Even storing the word 1 leaves different later word
reads: the device returns `0x0101010101010101`, while the table holds 1.
Separately, storing zero still sets the device flag; final public I/O represents
that flag as the word 1. Thus forbidding later panic reads alone would not
settle final panic agreement. The Lean `JoltDevice.load?` and `store?` match
these rules. Handle both the read invariant and the final flag explicitly;
do not treat the termination FIXME as covering this case. B6's soundness
consequence remains a code-reading finding, without a complete satisfying
witness or verifier reproduction.

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
at `8bbb2357` in [migration chunk 6](./model_update.md#chunk-6-source-recheck-and-historical-citations).
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
`ld_address_checks` and `sd_address_checks` extract these facts before their
respective execution proofs. They do not take successful execution as a hypothesis.

The SDK's
generated return stores byte 1 to termination (`jolt-sdk/macros/src/lib.rs:882`),
and its panic handler stores byte 1 to panic (`:903`); their expanded stores
remain allowed by the address checker. This checks compatibility with those
generated paths, not a proof of the premise for every SDK guest. Guest code
using advice as an address must meet the checks for every allowed answer.

**Limits of the premise.** `effective_address_ok` is the tracer's address-assertion
check, not its whole memory interpreter. Alignment and register access remain
proof obligations. Below RAM, `load_raw?` and `store_raw?` also reject hard-coded
unsupported peripheral ranges; establish that these cannot be selected under
the relevant layout and constraints, or expose that as a further obligation.
Do not infer successful execution from this premise alone. It also does not
resolve the panic/termination value mismatch or stopping. Narrow or remove the
premise as each case above is resolved and proved; both its definition and the
main theorem carry that FIXME. No execution semantics or constraints were changed.

For a runtime-advice step, justify the local lemma's advice hypotheses using the relevant expansion constraints; a tape-reading step takes its answer from the witness.
For `AdviceLB`, `AdviceLH` and `AdviceLW`,
[AdviceExpansion.lean](../JoltConstraints/Soundness/Layer5/AdviceExpansion.lean)
now proves the source expansion shapes and full execution of their
`VirtualAdviceLoad`, `VirtualMULI` and `VirtualSRAI` rows in order. Both the
ordinary-destination and x0 temporary-register branches are covered. The
proofs derive the shift constants from the generated programs, establish
register-value linkage, and apply `narrowAdvice_value` at widths 8, 16 and 32.
`execProgramWithTapeAnswers` composes the existing per-row execution rule,
using local expansion row indices. The induction still has to establish that
the witness selects these rows in order, relate its answer to the first row,
and maintain register/RAM table agreement through their intermediate states.
For an LD or SD step, use `ld_address_encoded` or `sd_address_encoded`
with the approved `RamRegionFits` premise and the source-column agreement
from the induction. These address lemmas already derive the signed integer
equality, nonwrapping bound and machine-address encoding. For ordinary RAM,
`ld_ram_step` and `sd_ram_step_agreement` then prove the access succeeds and
matches the RAM table; device accesses remain open.
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

**Closing Layer 5b (agreed with Ari, 2026-10-19).** Layer 5b can close with
approved restrictions for suspected Jolt bugs. Remove the SC restriction before
calling this layer closed.

Blocked parts and their status:
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
  Write-up: `blog/content/blog/completeness-and-soundness/index.md`.
- Stopping early on a "panicked" claim, where the witness's last cycle before the padding can be any JAL or JALR: `ClaimsNoPanic` (added 2026-10-20), which limits the theorem to "no panic" claims.
  Write-up: `blog/content/blog/proof-stops-at-any-jump/index.md`.
- Both are Jolt bugs that must be fixed in Jolt; neither may remain a restriction.

Remaining proof work, which no restriction may replace:
- Remove `NoStoreConditional` after composing SC.W and SC.D expansions. PR
  #2039 fixed the upstream bug; their local LD and SD steps currently cover
  ordinary RAM only, so device cases remain part of this work.
- The 9 row kinds without a step: JALR and the
  six branches, whose state part is a destination write or nothing;
  `VirtualAdviceLoad`, connecting tape reads to the witness's answers; and
  `VirtualAdvice`.
- Device memory for the input, advice, output and termination regions.
- Apply the proved per-expansion write-before-read fact
  (`ExpansionFacts.expand_temps_ok`) in the global register-agreement induction.
  Under [live-register agreement](#register-agreement-must-be-over-live-registers), a HostIO `x0` rewrite's unconstrained temporary is not live until its next write.
  The pinned allocator uses 40–47, not reservation
  registers 32 and 33 (`crates/jolt-program/src/expand/materialize.rs:79-90`,
  `expand/allocator.rs:115-139`).
- The dispatcher, shared with Layer 6.

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
The plan for finishing Layers 5b–6 is in [Running the Layer 6 agents](#running-the-layer-6-agents-for-ari).

**Entry and interior-slot bridge, ready for review, 2026-10-15.**
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

The module is imported by `JoltConstraints.lean`; `lake build JoltBytecode
JoltConstraints` passed (8782 jobs). `#print axioms` for all five public lemmas
lists only `propext`, `Classical.choice` and `Quot.sound`. No main-theorem
premise, `sorry`, native decision proof or heartbeat setting was added.
This is a bytecode/PC bridge, not yet the `Agrees` induction: entry selection
has not established that a nonzero entry starts a source instruction, and the
execution-prefix invariant must still identify the register shift's pre-state
with its producer's post-state.
Padding persistence is now proved (`padding_persists`, `padding_from`); the source-boundary transition remains to be proved before the dispatcher can use these lemmas.

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
The temporary `TerminationThenStall` and `ClaimsNoPanic` restrictions still address the separate B6 early-end case described in [the earlier review](./review_completeness_and_soundness.md#b6-the-soundness-statement).
Take the instance facts, including `initialized`, from the context; Layer 5a left `JoltPrivateInputs` unchanged. `accepted` follows from `expands` and `entryIsRust`.
Then rebuild one tape from the answers' low bytes, in read order, and run the program on it. Prove that this run is an `HonestTrace` with the same bytecode rows, ending every source instruction with the same registers and memory ([Choosing the private inputs](#choosing-the-private-inputs)).
Why: once all these obligations are resolved, the constructed prefix can be packaged as a relaxed trace, and the rebuilt tape turns it into an `HonestTrace`, the form the theorem concludes.
Uses: the context, Layers 5 and 6, stopping proofs.

The tape-rebuild closing plan's steps 1–6 are complete as of 2026-10-21, and `feat/layer7-tape-rebuild` is merged into `feat/soundness`.
`rebuild_rows` constructs all six fields directly, using a shared masking proof for every narrow width.
`narrow_load_shape` is proved from the advice-pair checker added in `de5aff70de66d290ceaeb6e7357ba352b855c5d0` and the generic adjacent-row lift.
The same lift now proves register-shift pairs.
`TapeRebuild.lean` has no `sorry`, and the reverse-language inclusion has no `sorryAx` dependency.
See the [step 6 validation and declaration timings](#tape-rebuild-step-6-2026-10-21).

### Layer 8: outputs

What: use `Represents.finalRam`, which the Layer 7 stopping proof obtains by carrying the cut RAM comparison to `RamValFinal` across stall replays and padding.
Helper B (`soundness_matches_outputs`) proves this layer without `sorryAx`.
Translate the agreed RAM encoding on the public I/O region into the final device's output bytes and panic flag.
Then use `RamOutputEqPublicIo` to prove that the final device has the instance's output bytes, after trimming trailing zeros, and its panic flag.
For an empty trace, use the initial device.
In the panic-store discrepancy in B6, a store of 0 to the panic word sets Jolt's tracer's flag but leaves 0 in the RAM table, so a false "no panic" claim passes (`blog/content/blog/completeness-and-soundness/index.md`).
It no longer blocks this step: B needs no panic restriction, and the burden now sits in the execution prefix's `cutRam` at the panic word, where the temporary `PanicStoresOne` restriction excludes it.
Why: this gives `matches_outputs` for the relaxed trace. The rebuilt run has the same final device, so it carries over to Layer 7's `HonestTrace`, which proves the theorem's existential conclusion.
Uses: endpoint agreement from Layers 5b–6, Layer 3's suffix lemma, `RamOutputEqPublicIo`, device semantics.

### Order of the remaining work

Superseded on 2026-10-20: work now goes top-down; see
[Change of course](#change-of-course-top-down-2026-10-20).

Agreed with Ari, 2026-10-16. Close Layer 5b as described in
[Closing Layer 5b](#layer-5b-one-execution-step), refined on 2026-10-19. Then state Layer 6's lemmas
with `sorry`, each in the form Layer 7 needs and with a short proof sketch.
Prove Layer 7 against those statements, then close Layer 6. Genuine unknowns
stay explicit open questions rather than `sorry`'d facts; in particular, whether
`AllConstraints` admits an instance with entry address 0. Track every new
`sorry` in `model_review.md`'s "Proofs owed".

### Obligations that need particular care

- **Chunk selection alone does not establish address selection.** With 5-bit addresses and
  two 4-bit chunks, one-hot digits `(2, 0)` encode 32, outside the domain `0…31`.
  The full selector is then zero throughout that domain. Layer 1(b) now rules
  this out for bytecode. For RAM, it proves that an all-zero selector forces
  `RamAddress`, read and write values, and all per-word increments to zero.
  Layer 5b still has to justify execution of zero-address instructions; the
  RAM-table facts alone are not a soundness proof for those instructions.
  This example alone is not a satisfying witness for `AllConstraints`.
- **Field-valued histories are not yet machine states.** Layers 2–3 prove update
  equations. Layer 5b must establish and preserve their interpretation as machine
  words. Check arithmetic bounds per expression, especially wide multiplication.
- **Lookup reuse must not assume execution.** `lookupEntryCorrect_*` takes an
  `HonestTraceRow`, which already includes a proof of execution. Reuse pure identities such
  as `and_entry`; separately prove the connection to arbitrary witness operands.
- **Local execution does not establish honest advice or termination.** Running a
  `VirtualAdvice` row with a supplied value does not show that the honest tracer
  supplies that value.
  The shape of padding and the stopping rule, needed before interpreting the witness as a complete relaxed trace, are now proved in Layer 7.

### Current status and known obstacles

- **Proved, first review chunk:** [Layer0/Field.lean](../JoltConstraints/Soundness/Layer0/Field.lean)
  proves bounded cast injectivity and Boolean decoding. It now also provides
  `two_pow_127_lt_char`, the shared bridge from `charAbove2pow128` to
  `charAbove2pow127`, used by Layer 2's zero-lookup and x0 proofs.
  [Layer1/OneHot.lean](../JoltConstraints/Soundness/Layer1/OneHot.lean) proves unique
  selection when the sum is one, all-zero selection when the sum is zero, and
  the selected-value read rule. These are generic algebraic lemmas; `Chunks.lean`
  now applies the selection lemmas to Jolt's chunk constraints (Layer 1(a)).
  `read_eq_selected` and its helper `selector_eq_ite` are now used by the
  selected-address read lemmas in `Bytecode.lean` and `Ram.lean`.
- **Proved, Layer 0 verifier bounds:** [Layer0/Bounds.lean](../JoltConstraints/Soundness/Layer0/Bounds.lean)
  bounds advice-polynomial variables by 64 and the modeled Dory setup by 72.
  From `ConstraintContext.oneHotFitsSetup`, it derives `chunkBits ≤ 72`, then
  `Fintype.card (Fin (2^chunkBits)) < ringChar F` using the existing `charAbove2pow127`
  assumption, directly matching the generic one-hot lemmas' cardinality premise.
  No honest-prover chunk configuration is assumed. The four lemmas compile at
  the default heartbeat limit; their only axioms are `propext`, `Classical.choice`
  and `Quot.sound`. The setup definition was rechecked against Jolt revision
  `8bbb2357890928d8f83b00ca542879077c4d3d28`; precommitted program tables remain
  outside this model, as documented in `verifier_sizes.lean`. Revisit 72 if those
  `extra_candidates` are modeled.
- **Proved, Layer 0 word encodings:** [Layer0/Words.lean](../JoltConstraints/Soundness/Layer0/Words.lean)
  derives `2^64 < ringChar F` and bounds every 64-bit word's natural value by the
  characteristic. It then proves that equal field encodings imply equal words,
  using bounded cast injectivity.
  All three lemmas compile at the default heartbeat limit and depend only on
  `propext`, `Classical.choice` and `Quot.sound`. No new premise is added to the
  soundness theorem or instance. This covers word encodings; bounds on wider
  arithmetic expressions still need proofs where those expressions are used.
  `Bytecode.lean` now uses the word-encoding bridge to exclude address four.
- **Proved, Layer 1(a) chunk selection:** [Layer1/Chunks.lean](../JoltConstraints/Soundness/Layer1/Chunks.lean)
  proves unique selection in every bytecode and instruction-lookup chunk at every
  cycle. The RAM weight is zero or one; at a cycle, either all RAM chunk entries
  are zero or every RAM chunk selects exactly one entry, according to that weight.
  The helpers use the context and equations obtained from `AllConstraints`,
  together with the existing `charAbove2pow127` assumption where needed. The five
  lemmas compile at the default heartbeat limit and depend only on `propext`,
  `Classical.choice` and `Quot.sound`. No new premise is added to the soundness
  theorem or instance. The combined selectors are handled by the proofs below.
- **Proved, full-selector alternatives:** [Layer1/Products.lean](../JoltConstraints/Soundness/Layer1/Products.lean)
  proves the Boolean-product facts, and [Layer1/Addresses.lean](../JoltConstraints/Soundness/Layer1/Addresses.lean)
  uses address-digit injectivity to show that the full bytecode and RAM selectors
  are each either all zero or select exactly one in-domain address. This holds
  for arbitrary satisfying witnesses, including the zero-bit RAM domain with no
  chunks; its empty product is one. No positive-chunk or in-range-selection
  premise is added. The ten public lemmas compile at the default heartbeat limit
  and depend only on `propext`, `Classical.choice` and `Quot.sound`.
- **Proved, Layer 1(b) selector classification:** [Layer1/Bytecode.lean](../JoltConstraints/Soundness/Layer1/Bytecode.lean)
  rules out all-zero bytecode selection: it would force the next unexpanded PC
  to four, contradicting either the next cycle's preprocessed address or the
  final-cycle zero shift. Every cycle therefore selects exactly one bytecode slot.
  The final-cycle boundary was rechecked against Jolt revision
  `8bbb2357890928d8f83b00ca542879077c4d3d28`: the `NextUnexpandedPC` claim in
  `crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs` is weighted
  by `EqPlusOneOuter`, which the verifier evaluates in
  `crates/jolt-verifier/src/stages/stage3/spartan_shift.rs` using
  `crates/jolt-poly/src/eq_plus_one.rs`. At the maximum input cycle every term
  has a zero bit-flip factor, so the entire successor kernel is zero; it does
  not wrap to cycle zero. `NextUnexpandedPc::extract` in
  `crates/jolt-witness/src/witnesses/pc.rs` also returns zero when no next row exists.
  [Layer1/Instruction.lean](../JoltConstraints/Soundness/Layer1/Instruction.lean)
  uses the checked divisibility of chunk widths to prove a bijection between
  lookup-chunk addresses and small-digit tuples, then proves each lookup selector
  selects exactly one address without bounding its entire domain by the characteristic.
  [Layer1/Ram.lean](../JoltConstraints/Soundness/Layer1/Ram.lean) proves full RAM
  selection is zero exactly when `RamAddress` is zero, and otherwise unique.
  It proves the zero read, write and per-word-increment consequences. Its loose
  remapped-address field bound uses `WitnessParams.logRamK_lt_usizeBits`, the
  modeled 64-bit host's domain-size bound, rather than an extra context premise.
  All eleven current public lemmas compile at the default heartbeat limit and depend
  only on `propext`, `Classical.choice` and `Quot.sound`. No premise was added to
  the soundness theorem or instance. This completes Layer 1(b)'s selector
  classification; instruction execution remains in Layer 5b. Generic selected
  bytecode and RAM read lemmas are also proved, since the classification uses
  them. Their column-specific consequences and the lookup read rule are proved
  in Layer 1(c) below.
  `ram_address_value_lt_char`, originally private, is now public because Layer 3
  reuses its bound to recover a natural-number address from the field equation.
- **Proved and reviewed, Layer 1(c):** [Layer1/BytecodeReads.lean](../JoltConstraints/Soundness/Layer1/BytecodeReads.lean)
  derives the ten bytecode-backed column reads: PC, unexpanded PC, immediate,
  circuit flags, instruction flags, both source-register selectors, the
  destination-register selector, lookup-table flags, and the lookup operand-format flag.
  [Layer1/RamReads.lean](../JoltConstraints/Soundness/Layer1/RamReads.lean)
  derives the raw address, read value and write value at a selected RAM index.
  Layer 3 uses `ram_zero_effects` for zero addresses; the unused generic
  `ram_read_of_address_zero` wrapper was removed, leaving three lemmas here.
  [Layer1/InstructionReads.lean](../JoltConstraints/Soundness/Layer1/InstructionReads.lean)
  reconstructs one full 128-bit lookup address from the `InstructionRa` choices,
  proves its read rule, and collapses the lookup-output and both operand sums.
  This uses exact chunk-width divisibility, without assuming `2^128 < ringChar F`.
  The selected-address hypotheses of the read lemmas are supplied by the proved
  selection lemmas; they are not new soundness premises.
  All twenty-one current public lemmas compile at the default heartbeat limit and depend
  only on `propext`, `Classical.choice` and `Quot.sound`. Layer 1's selector and
  read obligations are complete. Register and RAM histories are handled in Layers 2–3;
  identifying the active lookup table and interpreting its operation and operands
  remain in Layer 4. Ari reviewed these lemmas on 2026-10-10. Recheck the ten
  bytecode wrappers' callers as later layers land and remove any left unused.
- **Proved and reviewed, Layer 2(a):** [Layer2/Registers.lean](../JoltConstraints/Soundness/Layer2/Registers.lean)
  proves zero initialization and the single-cycle register increment from
  `RegistersValEqPrefixRdInc`. Using Layer 1 bytecode selection, it proves both
  source reads and the destination write value, then shows that the next table
  changes only the selected destination, to `RdWriteValue`. An absent operand
  reads zero; a cycle with no destination preserves every entry. This includes
  padding slots and keeps explicit x0 distinct from an absent operand.
  Updates require the next cycle to be inside the table; there is no register
  column at `traceLength`. All six public lemmas compile at the default heartbeat
  limit and depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  The public `sum_before_succ` helper now lives in
  [Helpers/PrefixSum.lean](../JoltConstraints/Soundness/Helpers/PrefixSum.lean),
  so Layer 3 can share it; it needs only an additive commutative monoid and has
  the same allowed axiom dependencies. Ari reviewed the six table lemmas on
  2026-10-10. Keep their match-form statements for now; add `some`/`none`
  corollaries when concrete callers need them.
  No soundness premise was added. `Rs1Ra`, `Rs2Ra`, and `RdWa` column wrappers
  from Layer 1(c) now have callers here.
  The equations were rechecked against Jolt revision
  `8bbb2357890928d8f83b00ca542879077c4d3d28`, in
  `crates/jolt-claims/src/protocols/jolt/relations/registers/{val_evaluation,read_write_checking}.rs`
  and the verifier's `stages/stage5/registers_val_evaluation.rs` and
  `stages/derivations.rs`: the history uses the strict comparison of the write
  cycle with the read cycle, with no initial-register term.
- **Proved and reviewed, Layer 2(b):**
  [Layer2/RegisterMap.lean](../JoltConstraints/Soundness/Layer2/RegisterMap.lean)
  proves encoding/decoding identities and injectivity for canonical source and
  destination operands. `bytecodeRow_rowOk` derives a real row's validity and
  operand canonicality from `context.expands`, using
  `ExpansionRows.expand_program_rowOk`. Its destination facts exclude a virtual
  register alias at index zero when proving that an x0 destination is the
  canonical no-op.
  [Layer2/State.lean](../JoltConstraints/Soundness/Layer2/State.lean) connects every
  initial register-table entry to the actual initial-state word, using
  `initial_state_sourceValue`, and proves that `advance_pc` preserves every
  source value. `context.initialized` supplies the initialization equation;
  no honest trace is assumed.
  [Layer2/ZeroLookup.lean](../JoltConstraints/Soundness/Layer2/ZeroLookup.lean)
  proves that identity RAF with a zero right operand and the RangeCheck table
  gives zero output. The existing `charAbove2pow128` bound makes the full-address
  cast injective. The flag and operand hypotheses are discharged for the
  canonical no-op in
  [Layer2/ZeroRegister.lean](../JoltConstraints/Soundness/Layer2/ZeroRegister.lean).
  Its induction proves `registersVal_x0` at every cycle and
  `x0_write_effect_zero` even at the final cycle, where no next register-table
  column exists. Padding and every other destination leave x0 unchanged.
  These fourteen new public lemmas, the six Layer 2(a) lemmas, and the shared
  prefix-sum helper compile at the default heartbeat limit. Each was audited
  with `#print axioms`: dependencies are subsets of `propext`, `Classical.choice`,
  and `Quot.sound`, with no `sorryAx`, compiler-trust axiom, or project axiom.
  The broader `expand_program_rows_valid` bundle still depends on
  `sys_enable_experimental_extensions`; none of these proofs uses that bundle.
  No premise was added to the soundness theorem or instance. This completes the
  planned Layer 2 obligations; agreement after instruction
  execution remains in Layer 5b.
  `sourceRegisterAddress_injective`, `registersVal_initial_advance_pc` and
  `x0_write_effect_zero` currently have no callers; `source_encode_decode` is
  now used by `Layer5/Registers.lean`. Keep them for the planned state and linkage proofs in Layers 5b and 6;
  recheck their callers when those layers land and remove any left unused.

  The three case-split proofs requested for timing were profiled separately
  from the build on 2026-10-10, using Lean 4.29.0-rc4 on this checkout. One run
  per module with `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=5`
  followed by the module's file path reported:

  | Declaration | Proof elaboration | Main theorem kernel check |
  | --- | ---: | ---: |
  | `slot_setWidth` (`Layer2/RegisterMap.lean`) | 0.361 s | 0.017 s |
  | `sourceValue_advance_pc` (`Layer2/State.lean`) | 0.883 s | 0.051 s |
  | `instruction_destination_canonical` (`Layer2/RegisterMap.lean`) | 0.754 s | 0.020 s |

  These are declaration timings with profiling enabled, excluding process
  startup and import loading, not whole-module build times. The profiler also
  reported a 0.031 s kernel check for the generated auxiliary proof of
  `sourceValue_advance_pc`. The default heartbeat limit was unchanged. Keep
  these case splits: the measured times do not warrant rewriting them solely
  for performance. Reprofile if the proofs or instruction set grow.
- **Proved, awaiting review, Layer 3:**
  [Layer3/History.lean](../JoltConstraints/Soundness/Layer3/History.lean) proves
  the initial table, the one-cycle increment, the last-cycle update into
  `RamValFinal`, and equality with the final column when all remaining per-word
  increments vanish. It reuses `sum_before_succ` and takes only the history
  constraints it needs. The last-cycle theorem also covers `traceLength = 1`.
  [Layer3/Updates.lean](../JoltConstraints/Soundness/Layer3/Updates.lean) uses
  selection to replace only the accessed word with `RamWriteValue`, both between
  table cycles and into the final column. A zero address leaves every word
  unchanged; `RamInc` itself need not be zero in this case.
  [Layer3/Access.lean](../JoltConstraints/Soundness/Layer3/Access.lean) derives zero
  address for non-memory cycles and for `IsNoop = 1` padding, and proves that a
  load has zero write effect on every word. This does not assume that padding
  forms a suffix or that a zero-address load executes successfully.
  [Layer3/Address.lean](../JoltConstraints/Soundness/Layer3/Address.lean) recovers
  `raw.toNat = ramLowestAddress + 8 * chosen` from selection and the field
  encoding of a 64-bit raw address, then proves that raw address remaps to
  `chosen`. The execution proof must establish the raw-address encoding from
  its operands; it is a local helper hypothesis, not a new soundness premise.
  [Layer3/State.lean](../JoltConstraints/Soundness/Layer3/State.lean) ties the
  initial table to `context.initialized`, proves agreement of the public and
  initial-state memory layouts, and proves that preparing PC preserves any
  observation of the memory map and Jolt device. In particular, initial RAM
  agreement survives preparing the first instruction's PC.
  All eighteen public Layer 3 lemmas build at the default heartbeat limit and
  have only subsets of the three standard axioms. No soundness or instance
  premise was added.
  The Layer 7 stopping proof discharges the suffix-zero hypothesis.
  Read agreement after execution, including device regions, remains in Layer 5b; output and panic agreement are proved in Layer 8.
  The history equations were rechecked against Jolt revision
  `8bbb2357890928d8f83b00ca542879077c4d3d28`:
  `crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs` batches the
  current and final histories; the verifier's `stages/stage4/ram_val_check.rs`
  uses `LtPolynomial::evaluate(write_cycle, read_cycle) + gamma`. The strict
  comparison in `crates/jolt-poly/src/lt.rs` gives earlier writes for `RamVal`,
  while the final term includes every cycle. The remapping matches
  `MemoryLayout::remap_word_address` in `common/src/jolt_device.rs`; the
  non-memory and load guards match `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`.
  This is a source check of the modeled equations, not a PCS proof.
- **Layer 3 review, address wraparound:** resolved by a new premise.
  [layout_check.lean](../bug-report/ram-address-wraparound/layout_check.lean)
  shows that layout construction and the maximum RAM size alone allow a RAM
  domain past `2^64`; it is not a satisfying witness. Its two lemmas use only
  subsets of the three standard axioms.
  Ari approved replacing the run-based address assumption with the
  instance-only `RamRegionFits` premise on 2026-10-10. NOTE: to confirm with
  a16z. `Layer3/Layout.lean` derives the witness domain bound from the verifier's
  maximum-size check and proves that all eight bytes of every word fit.
  `Layer5/MemoryAddress.lean` derives `encoded` as described in Layer 3,
  including the unselected zero case. The old predicate and next-step helper
  are deleted. The module note, `model_review.md` and B6 of
  `review_completeness_and_soundness.md` now describe the layout premise.
  The main theorem depends on `sorry` only through `soundness_execution_prefix_agreement`, `soundness_prover_accepts` and `soundness_spoil_asserts_pass`; compiling it is not a proof of soundness.
  The Noop decoder/expansion audit above resolves the metadata TODO for the
  modeled instruction set.
  The padding suffix and stopping are proved in Layer 7.
  The remaining Layer 3 lemmas keep their planned callers in Layers 5b,
  6 and 8.
- **Proved and reviewed, Layer 4(a):**
  [Layer4/Table.lean](../JoltConstraints/Soundness/Layer4/Table.lean) collapses
  the table selection, including the no-table case, and derives identity RAF
  from an active arithmetic flag using the selected bytecode row.
  [Layer4/Identity.lean](../JoltConstraints/Soundness/Layer4/Identity.lean)
  recovers the full address using `charAbove2pow128` and evaluates the selected
  table there.
  [Layer4/RangeCheck.lean](../JoltConstraints/Soundness/Layer4/RangeCheck.lean)
  and [Layer4/Arithmetic.lean](../JoltConstraints/Soundness/Layer4/Arithmetic.lean)
  prove the wrapped 64-bit addition, subtraction and multiplication results.
  They retain addition's carry, subtraction's `2^64` bias (also when the right
  input is zero), and every multiplication bit until the table truncates them.
  The pure `rangeCheck_entry` identity moved from the completeness helper into
  [Layer4/RangeCheckEntry.lean](../JoltConstraints/Soundness/Layer4/RangeCheckEntry.lean),
  keeping its name and callers. Its new proof uses ordinary bit-vector lemmas
  and a kernel-checked constant mask instead of bit blasting.
  These twelve public lemmas use only subsets of the three standard axioms,
  build at the default heartbeat limit, and introduce no soundness or instance
  premise. Jolt's `add.rs`, `sub.rs`, `mul.rs`, `tables/range_check.rs` and the
  arithmetic rows of `jolt-claims/src/protocols/composed/r1cs/rv64.rs` were rechecked at
  `8bbb2357`; no mismatch was found in this chunk.
  Connecting instruction inputs and destination writes to execution belongs
  to Layer 5b.
  The requested timing check for `instructionRafFlag_one_of_arithmetic` measured
  0.386 s for proof elaboration and 0.0025 s for kernel checking, excluding
  imports, with Lean's trace profiler on the unchanged theorem text. The default
  heartbeat limit was unchanged. This does not justify rewriting the proof
  for performance. Advice rows follow the separate word-recovery route in
  Layer 4 above; they do not need an input-determined identity address.
- **Proved and reviewed, Layer 4(b), operand recovery:**
  [Layer4/Interleave.lean](../JoltConstraints/Soundness/Layer4/Interleave.lean)
  proves the bit-unpacking identities, both round trips, and agreement between
  the field operand polynomials and the decoded words. Five existing pure
  lemmas moved from the completeness helper, retaining their names and callers.
  Their two native `bv_decide` proofs introduced compiler-generated axioms, so
  those proofs were replaced by kernel-checked bit simplification, split into
  four private lemmas covering sixteen bit positions each.
  [Layer4/Interleaved.lean](../JoltConstraints/Soundness/Layer4/Interleaved.lean)
  uses the two RAF equations and word-cast injectivity to recover both operands,
  their unique interleaved address, and the selected table's entry there.
  These files contain eleven public lemmas: six new and five moved. The weaker
  `charAbove2pow127` bound suffices because each operand is a 64-bit word.
  RAF zero and operand agreement remain local obligations for later instruction
  proofs; no soundness or instance premise was added.
  `lake build JoltConstraints` passes, including the existing completeness
  callers. All eleven public lemmas' axiom lists contain only subsets of
  `propext`, `Classical.choice` and `Quot.sound`. The default heartbeat limit
  is unchanged. Replacing `norm_num` with targeted `simp only` reduced the
  four bit-unpacking helpers from the earlier 2.29–2.33 s each. The follow-up
  timing audit below measures their current proofs and both `WordEntry` mask
  computations. The four bounded sixteen-position case splits remain; a proof
  through the mask stages is a possible later refactor. The earlier full build
  reported 6.2 s for `Interleave.lean`, including imports and concurrent jobs.
  Docstrings now describe both interleaving bit lemmas and every bitwise and
  comparison entry lemma.
  Jolt's `interleave.rs` and stage-5 `instruction_read_raf.rs` were rechecked at
  `8bbb2357`; the odd-left/even-right convention agrees with the model.
- **Proved and reviewed, Layer 4(b), table operations:**
  [Layer4/Bitwise.lean](../JoltConstraints/Soundness/Layer4/Bitwise.lean) and
  [Layer4/Comparison.lean](../JoltConstraints/Soundness/Layer4/Comparison.lean)
  interpret AND, OR, XOR, ANDN, equality, inequality, unsigned comparisons and
  signed comparisons. Their eleven witness lemmas use `lookupOutput_of_interleaved`
  and eleven pure identities in the matching `Entry` files. The pure identities
  moved from completeness with their names and callers retained. All 45 public
  lemmas in Layer 4(a–b) were audited: only the three standard axioms occur.
  The modules build at the default heartbeat limit. Ari reviewed these table
  interpretations on 2026-10-10. The eleven table operations were checked against
  Jolt's `materialize_entry` implementations at `8bbb2357`; the source recheck found no change.
- **Proved and reviewed, Layer 4(c):**
  [Layer4/Word.lean](../JoltConstraints/Soundness/Layer4/Word.lean) interprets
  word slices, sign extension, aligned addresses, powers, shift masks, byte
  reversal and window masks.
  [Layer4/WordArithmetic.lean](../JoltConstraints/Soundness/Layer4/WordArithmetic.lean)
  composes these results with the arithmetic constraints for ADDW/SUBW/MULW
  and the high product used by MULHU.
  [Layer4/Conditional.lean](../JoltConstraints/Soundness/Layer4/Conditional.lean)
  covers sign masks, conditional negation, division checks and store lanes.
  [Layer4/Shift.lean](../JoltConstraints/Soundness/Layer4/Shift.lean),
  [Layer4/Rotate.lean](../JoltConstraints/Soundness/Layer4/Rotate.lean) and
  [Layer4/Pext.lean](../JoltConstraints/Soundness/Layer4/Pext.lean) cover the four
  right shifts, twelve XOR-rotate tables, and both unsigned and signed extraction
  for arbitrary masks. Shift interpretations require the appropriate right-shift
  mask as a local hypothesis; Layer 5b must derive that shape from expansion and
  the earlier mask-producing row or immediate. The other operand-agreement
  hypotheses likewise belong to the execution induction.

  [Layer4/Assertions.lean](../JoltConstraints/Soundness/Layer4/Assertions.lean)
  interprets halfword alignment, word alignment and multiplication without
  overflow. [Layer4/Inputs.lean](../JoltConstraints/Soundness/Layer4/Inputs.lean)
  recovers the input-source selection from bytecode and proves that RAF zero
  preserves both instruction inputs.
  [Layer4/Outputs.lean](../JoltConstraints/Soundness/Layer4/Outputs.lean) connects
  lookup outputs to register writes and branch decisions, and proves that an
  active assertion establishes its table predicate.
  [Layer4/Advice.lean](../JoltConstraints/Soundness/Layer4/Advice.lean) recovers
  a 64-bit RangeCheck output without an input-determined address. It supplies
  the advice word, without claiming that internal runtime advice is correct.

  All 55 `LookupTableKind` constructors are accounted for: 53 have operation
  interpretations; [Layer4/Reachable.lean](../JoltConstraints/Soundness/Layer4/Reachable.lean)
  proves the other two (`VirtualROTR`, `VirtualROTRW`) cannot be selected by
  bytecode expanded from the current `SourceInstruction` type. It uses
  `bytecodeRow_rowOk`'s `immShift` fact, not the broader execution-validity bundle.
  This exclusion is specific to the modeled language: Jolt's
  `expand/inline.rs::rotri` and `rotri32` can emit these instructions, but inline
  source opcodes `0x0B` and `0x2B` are already outside `SourceInstruction`.

  The matching `Entry` files hold the pure identities shared with completeness.
  The shift and PEXT helpers moved there with compatibility imports at their
  old paths. The moved word, sign-mask and rotation proofs now avoid native
  evaluation; their constant checks and bit-vector steps are kernel checked.
  All modules are imported by `JoltConstraints.lean`, and `lake build
  JoltConstraints` passes, including the completeness callers. All 162 public
  Layer 4 theorems were checked with `#print axioms`: only subsets of `propext`,
  `Classical.choice` and `Quot.sound` occur. No heartbeat limit, soundness premise
  or instance premise was added.

  The same declaration timing audit found a maximum of 0.146 s in `PextEntry`
  (`pextSigned_eq_jolt_virtual_pext_signed_value`) and 0.175 s in `ShiftEntry`
  (`sign_foldl`); their other declarations were below those times. Both use
  loop invariants and induction. The full build reported 3.6 s and 3.3 s for
  those modules respectively. A follow-up audit on 2026-10-10 measured the
  remaining case-split proofs with one Lean worker, excluding imports. It used
  `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true
  -Dtrace.profiler.threshold=50` on each source file. Explicit `Elab.async`
  tracing also reports declarations below the 50 ms threshold. Times below are
  proof elaboration and the sum of the following kernel `Lean.addDecl` checks;
  they are measurements of this run, not performance bounds.

  | File and lemma | Proof elaboration | Kernel checks |
  |---|---:|---:|
  | `Interleave.lean: uninterleave_snd_bits_0_15` (private) | 1.165 s | 0.039 s |
  | `Interleave.lean: uninterleave_snd_bits_16_31` (private) | 1.164 s | 0.037 s |
  | `Interleave.lean: uninterleave_snd_bits_32_47` (private) | 1.158 s | 0.040 s |
  | `Interleave.lean: uninterleave_snd_bits_48_63` (private) | 1.161 s | 0.040 s |
  | `WordEntry.lean: shiftRightBitmask_value` | 0.053 s | 0.009 s |
  | `WordEntry.lean: shiftRightBitmaskW_value` | 0.026 s | 0.004 s |

  These timings support retaining the bounded case splits for now, with the
  default heartbeat limit. `Interleave` uses `simp only`; the two `WordEntry`
  lemmas use kernel-checked `decide` after the case split. Every public helper
  in `ShiftEntry` and `PextEntry` now has a docstring. Their names and visibility
  are preserved for existing callers. Ari reviewed all of Layer 4 by reading on
  2026-10-10; compilation and axiom checks were run separately as recorded above.

  The remaining table families' `materialize_entry`
  functions, including the PEXT and byte-reversal helpers, were checked against
  Jolt at `8bbb2357`; the source recheck found no change in those definitions.
- **Resolved scope, Layer 4:** the Akita address alias is excluded by a
  feature-gated constraint already present in Jolt at `43cc043`, but that
  constraint is explicitly outside our base model. With Ari's approval on
  2026-10-10, the main theorem now requires `2^128 < ringChar F`; the proved
  Layer 0–1 lemmas retain their weaker bounds. Akita will be modeled separately
  as a non-succinct constraint relation, with PCS security outside scope.
  The detailed source audit is in Layer 4 above.
- **SC advice at the previous revision `43cc043` (runtime-advice agreement):** SC.W can report failure when the reservation holds;
  the honest tracer reports success. The reproducer was reported as
  [a16z/jolt#2037](https://github.com/a16z/jolt/issues/2037). SC.D has the same
  one-way check; only SC.W was run. With Ari's approval on 2026-10-10, the main
  theorem now temporarily assumes `NoStoreConditional`, excluding both instructions
  from the source program. The `FIXME` requires removing this premise after the
  constraints and model are fixed. The current model is
  regenerated from PR #2039; its SC constraint-to-execution proof remains open.
- **Stopping and panic (Layers 7–8):** the two cases under "Known not sound for
  this L" in [B6](./review_completeness_and_soundness.md#b6-the-soundness-statement)
  are findings from reading the code; they still need reproductions.
- **Layer 5a implemented and reviewed by reading:**
  [TapeSemantics.lean](../JoltConstraints/Soundness/Layer5/TapeSemantics.lean)
  defines independent 64-bit tape answers and proves that a successful
  fixed-tape step has exactly the same post-state under the relaxed rule.
  [TapeTrace.lean](../JoltConstraints/Soundness/Layer5/TapeTrace.lean) defines
  relaxed runs, completed traces and their language. Its embeddings retain
  the entire original trace, including runtime advice, outputs and stopping
  requirements, and prove `inLanguage_implies_untrustedAnswerLanguage`.
  [NarrowAdvice.lean](../JoltConstraints/Soundness/Layer5/NarrowAdvice.lean)
  proves the multiply/shift post-processing returns the signed low-width word
  for every width in `1..64`. The generated `AdviceLB`, `AdviceLH` and `AdviceLW`
  expansions use those operations at widths 8, 16 and 32 in both destination
  branches, including the x0 temporary-register branch. The generic value
  identity is proved here; the expansion shapes and their full execution are
  now proved in the Layer 5b narrow-advice chunk below. Connecting the resulting
  states to the witness tables remains open.

  All three modules are imported by `JoltConstraints.lean`; `lake build
  JoltConstraints` passes. The five public theorems and two embedding definitions
  were checked with `#print axioms`. The step and trace inclusion results use
  exactly `propext`, `Classical.choice`, `Quot.sound` and the allowed Sail constant
  `sys_enable_experimental_extensions`, through the instruction semantics in
  their statements. `narrowAdvice_value` uses only the three standard axioms.
  No new `sorry`, compiler-trust axiom or heartbeat setting was introduced.
  The existing main theorem remains unfinished and fixed-tape; no premise or
  instance definition was changed in the Layer 5a chunk. The later approved
  layout-premise replacement is recorded in the Layer 5b entry below.

  The review clarified the remaining narrow-expansion execution obligation and
  the need to keep the duplicated trace requirements synchronized. The relaxed
  load's error message now says only `invalid width`: it cannot exhaust a tape.

  The updated advice contract is recorded in `model_review.md`.
  PR #2049 removes the length-query candidate; no complete satisfying witness
  for that historical example was constructed.
  The reverse inclusion into the fixed-tape language is now proved in Layer 7.
  Layer 5a was reviewed before starting 5b.
  `CodeUnchanged`
  needs no relaxed counterpart for bytecode execution.
- **Layer 5b, address chunk proved and ready for review:**
  [Layer3/Layout.lean](../JoltConstraints/Soundness/Layer3/Layout.lean) defines
  the approved `RamRegionFits` premise, with `NOTE: to confirm with a16z`,
  and proves two lemmas: the witness-domain bound and the bound on every byte
  of each word. The former run-based predicate and its next-step helper are
  deleted; the main theorem now takes `ramRegionFits`.
  [Layer5/MemoryAddress.lean](../JoltConstraints/Soundness/Layer5/MemoryAddress.lean)
  proves seven public lemmas. The address constraint gives the field encoding
  of the signed sum; the selected and unselected cases recover integer
  equality, including zero; the layout bound then gives the machine range and
  address encoding. The LD and SD lemmas derive the flags and signed immediate
  from the selected bytecode row. Their source-column equality is a local
  induction obligation, not a new soundness premise.

  `lake build JoltConstraints` passes. All nine new public lemmas were checked
  with `#print axioms` and use only `propext`, `Classical.choice` and `Quot.sound`.
  There are no new `sorry`s, compiler-trust axioms or heartbeat settings.
  The existing unfinished `JoltInstance.soundness` was checked separately: it
  still has `sorryAx`, plus the three standard axioms and
  `sys_enable_experimental_extensions`; it remains a fixed-tape target.
  This closes the address-wraparound subproblem under the approved premise.
  Layer 5b still must establish source-register agreement, successful execution
  and post-state agreement, including memory/device behavior at address zero.
- **Layer 5b, narrow-advice execution proved and ready for review:**
  [Program.lean](../JoltConstraints/Soundness/Layer5/Program.lean) composes
  `execWithTapeAnswer` over a generated program. Answers are indexed by local
  row number; only tape instructions use them. Errors and non-success results
  stop execution as in the original `execProgram`. Its step lemma passes the
  exact post-state to the next row.
  [AdviceExpansion.lean](../JoltConstraints/Soundness/Layer5/AdviceExpansion.lean)
  proves the actual `AdviceLB`, `AdviceLH` and `AdviceLW` expansion shapes and
  their execution under this rule. The final state advances the cursor by
  1, 2 or 4 and writes the sign-extended low 8, 16 or 32 bits of the first
  answer. Later row answers have no effect. For rd = x0 the generated sequence
  uses temporary register 40, so the cursor still advances and architectural
  x0 is unchanged. Other state is preserved by the full-state result
  `afterAdviceLoad`, which uses the existing `NativeDispatch.afterDst` model.

  The load establishes the value read by the arithmetic rows, so the proofs
  require no initial register-presence hypothesis. Small read-after-write and
  write-overwrite helpers reuse the existing register proofs; no new finite
  register enumeration or heartbeat setting is needed. All eight new public
  lemmas were checked with `#print axioms`: the three expansion-shape lemmas
  use `propext` and `Quot.sound`; the five execution/composition lemmas use the
  standard three axioms plus the allowed `sys_enable_experimental_extensions`.
  There are no new `sorry`s, compiler-trust axioms or soundness premises.
  Both modules are included in `JoltConstraints.lean`; `lake build
  JoltConstraints` passes. Module builds reported 2.5 s for `Program.lean`
  and 3.5 s for `AdviceExpansion.lean`; these include more than proof elaboration.
  Witness selection, answer recovery and table agreement at the intermediate
  rows still need to be connected to these execution results in the induction;
  this chunk does not establish all of Layer 5b.
- **Layer 5b, register agreement proved and ready for review:**
  [Registers.lean](../JoltConstraints/Soundness/Layer5/Registers.lean) defines
  `RegisterAgreement` and proves four public lemmas: initialization, preservation
  through `advance_pc`, successful canonical-operand reads with table encoding,
  and preservation through a selected instruction's destination write.
  The invariant includes every Sail register's presence, established from
  `initial_state` and preserved using existing write and PC lemmas. The write
  proof combines Layer 2's table update with read-after-write and frame facts,
  derives canonicality from expansion, and uses `registersVal_x0` for x0.
  It covers architectural and virtual destinations without new register
  enumeration. Its successful-write and `RdWriteValue` encoding hypotheses
  must still be proved for each instruction family. RAM, device state and
  control flow are outside this register-only chunk.

  The module is imported by `JoltConstraints.lean`; `lake build JoltConstraints`
  passes. Its module build reported 3.7 s. All four public lemmas were checked
  with `#print axioms` and use only `propext`, `Classical.choice` and `Quot.sound`.
  No new `sorry`, heartbeat setting or soundness premise was introduced.
- **Layer 5b, ADDI execution and register agreement proved and ready for review:**
  [RegisterWrite.lean](../JoltConstraints/Soundness/Layer5/RegisterWrite.lean)
  defines the concrete state `afterWriteDst` and proves that writing any
  canonical destination reaches it. A virtual destination cannot alias a
  protected architectural index: the proof uses register-address injectivity
  and width bounds, without enumerating the 32 architectural registers.
  [AddImmediate.lean](../JoltConstraints/Soundness/Layer5/AddImmediate.lean)
  proves `addi_step` from the context, constraints, selected ADDI row and
  current register agreement. Private lemmas derive operand canonicality,
  metadata, input encodings and the wrapped write value before composing
  execution with `RegisterAgreement.write`. Neither a successful-write
  hypothesis nor a write-value hypothesis is left to the caller.

  The theorem includes architectural and virtual operands and x0. It accepts
  the row's already-decoded 64-bit immediate, including arithmetic wraparound.
  Its exact execution state is `afterWriteDst`; register agreement is proved
  whenever the next column exists. The execution and write-value results do
  not require a next column. Full RAM agreement, bytecode linkage and the
  remaining instruction families are still open.

  Both modules are in the `JoltConstraints` build, which passes. Module builds
  reported 3.6 s for `RegisterWrite` and 4.1 s for `AddImmediate`.
  `#print axioms` checked both public lemmas: the write helper uses only the
  three standard axioms; `addi_step` also includes the allowed Sail constant
  `sys_enable_experimental_extensions`, without assuming its value.
  No new soundness premise, `sorry`, compiler-trust axiom, heartbeat setting
  or finite register enumeration was introduced.
- **Layer 5b, XOR, SLTIU and runtime advice; original reviewed chunk:**
  [Xor.lean](../JoltConstraints/Soundness/Layer5/Xor.lean) and
  [SetLessThanImmediate.lean](../JoltConstraints/Soundness/Layer5/SetLessThanImmediate.lean)
  prove `xor_step` and `sltiu_step` from the selected row, constraints and
  current register agreement. The original private lemmas derived canonical operands,
  metadata, instruction inputs and the write value; Layer 4 interprets the
  lookup, and `RegisterAgreement.write` establishes the next register column.
  Each theorem returns the exact destination-write state and covers aliases,
  architectural and virtual operands, and the last cycle's execution/result.
  SLTIU reads its source before writing the same register, as SC requires.

  [RuntimeAdvice.lean](../JoltConstraints/Soundness/Layer5/RuntimeAdvice.lean)
  proves runtime-advice agreement for any row without `VirtualAdvice`, plus
  absence of such rows throughout each generated SC.W/SC.D expansion in both
  destination branches. These are facts about expanded rows; neither they nor
  the execution lemmas assume anything about LR/SC history. Connecting selected
  rows through the full expansion, RAM agreement and the other instruction
  families remains open. `NoStoreConditional` is still present; this chunk
  neither removes it nor completes Layer 5b.

  All three modules are imported by `JoltConstraints.lean`; `lake build
  JoltConstraints` passed (8744 jobs). Module builds reported 4.3 s for XOR,
  4.9 s for SLTIU and 3.8 s for runtime advice. The five public lemmas passed
  `#print axioms`: only the standard axioms occur, with the allowed Sail
  constant `sys_enable_experimental_extensions` also in the two execution
  lemmas. No new premise, `sorry`, compiler-trust axiom or heartbeat override
  was introduced. Ari reviewed all three files by reading and found them correct.
  This was the weekend review boundary. The 2026-10-15 chunk below implements
  the advice bridge and shared steps planned after that review.
- **Layer 5b, advice bridge and shared steps; implemented, 2026-10-15:**
  [LookupWrite.lean](../JoltConstraints/Soundness/Layer5/LookupWrite.lean) had four
  reusable lemmas, all used by the refactored instruction proofs; two of them,
  `RegisterAgreement.rs1Value` and `rs2Value`, later moved to `RegisterInputs.lean`. The public
  identity in [RuntimeAdvice.lean](../JoltConstraints/Soundness/Layer5/RuntimeAdvice.lean)
  replaces its weaker private helper and connects all three step conclusions
  to the trace's runtime-advice application. XOR and SLTIU share the selected
  metadata and lookup-write argument; ADDI shares the final write/execute/update
  argument. Instruction-specific canonicality, input selection and read/write
  equations remain proved locally. The new arguments and the remaining work
  are described in the PR #2039 section above.

  `lake build` passed for both libraries (8747 jobs). The shared module built
  in 3.6 s; XOR, SLTIU and ADDI built in 4.9 s, 4.0 s and 5.4 s respectively.
  These proofs use the default heartbeat limit. `#print axioms` checked the
  five new public lemmas, all three step lemmas and the three existing
  runtime-advice/SC facts. Only `propext`, `Classical.choice`, `Quot.sound` and
  the allowed Sail constant `sys_enable_experimental_extensions` occur; that
  Sail constant appears in the four execution lemmas. No new premise, `sorry`,
  compiler-trust axiom or heartbeat override was introduced. The main theorem
  and its existing proof gaps are unchanged.

  After the migration and main-theorem cleanup, `lake build JoltBytecode
  JoltConstraints` passed again (8751 jobs). All Lean sources are unchanged
  since that build. Before committing this refactor, the same 11-lemma axiom
  audit was repeated and retained exactly the allowed dependencies above.
  Ari requested committing the completed soundness work and returning to
  Layer 5b; the remaining instruction families are next.
- **Layer 5b, shared operands and six more instruction cases, 2026-10-15:**
  [RegisterInputs.lean](../JoltConstraints/Soundness/Layer5/RegisterInputs.lean)
  now holds `RegisterAgreement.rs1Value` and `rs2Value`, moved unchanged from
  `LookupWrite.lean`. Its two new input lemmas recover either two register
  operands or a register and decoded immediate. XOR, ADD/SUB/MUL and
  VirtualAssertLTE use the former; ADDI, SLTIU and XORI use the latter. Each
  caller derives canonicality and discharges the operand/selection facts from
  its selected instruction. No successful read or execution is assumed.

  | Instructions | Step result | Reused proof |
  | --- | --- | --- |
  | ADD, SUB, MUL | `arithmetic_step` in `Layer5/Arithmetic.lean` | One proof indexed by `RegisterArithmetic`; shared register inputs, the three existing Layer 4 RangeCheck rules, and `registerWrite_step` |
  | LUI | `lui_step` in `Layer5/LoadUpperImmediate.lean` | RangeCheck addition of zero and the decoded immediate, then `registerWrite_step` |
  | XORI | `xori_step` in `Layer5/XorImmediate.lean` | Shared immediate inputs, the existing XOR lookup theorem, and `registerWrite_step` |
  | VirtualAssertLTE | `assertLTE_step` in `Layer5/AssertLessThanEqual.lean` | Shared register inputs, unsigned comparison and `predicate_of_assert`; `RegisterAgreement.noWrite` preserves the table |

  `RegisterArithmetic.instruction` selects the existing ADD/SUB/MUL constructors,
  and `.value` states their wrapped result. They do not replace `execInstr`:
  the common proof checks each of its three branches. The assertion proof
  derives the comparison from `AssertLookupOne`, proves successful execution
  with the entire state unchanged, and derives the next register column from
  the absence of a destination. All step results apply runtime advice as the
  trace does, permit register aliases, retain exact post-states, and cover
  execution at the final cycle. Only next-column agreement requires a successor.

  The local Rust checkout remains at `1c8aaff2`; the inspected tracer,
  instruction-metadata and lookup-query files match public pin `8bbb2357`.
  Source checks cover `tracer/src/instruction/{lui,xori,add,sub,mul,virtual_assert_lte}.rs`,
  their `crates/jolt-riscv/src/instructions/{i,m,assert}` metadata, and
  `crates/jolt-lookup-tables/src/instructions/{riscv,virt}` lookup queries.
  LUI takes the already-decoded immediate; `normalize_imm` preserves its word
  bits. ADD/SUB/MUL wrap at 64 bits; XORI combines the source with that decoded
  word; VirtualAssertLTE compares unsigned words and writes nothing. These
  proofs apply to a selected row of the expanded bytecode, whether it represents
  a source instruction directly or was emitted inside an expansion. They do
  not claim whole-expansion composition or LR/SC-to-Sail equivalence.

  All new modules are imported by `JoltConstraints.lean`. The existing ADDI,
  XOR and SLTIU statements are unchanged. Remaining work includes the nine
  SC.W row kinds named above, RAM/PC agreement and execution-prefix composition.

  Validation: `lake build JoltBytecode JoltConstraints` passed (8756 jobs).
  `#print axioms` checked the 14 affected public soundness lemmas and both
  main theorems. The 14 lemmas use only the three standard Lean axioms and,
  for execution results, the allowed `sys_enable_experimental_extensions`.
  Both main theorems retain exactly their previous dependency sets, including
  their existing proof gaps. No new premise, `sorry`, native proof or heartbeat
  override was added. All 20 inspected Rust source files match `8bbb2357`.
  Review corrections name the remaining SC.W rows and the division, remainder
  and LR/SC expansions using VirtualAssertLTE, clarify which rows of the
  expanded bytecode the proofs cover, and add line numbers to the new Rust
  citations. The FIXME in `soundness.lean` now states that the theorem is false
  today for B6's stopping and panic cases, which the temporary restrictions
  do not cover. Two proof-style edits use a direct `exact` and an explicit
  `simpa only` set; statements are
  unchanged. After these corrections, the same build passed (8756 jobs) and
  all 16 audited axiom sets were unchanged. All 14 files cited in the four
  new instruction headers match `8bbb2357`; each cited line range exists.
- **Layer 5b, alignment and ordinary-RAM stores, 2026-10-15:**
  This chunk tests the connection between the constraints and memory execution.
  [RamAlignment.lean](../JoltConstraints/Soundness/Layer5/RamAlignment.lean)
  proves `ramAddress_aligned` and `ramAddress_mask_aligned`: every encoded
  machine address is eight-byte aligned. Selection gives an aligned layout
  base plus eight times an index; the all-zero selector gives address zero.
  No alignment assumption or successful-access certificate is added.

  [RamStore.lean](../JoltConstraints/Soundness/Layer5/RamStore.lean) proves
  `ram_store_index`. It reuses `stored_dword_get?_hit`, `stored_dword_untouched`
  and `Mmu.write_ram_doubleword_eq` from the instruction-equivalence work.
  Adjacent BitVec extraction lemmas reassemble the eight stored bytes. Reading
  the resulting byte map on the RAM table's eight-byte grid yields the stored
  word at the selected index and the original words everywhere else, including
  where the original byte map was sparse.

  [StoreDoubleword.lean](../JoltConstraints/Soundness/Layer5/StoreDoubleword.lean)
  proves `sd_ram_step` for addresses at or above `RAM_START_ADDRESS`. It derives
  canonical source operands, the signed address encoding, alignment, the Store
  flag, the stored value and a selected RAM index. It then proves successful
  execution with the exact byte-map post-state, the matching single-word
  update in both memory and the witness, and next-cycle register agreement.
  At the last cycle, the same update goes to `RamValFinal`. Source aliases and
  runtime advice are included; no initial RAM value agreement is needed to
  establish this matching update.

  The local `inRam` argument selects the ordinary-RAM branch. `checked` is the
  existing `DoublewordAddressChecks` fact obtainable from `sd_address_checks`
  under the approved restriction and execution-prefix readiness. Neither is
  added to the main theorem or instance. The proof uses the existing
  `RamRegionFits` bound. Connecting the prefix to the selected bytecode row,
  initializing the full RAM invariant, LD execution, device stores and PC
  agreement remain open. This is not a proof of all SD cases or of Layer 5b.

  The inspected local Rust MMU, SD execution and R1CS sources match public pin
  `8bbb2357`. In ordinary RAM, Rust checks only the starting address before
  writing eight bytes. Its fast-path condition also checks that adding seven
  does not wrap; eight-byte alignment and the 64-bit word bound ensure that
  condition for these accesses. No new Jolt issue is claimed by this chunk.

  Validation: all three modules are imported by `JoltConstraints.lean`.
  `lake build JoltBytecode JoltConstraints` passed (8759 jobs). An axiom audit
  checked the four new public lemmas, the 14 previously reviewed Layer 5
  lemmas and both main theorems. The three new memory/address lemmas use only
  `propext`, `Classical.choice` and `Quot.sound`; `sd_ram_step` additionally
  uses the allowed `sys_enable_experimental_extensions`. All 16 previous
  dependency sets are unchanged, including the deferred main-theorem gaps.
  No new `sorry`, native decision proof, heartbeat setting or main-theorem
  premise was added. Existing Lean declarations and unrelated working files
  are unchanged. Reviewed by reading; the final comment corrections refresh
  the `DoublewordAddressChecks` MMU citation to `8bbb2357` and simplify the
  `RamStore.lean` header. Lean declarations are unchanged since validation.
- **Layer 5b, device-memory audit; still open:** `TerminationThenStall` permits
  the standard SDK return sequence and is built, but does not yet
  close RAM agreement. Panic needs separate read and final-flag arguments.
  [DeviceMemoryObstruction.lean](../JoltConstraints/Soundness/Layer5/DeviceMemoryObstruction.lean)
  is a diagnostic artifact: for a generated layout, it proves that a store of
  one to the termination word is ignored by device execution while a selected
  store forces the next RAM-table entry to one. It does not construct a
  satisfying witness. It is imported by `JoltConstraints.lean`, so the root
  build checks it. `MemoryLayout` now derives its equality decision in
  `JoltDevice.lean`. The diagnostic has two `decide +kernel` invocations; a
  direct `lake env lean` check took 5.55 s wall time, and its Lake module build
  took 4.6 s on 2026-10-20. These times include elaboration and kernel checks.
  Ari reports an accepted-proof reproduction for input/advice stores in #2044,
  following #2041; it has not been independently rerun here. The approved
  `TracerAddressChecks` premise now supplies the modeled address assertions for
  attempted LD/SD accesses after relaxed prefixes, including an attempt that
  aborts. It also covers four separately listed, unconfirmed candidates: zero
  stores, the I/O gap, canary stores and accesses at or above `heap_end`.
  Its FIXME requires narrowing or removal as each case is resolved. It does
  not resolve alignment, peripheral dispatch, device value agreement or stopping.

  [MemoryAccessRestriction.lean](../JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean)
  defines the premise, the next-attempt predicate and two application lemmas
  for LD/SD. The unchanged fixed-tape language definition moved to
  [Language.lean](../JoltConstraints/language.lean) to avoid an import
  cycle with the relaxed-run definitions. `lake build JoltConstraints` passes
  (8741 jobs). Both new application lemmas, the premise and `NextStep` were
  checked with `#print axioms`: only the three standard axioms and the allowed
  `sys_enable_experimental_extensions` occur. The main theorem still has its
  existing `sorry`; no new `sorry`, compiler-trust axiom or heartbeat setting
  was added.

  Scratch proofs checked the address predicate by kernel reduction on a layout
  generated by `MemoryLayout.new`, with #2044's configuration: output and SDK
  panic/termination stores pass; input/advice stores and all four newly listed
  address cases fail as described; loads at zero and inside the canary pass.
  Boundary checks also confirm that RAM words starting below an unaligned
  heap/canary boundary retain the tracer's starting-address behaviour. These
  checks validate the restriction, not satisfying witnesses for the candidates.
- **Layer 5b, ordinary-RAM agreement; ready for review, 2026-10-15:**
  [RamInitialization.lean](../JoltConstraints/Soundness/Layer5/RamInitialization.lean)
  proves from `MemoryLayout.new` that checked advice and input overlays end
  below `RAM_START_ADDRESS`. It then identifies each ordinary-RAM word in the
  initial witness with the interpreter's byte-map word. The separate
  [PowerOfTwo.lean](../JoltConstraints/Soundness/Layer5/PowerOfTwo.lean)
  proves the round-up bound used by that layout argument.

  [RamAgreement.lean](../JoltConstraints/Soundness/Layer5/RamAgreement.lean)
  states agreement only for ordinary-RAM table indices. It establishes that
  relation initially, recovers a selected LD read, and preserves it through PC
  preparation, register writes, zero RAM effects and non-memory cycles.
  [LoadDoubleword.lean](../JoltConstraints/Soundness/Layer5/LoadDoubleword.lean)
  combines those facts with the selected LD constraints: an ordinary-RAM LD
  reads the agreed word, writes that value to its destination, executes
  successfully, and preserves agreement at the next or final column.
  [RamStoreAgreement.lean](../JoltConstraints/Soundness/Layer5/RamStoreAgreement.lean)
  applies the existing SD step: the selected table word and interpreter word
  receive the same value, preserving agreement at the next or final column.
  Both steps use the shared nonzero-address lemma in `RamAlignment.lean`.
  The LD citation includes Rust's full execution method; its i32 cast agrees
  with the sign-extended 12-bit immediate used by modeled LD rows.
  The LD and SD lemmas use the existing `RamRegionFits` and local address-check
  facts; no main-theorem premise was added.

  The local Rust files cited for layout, witness initialization, LD and MMU
  reads are byte-identical to public pin `8bbb2357`. Both root targets build
  (`lake build JoltBytecode JoltConstraints`, 8764 jobs). `#print axioms`
  shows only `propext`, `Classical.choice`, and `Quot.sound` for initialization
  and agreement; the LD and SD execution lemmas additionally use the existing
  `sys_enable_experimental_extensions`. Neither new lemma depends on `sorryAx`
  or a native decision axiom. The main-theorem axiom sets are unchanged.
  Reproduce the audit with `#print axioms` for `initialRamWord_eq_ram_doubleword`,
  `sd_ram_step_agreement` and `ld_ram_step` after importing `JoltConstraints`.

  Ordinary RAM now has the initialization and per-step preservation pieces.
  The full execution-prefix induction has not yet composed them with every
  instruction case. Device reads and writes, panic/termination behavior and
  the remaining Layer 5b instruction families remain open.
- **Layer 5b, routine register rows; ready for review, 2026-10-15:**
  [BitwiseBinary.lean](../JoltConstraints/Soundness/Layer5/BitwiseBinary.lean)
  proves one shared step for AND, OR and ANDN.
  [XorRotation.lean](../JoltConstraints/Soundness/Layer5/XorRotation.lean)
  covers all twelve XORROT rows: rotations 32, 24, 16 and 63; left rotation 1;
  and word rotations 16, 12, 8, 7, 22, 19 and 6.
  [RegisterComparison.lean](../JoltConstraints/Soundness/Layer5/RegisterComparison.lean)
  covers SLT and SLTU. These are 17 additional native row kinds. Each proof
  derives its lookup result and successful register write from the selected
  row and register agreement, including operand/destination aliasing and the
  final trace cycle. None adds a main-theorem premise.

  The eight cited Rust tracer files are byte-identical between the local
  checkout and public pin `8bbb2357`. All three modules are imported by
  `JoltConstraints.lean`; `lake build JoltBytecode JoltConstraints` passed
  (8767 jobs). `#print axioms` gives each new step only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`. The main-theorem axiom sets are
  unchanged. Reproduce the audit with `#print axioms` for `bitwise_step`,
  `xorRotation_step` and `comparison_step` after importing `JoltConstraints`.
  No new `sorry`, native decision proof or heartbeat setting was added.

  The four register-based virtual shifts require a right-shift mask of the
  correct shape. The paired producer lemma recorded below now derives that
  shape from a preceding mask write, and `selected_registerShift_fed` in
  `Layer6/BytecodePC.lean` identifies that predecessor among the selected rows.
  Applying them in the execution-prefix induction still requires state linkage.
- **Layer 5b, word arithmetic, virtual binary and FENCE rows; ready for review,
  2026-10-15:**
  [WordArithmetic.lean](../JoltConstraints/Soundness/Layer5/WordArithmetic.lean)
  shares one step over ADDW, SUBW, MULW and MULHU. The existing Layer 4 rules
  consume the arithmetic flag and wide operand, then return either the
  sign-extended low word or the unsigned high product.
  [VirtualBinary.lean](../JoltConstraints/Soundness/Layer5/VirtualBinary.lean)
  shares one step over Pext, PextSigned, ShiftDataB/H/W and NegateIf. Its
  interleaved table rules hold for arbitrary source words, so these steps do
  not need a mask-shape hypothesis.
  [Fence.lean](../JoltConstraints/Soundness/Layer5/Fence.lean) proves that FENCE
  executes without changing the machine state and advances both register and
  ordinary-RAM agreement through the next or final column. Together these
  files cover eleven additional native row kinds. The arithmetic and virtual
  binary steps derive the constrained destination value and next-cycle
  register agreement. No main-theorem premise was added.

  The eleven cited Rust tracer files in the local checkout match public pin
  `8bbb2357` and have no local edits. All three modules are imported by
  `JoltConstraints.lean`; `lake build JoltBytecode JoltConstraints` passed
  (8770 jobs). `#print axioms` for the three new steps lists only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`; the main-theorem axiom sets are
  unchanged. Reproduce the audit with `#print axioms` for
  `wordArithmetic_step`, `virtualBinary_step` and `fence_step` after importing
  `JoltConstraints`. No new `sorry`, native decision proof or heartbeat setting
  was added.
- **Layer 5b, unary word and shift-mask rows; ready for review, 2026-10-15:**
  [UnaryWord.lean](../JoltConstraints/Soundness/Layer5/UnaryWord.lean)
  shares a step for VirtualSignExtendWord, VirtualZeroExtendWord, VirtualPow2,
  VirtualPow2W, VirtualShiftRightBitmask, VirtualShiftRightBitmaskW and
  VirtualRev8W. All seven rows send their source value through AddOperands
  with a zero right input, then use that value directly as the lookup index.
  The proof derives the selected inputs, lookup value, successful execution
  and next-cycle register agreement;
  the row immediate is ignored by the circuit and interpreter. VirtualRev8W
  uses kernel-checked bit-extensional and arithmetic lemmas to equate the
  interpreter's byte reversal with the table; it does not reuse completeness's
  `bv_decide` lemmas. The two shift-mask rows produce the words needed by
  later shift rows; their local producer bridge is recorded below.

  The seven cited local Rust tracer files are byte-identical to public pin
  `8bbb2357` and unmodified. `UnaryWord.lean` is imported by
  `JoltConstraints.lean`; `lake build JoltBytecode JoltConstraints` passed
  (8778 jobs). `#print axioms unaryWord_step` lists only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`. The main-theorem axiom sets are
  unchanged. Reproduce the audit with `#print axioms unaryWord_step` after
  importing `JoltConstraints`. No new main-theorem premise, `sorry`,
  native decision proof or heartbeat setting was added.
- **Layer 5b, immediate logic and arithmetic rows; ready for review,
  2026-10-15:**
  [ImmediateLogic.lean](../JoltConstraints/Soundness/Layer5/ImmediateLogic.lean)
  shares one step for ANDI, ORI and SLTI. SLTI reuses the signed-comparison
  value lemma exported from `RegisterComparison.lean`.
  [ImmediateArithmetic.lean](../JoltConstraints/Soundness/Layer5/ImmediateArithmetic.lean)
  shares one step for ADDIW, VirtualMULI and VirtualMULIW. Their existing
  Layer 4 rules turn the arithmetic operand into either a full-word result or
  a sign-extended low word. All six cases prove the constrained write,
  successful execution and next-cycle register agreement, including aliases.

  The six cited local Rust tracer files are byte-identical to public pin
  `8bbb2357` and unmodified. Both modules are imported by
  `JoltConstraints.lean`; `lake build JoltBytecode JoltConstraints` passed
  (8773 jobs). `#print axioms` for the two steps lists only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`. The main-theorem axiom sets are
  unchanged. Reproduce the audit with `#print axioms immediateLogic_step` and
  `#print axioms immediateArithmetic_step` after importing `JoltConstraints`.
  No new premise, `sorry`,
  native decision proof or heartbeat setting was added. This and the four
  added unary cases bring the covered count to 51 of 88 row kinds,
  with LD and SD counted for ordinary RAM only.
- **Layer 5b, remaining 29 routine kinds; ready for review, 2026-10-15:**
  The prior immediate-logic, immediate-arithmetic and unary-mask steps cover
  ten kinds on Ari's list. [Movsign.lean](../JoltConstraints/Soundness/Layer5/Movsign.lean)
  adds VirtualMovsign. [ImmediatePowerMask.lean](../JoltConstraints/Soundness/Layer5/ImmediatePowerMask.lean)
  covers VirtualPow2I, VirtualPow2IW and VirtualShiftRightBitmaskI.
  [AddressMasks.lean](../JoltConstraints/Soundness/Layer5/AddressMasks.lean)
  covers VirtualAlignAddr and WindowMaskB/H/W, using the decoded base-plus-
  immediate wide lookup index. [ImmediateShift.lean](../JoltConstraints/Soundness/Layer5/ImmediateShift.lean)
  covers VirtualSRLI, VirtualSRAI, VirtualSRLIW and VirtualSRAIW; bytecode's
  `immShiftOk` supplies their mask shape. `UnaryWord.lean` now covers Rev8W.
  [RegisterShift.lean](../JoltConstraints/Soundness/Layer5/RegisterShift.lean)
  covers VirtualSRL, VirtualSRA, VirtualSRLW and VirtualSRAW. Its paired-row
  lemma derives the mask shape from the concrete post-state of the immediately
  preceding VirtualShiftRightBitmask(W) write and `masksFed`; the dispatcher
  still has to connect those adjacent selected rows and their states.
  `selected_registerShift_fed` in `Layer6/BytecodePC.lean` now proves that the
  cycle before a selected shift selects the previous bytecode slot, and that
  this slot's instruction produces the shift's mask. It needs that earlier slot
  to be a real row, because a padding no-op also sets `DoNotUpdateUnexpandedPC`.
  The induction must still supply that real-row fact, rule out a register shift
  at cycle 0, and identify the shift's input state with the producer's
  post-state before applying `registerShift_step_after_producer`.
  VirtualROTRI and VirtualROTRIW are excluded by `immShiftOk` and the existing
  `bytecodeTable_ne_plainRotate` proof, so no execution step is needed.

  The 17 cited local tracer files are byte-identical to public pin `8bbb2357`.
  All new modules are imported by `JoltConstraints.lean`; `lake build JoltBytecode
  JoltConstraints` passed (8778 jobs). `#print axioms` for `movsign_step`,
  `immediatePowerMask_step`, `addressMask_step`, `immediateShift_step`,
  `unaryWord_step`, `registerShift_step`, `registerShift_step_after_producer`
  and `bytecodeTable_ne_plainRotate` contains only `propext`,
  `Classical.choice`, `Quot.sound` and, for execution steps, the existing
  `sys_enable_experimental_extensions`. The producer-shape bridge uses only
  the first three. No new `sorry`, native decision proof, heartbeat setting or
  main-theorem premise was added. This brings the local step count to 68 of
  88 row kinds, with LD and SD counted for ordinary RAM only; two further
  row kinds are proved unreachable. The dispatcher will apply
  `OrdinaryRamAgreement.noAccess` to rows without Load or Store and
  `OrdinaryRamAgreement.afterWriteDst` after register writes.
- **Layer 5b, six assertion rows; ready for review, 2026-10-15:**
  [AssertionsBinary.lean](../JoltConstraints/Soundness/Layer5/AssertionsBinary.lean)
  proves a shared step for VirtualAssertEQ, VirtualAssertValidDiv0 and
  VirtualAssertValidUnsignedRemainder. The selected comparison or conditional
  table and `assertLookupOne` force the interpreter's acceptance condition.
  This includes AssertEQ with a nonzero spoil immediate: Rust may retire a
  failed spoil assert, but the constraints still force equal operands.
  [AssertionsAlignment.lean](../JoltConstraints/Soundness/Layer5/AssertionsAlignment.lean)
  proves VirtualAssertHalfwordAlignment and VirtualAssertWordAlignment. Their
  wide AddOperands lookup forces the low machine word's alignment test, even
  when the address addition wraps at 64 bits.
  [AssertionMulOverflow.lean](../JoltConstraints/Soundness/Layer5/AssertionMulOverflow.lean)
  proves VirtualAssertMulUNoOverflow from the wide product lookup. All six
  steps retire successfully, preserve the state and register agreement, and
  work at the final trace cycle. The six cited Rust `exec` methods were read
  at pin `8bbb2357`; their ranges are in the Lean headers. The files are
  imported by `JoltConstraints.lean`; `lake build JoltBytecode JoltConstraints`
  passed (8781 jobs). `#print axioms` for `binaryAssertion_step`,
  `alignmentAssertion_step` and `mulAssertion_step` shows only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`. No new premise, `sorry`, native
  decision proof or heartbeat setting was added. The local step count is now
  74 of 88 row kinds, with LD and SD counted for ordinary RAM only; two more
  kinds are proved unreachable. The global dispatcher is still open.
- **VirtualHostIO live-mode audit; step open, 2026-10-15:**
  The modeled `JoltInstance.initial_state` calls `init_state` with its default
  HostIO config, whose mode is `.live`. At pin `8bbb2357`, Rust's `Cpu::new`
  also starts `HostIo::Live` (`tracer/src/emulator/cpu.rs:450-473`); only
  parallel chunk workers switch to `Replay` (`tracer/src/parallel.rs:130-163`).
  Pass 1 remains the authority for final advice and device state
  (`tracer/src/parallel.rs:404-411`). Thus the replay no-op branch in
  `JoltISA.execHostIOWith` cannot justify the theorem's HostIO step.
  A live advice-write call reads memory and appends bytes to the advice tape;
  marker and print calls can read memory and reject invalid events
  (`tracer/src/emulator/cpu.rs:1056-1129`). The next proof must connect those
  reads and tape updates to the execution-prefix invariant. Ari added
  `HostCallsSucceed` to `TemporaryRestrictions`, requiring successful execution
  of every next attempted host call for every private input and relaxed prefix.
  `host_call_exec_sail_frame` now uses it to prove that an attempted HostIO row
  retires successfully and preserves Sail registers and RAM, while allowing
  its advice tape to change. `lake build JoltConstraints` passed with the
  restriction and these facts. It is a program-execution condition,
  independent of witness columns; it does not establish register-table
  agreement. The frame lemma's axiom list contains only `propext`,
  `Classical.choice`, `Quot.sound` and the existing
  `sys_enable_experimental_extensions`.

  **A separate HostIO register-update obligation remains.** The source decoder
  accepts a VirtualHostIO instruction with a nonzero encoded `rd`, and the
  tracer captures that register before and after the call although the call
  does not write it. The bytecode selector nevertheless chooses `rd` for the
  register history. VirtualHostIO has no lookup table and does not set
  `WriteLookupOutputToRD`, so the current local constraints do not visibly
  force its `RdInc` to zero. The call-success restriction does not constrain
  that increment. Establish a zero-increment consequence from the full
  constraints or treat this as a separate underconstraint candidate; no
  satisfying witness has been constructed. Pinned sources: `crates/jolt-program/src/image/decode.rs:196-208`,
  `tracer/src/instruction/registers/i.rs:51-69`, and
  `crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:56-79`.
  Ari approved `HostCallRdZero` as a temporary source-program restriction:
  every source HostIO names `x0`, excluding the architectural-register case.
  It does not itself settle the temporary case: Rust rewrites a side-effecting
  `rd = x0` HostIO destination to a virtual register
  (`crates/jolt-riscv/src/kind.rs:1345-1347`,
  `crates/jolt-program/src/expand/materialize.rs:79-90`). At pin `8bbb2357`,
  `ExpansionAllocator::allocate` draws only from registers 40–47; reserved
  registers 32 and 33 hold the LR/SC reservations
  (`crates/jolt-program/src/expand/allocator.rs:1-23, 115-139, 184-199`).
  `ExpansionFacts.expand_temps_ok` now proves from every source expansion that
  each temporary's first read follows a write within that expansion. A row
  that reads and writes the same temporary still needs a prior write. The
  global register-agreement induction must use this fact to discard a HostIO
  temporary after its one-row expansion; that composition remains open. No
  satisfying witness for the suspected underconstraint has been constructed.
  Also, the model initializes `hostIO.overflowChecks` to `false`, so the
  current success condition alone does not exclude pointer wraparound in a
  Rust build that checks arithmetic overflow. The exact reachable case still
  needs verification.
  With `HostCallRdZero` and the expansion-liveness check included,
  `lake build JoltConstraints` passed (8783 jobs). `#print axioms` for
  `ExpansionFacts.expand_temps_ok` reports only `propext`, `Classical.choice`
  and `Quot.sound`; `host_call_exec_sail_frame` additionally reports the
  existing `sys_enable_experimental_extensions`.
- **Language decision, 2026-10-15:** Ari decided the theorem keeps
  `JoltInstance.InLanguage`. Jolt's tracer reads one tape whose contents the
  prover chooses; the relaxed semantics is a proof device.
  Rebuilding one tape from the witness's answers is proved in Layer 7.
  `JoltInstance.soundness` and `JoltInstance.completeness` now take bundled
  assumptions (`Soundness/Assumptions.lean`, `Completeness/Assumptions.lean`;
  commit `8f6d59f`).
  Ari then made L exactly what Jolt's code says it proves: `InLanguage` also
  requires that Jolt's prover accepts the trace and that no spoil assert fails.
  Completeness now takes only `CompletenessAssumptions` and `InLanguage`, and
  concludes that some private inputs and witness satisfy `AllConstraints`;
  `HonestTrace.ProverAccepts` is removed.
  Soundness must now also prove those two facts; they are helpers C and D in `TopLevel.lean`.

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
   and the panic-store case in B6.
   Also open: whether and how the verifier enforces the separate zero-store,
   I/O-gap, canary-store and heap-boundary cases listed above. These four remain
   code-reading candidates, without complete witnesses.
   Assumed meanwhile: the approved temporary `TracerAddressChecks` premise,
   with a FIXME to narrow or remove it as each case is resolved and proved.
4. **Temporary restrictions added since, each needing a write-up for the batch.**
   - `HostCallsSucceed`: host calls that fail in Jolt's tracer pass the
     constraints as no-op rows.
   - `HostCallRdZero`: nothing forces a host-call row's destination register
     to stay unchanged. Even a source `x0` destination becomes a temporary.
   - `TerminationThenStall`: B6's stopping case, and the termination word's
     device/table mismatch.
   - `PanicStoresOne`: a store of 0 proved as "no panic", and loads of the panic word after a store.
     Written up in `blog/content/blog/completeness-and-soundness/index.md`.
   - `ClaimsNoPanic`: stopping early on a "panicked" claim.
     Written up in `blog/content/blog/proof-stops-at-any-jump/index.md`.
   - Each finding gets its own post under `blog/content/blog/`.

## First milestone

Layer 1(b)'s selector proofs and Layer 1(c)'s read proofs have been reviewed.
Layer 2's register proofs and review corrections are complete. Layer 3's eighteen
RAM lemmas are proved and ready for review: histories, boundary updates,
non-memory and load effects, remapping, initialization, and PC preparation.
Layer 3's review exposed the address-wraparound case; Ari approved the instance-only
`RamRegionFits` premise, pending a16z's confirmation. The integer no-wrap
derivation and machine-address encoding are proved in Layer 5b.
Layer 4(a)'s twelve lemmas cover table selection, identity-address recovery,
and arithmetic RangeCheck. Layer 4(b) is proved and reviewed: operand recovery
and bitwise/comparison table operations. Layer 4(c) is also proved and reviewed,
including the remaining table operations, input/output connections and
advice word recovery. Layer 5a now adds the relaxed tape semantics and proves
fixed-tape inclusion and narrow-answer truncation. It is built and reviewed by
reading. Layer 5b now includes the address proofs, full execution of the
three narrow-advice expansions, and the shared register-agreement invariant
with initialization, read, write and no-write rules. ADDI, XOR, SLTIU, LUI,
XORI, ADD/SUB/MUL and VirtualAssertLTE now derive their local execution and
preserve register agreement, reusing common operand and update proofs.
AND, OR, ANDN, all twelve XORROT variants, SLT and SLTU now also have grouped
steps from their Layer 4 table rules.
ADDW, SUBW, MULW, MULHU, Pext, PextSigned, ShiftDataB/H/W and NegateIf now
have grouped steps too. FENCE preserves both register and ordinary-RAM
agreement across its no-effect step.
VirtualSignExtendWord and VirtualZeroExtendWord have a shared step too.
Four source-based power and shift-mask rows, plus ANDI, ORI, SLTI, ADDIW,
VirtualMULI and VirtualMULIW, now have grouped steps as well.
The remaining immediate powers, address masks, right shifts, Movsign and
Rev8W also have local steps; the two plain immediate rotates are unreachable.
`ramAddress_aligned` derives eight-byte alignment from RAM selection;
`sd_ram_step_agreement` connects ordinary-RAM SD execution to matching byte-map
and witness-word updates. Initial ordinary-RAM agreement and the LD step are
proved as well. The six remaining assertion rows have steps too. Layer 6's
bytecode/PC bridge proves entry selection, next-slot selection inside an
expansion, and the link from a register shift to the row producing its mask.
Temporary restrictions now also cover host calls and the termination word.
`VirtualHostIO` and JAL now have steps.
Layer 5b still needs JALR, the six branches, `VirtualAdviceLoad`, `VirtualAdvice`, device accesses and the composition; see Closing Layer 5b under [Layer 5b](#layer-5b-one-execution-step).
The separate Akita model remains future work.


### 2026-10-21: tape-rebuild closing steps 1–5

`rebuild_rows` constructs the fixed-tape execution by mapping the relaxed rows, with `narrow_load_shape` as its sole staged dependency.
The six certificate fields are proved: length, execution, initialization, linkage, row agreement and source-start agreement.
Loads read the low answer bytes from the rebuilt prefix, and the following multiply restores full state agreement for a narrow load.
Non-load instructions preserve the rebase while host writes append the same suffix.
The shared arithmetic proof handles all narrow widths, including the x0 destination rewrite to temporary register 40.
`read_afterDst` and `afterDst_afterDst` in `AdviceExpansion.lean` are now public and reused.
The seven unused expansion-specific or width-specific lemmas and two unused replay helpers were removed.
The existing long tape-growth proof was split into its used frame lemmas, and pending-load shape arguments share one bytecode helper.
The protected statements and definitions are unchanged.
Step 6, done later, proved `narrow_load_shape`; see [Tape rebuild: step 6](#tape-rebuild-step-6-2026-10-21).

Validation used an isolated copy of the build cache because this worktree's `.lake` links to the main worktree's cache.
`lake -f /private/tmp/tape-rebuild-lakefile.toml build JoltConstraints.Soundness.Layer7.TapeRebuild` passed all 8,591 jobs, rebuilding this worktree's changed dependencies.
The temporary configuration changes only the build directory.
The complete `TapeRebuild.lean` check took **8.52 seconds** wall time; Lake reported **9.2 seconds** for its build job.
`git diff --check` passed.
The only file warnings were the staged `narrow_load_shape` gap and two existing `simpa` style suggestions.

At that point `#print axioms untrustedAnswerLanguage_implies_inLanguage` reported `propext`, `Classical.choice`, `Quot.sound`, the existing `sys_enable_experimental_extensions`, and `sorryAx`.
A second `Lean.CollectAxioms` traversal with `narrow_load_shape` already visited reported the same axioms except `sorryAx`.
Thus the staged bytecode shape was then the only route to `sorryAx` in the reverse inclusion; step 6 removed it.

No existing private helper gained hypotheses.
The new `lowAnswer_muli` and `exec_muli_truncated` helpers require `0 < width` and `width < 8`.
Their caller gets positivity from `UntrustedAnswerRun.pendingBefore_width`, which uses the preceding executed load's valid width, and gets narrowness from the bytecode shape.
The positive-width premise ensures that the six-bit shift immediate does not wrap from 64 to zero.
No limit was raised and no new `bv_decide`, `native_decide` or `decide +kernel` was used.

The following are every new or changed declaration's elaboration times, measured with Lean's `#time` and `Elab.async=false` after loading imports.
A value of 0 ms is below the timer's millisecond resolution.
Documentation-only changes are included.
The slowest new or changed declaration was `replayRow_executes_nonload` at **574 ms**.

| Declaration in `TapeRebuild.lean` | Elaboration (ms) |
|---|---:|
| `tapeGrowth_lift` | 2 |
| `tapeGrowth_append` | 4 |
| `tapeGrowth_read` | 5 |
| `tapeGrowth_write` | 12 |
| `tapeGrowth_storeFold` | 7 |
| `tapeGrowth_loadDoubleword` | 22 |
| `tapeGrowth_storeDoubleword` | 37 |
| `tapeGrowth_load` | 6 |
| `tapeGrowth_readHostBytes` | 11 |
| `tapeGrowth_execHostIO` | 206 |
| `execInstr_tapeGrowth` | 570 |
| `execWithTapeAnswer_load_width` | 8 |
| `UntrustedAnswerRun.load_width` | 42 |
| `UntrustedAnswerRun.postCursor_step` | 434 |
| `rebuiltTape_read_exact` | 218 |
| `ReplayStateAgreement` | 1 |
| `swapBytes` | 3 |
| `swapResult` | 3 |
| `SwapInvariant` | 0 |
| `SwapAppend` | 2 |
| `RebuildAgreement` | 43 |
| `tapeHostSuffix` | 2 |
| `rebaseTapeState` | 1 |
| `narrowLoadAt?` | 5 |
| `pendingBefore?` | 2 |
| `dstSource` | 1 |
| `replayState` | 2 |
| `replayRow` | 63 |
| `narrow_load_shape` | 5 |
| `narrowLoadAt?_eq_some` | 37 |
| `narrow_load_next_not_start` | 10 |
| `pendingBefore?_shape` | 28 |
| `pendingBefore?_none_of_start` | 5 |
| `pendingBefore?_none_of_load` | 6 |
| `narrowAdvicePending_post_iff` | 6 |
| `narrowAdvicePending_pre_iff` | 24 |
| `replaceDst_sideEffecting` | 5 |
| `dstSource_sideEffecting` | 3 |
| `rebaseTapeState_replaceDst` | 13 |
| `rebaseTapeState_afterDst` | 1 |
| `replaceDst_nextPC` | 5 |
| `replayState_nextPC` | 4 |
| `replayState_agreement` | 6 |
| `narrowLoadAt?_none_of_ends` | 10 |
| `replayRow_agrees` | 31 |
| `replayRow_sourceStartPre` | 64 |
| `replayState_initial` | 5 |
| `UntrustedAnswerRun.pendingBefore_width` | 343 |
| `lowAnswer_muli` | 31 |
| `sourceValue_afterDst` | 1 |
| `exec_muli_truncated` | 10 |
| `exec_rebased` | 5 |
| `swap_answer_load` | 9 |
| `replay_load_eq_answer` | 97 |
| `replayRow_executes_load` | 232 |
| `replayRow_executes_nonload` | 574 |
| `replayRow_executes` | 122 |
| `replayRow_starts` | 78 |
| `replayRow_linked` | 379 |
| `replayRows_at` | 5 |
| `replayRows_pair` | 56 |
| `RebuiltRows` | 246 |
| `rebuild_rows` | 67 |
| `RebuildAgreement.ram_address_eq` | 160 |

| Declaration in `AdviceExpansion.lean` | Elaboration (ms) |
|---|---:|
| `read_afterDst` | 9 |
| `afterDst_afterDst` | 23 |


### Tape rebuild: generic adjacent-row lift (2026-10-21)

`Soundness/Layer7/AdjacentRows.lean` now provides a checker-independent lift from an arbitrary property of each materialized expansion's instruction list to adjacent bytecode rows.
`Pairs` selects the earlier item with side 0 (load/multiply) or the later item with side 1 (mask/shift).
`materialized_pairs` derives the earlier row's continuation and the later row's false `starts_source` flag from `ExpandedRows` countdown and start metadata.
`expand_program_pairs` transports these local pairs through concatenation, so a pair cannot cross a source boundary.
The file imports only `program_facts`; it does not depend on `expand_ok`, `shiftsOk`, or an advice checker.
`trace_interface.lean` was unchanged at this point.
Step 6 later moved `ShiftPairs` onto this lift and proved `narrow_load_shape` once `expand_ok` supplied `advicePairsOk`.

The isolated Lake target `JoltConstraints.Soundness.Layer7.AdjacentRows` builds.
`#print axioms expand_program_pairs` reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
No limit was raised and no new `bv_decide`, `native_decide`, or `decide +kernel` was used.
All new declaration times below use `#time` with `Elab.async=false`.

| Declaration in `AdjacentRows.lean` | Elaboration (ms) |
|---|---:|
| `Pairs` | 11 |
| `pairs_append` | 87 |
| `pairs_flatten` | 11 |
| `materialized_pairs` | 93 |
| `expand_program_pairs` | 45 |


### Tape rebuild: shared instruction frame (2026-10-21)

`InstructionEquivalence/ProofSupport/InstructionFrame.lean` now proves `execInstr_rule` once for a reflexive, transitive relation on `SailJoltState`.
`Rules` records preservation under Sail-state replacement (covering Sail steps and RAM stores), virtual-register writes, successful device byte stores, and advice-tape appends.
The theorem also takes a conditional obligation for a successful advice-tape read when the instruction is `VirtualAdviceLoad`.
This obligation is necessary because a tape read advances the cursor, which `TapeGrowth` forbids.
`execInstr_tapeGrowth` discharges it using its existing `notLoad` hypothesis; `execInstr_rule_of_device_relation` discharges it because changing the tape leaves the device unchanged.
Both existing theorem statements are unchanged, as are the statements and source of their callers.

The two frame proofs are now short instances of this theorem.
The shared proof uses `StatePreservation.Preserves` and `preservation_auto`, with one traversal of the instruction constructors.
Eleven tape-specific primitive helpers were removed.
The existing public device-register-write and raw-store lemmas also use the shared primitive proofs, with their statements unchanged.

The isolated Lake build of `JoltConstraints.Soundness.Layer7.TapeRebuild` and `JoltConstraints.Completeness.Helpers.IOSetupFrame` passed all 8,605 jobs.
This rebuilt the existing device-frame callers, including `TapeSemantics`, `memory_presence`, and the atomic-instruction proofs.
`git diff --check` passed.
The shared instruction theorem and both instances have only `propext`, `Classical.choice`, `Quot.sound`, and the existing `sys_enable_experimental_extensions` as axioms, with no `sorryAx`.
At this point the reverse inclusion's dependency audit still found `sorryAx` only through `narrow_load_shape`; step 6 removed it.
No limit was raised and no new `bv_decide`, `native_decide`, or `decide +kernel` was used.

All times below use Lean's `#time` with `Elab.async=false`, after loading imports.
The before measurements use the original complete source files; the after measurements use the modified complete source files.
A value of 0 ms is below the timer's millisecond resolution.
The shared instruction theorem takes 878 ms; neither instance repeats its instruction traversal.

| Existing declaration | Before (ms) | After (ms) |
|---|---:|---:|
| `execInstr_tapeGrowth` | 580 | 6 |
| `execInstr_rule_of_device_relation` | 1363 | 4 |

| New declaration in `InstructionFrame.lean` | Elaboration (ms) |
|---|---:|
| `Rules` | 5 |
| `writeDst_rule` | 14 |
| `lift_rule` | 0 |
| `readSrc_rule` | 6 |
| `storeRaw_rule` | 29 |
| `storeFold_rule` | 6 |
| `loadDoubleword_rule` | 22 |
| `storeDoubleword_rule` | 32 |
| `load_rule` | 10 |
| `readHostBytes_rule` | 11 |
| `execHostIO_rule` | 212 |
| `execInstr_rule` | 878 |

| Other changed declaration in `DeviceFrame.lean` | Elaboration (ms) |
|---|---:|
| `writeDst_rule_of_device_relation` | 2 |
| `store_raw_same` | 2 |


### Tape rebuild: step 6 (2026-10-21)

Rebased `feat/layer7-tape-rebuild` onto Ari's supplied step (c) commit `de5aff70de66d290ceaeb6e7357ba352b855c5d0`.
The previous branch tip is retained at `backup/tape-rebuild-before-step-c` (`53f0608`).
The only rebase conflict was the stale tape-rebuild paragraph in `model_review.md`; the completed stopping proof and completed tape work are both retained.

`ExpansionFacts.expand_instruction_property` transports any property supplied by the native and sequence checks to the instruction list of materialized rows, using the existing `expand_instruction_checks` theorem.
The advice instance decodes the two accepted register forms: the same nonzero architectural register throughout, or virtual register 40 for the x0 rewrite.
`advicePairsOk_narrow` locates the resulting multiply in the checked instruction list.
`narrow_load_shape` then uses `AdjacentRows.expand_program_pairs` with side 0 to obtain the exact multiply and the load's continuation flag in bytecode.
The existing `ExpansionRows.expand_program_shiftPairs` uses the same lift with side 1.
Its old stamping, per-expansion, append, and flatten transport lemmas were deleted because no proof uses them.

All protected statements are unchanged, including `narrow_load_shape`, `untrustedAnswerLanguage_implies_inLanguage`, `rebuild_valid_run`, `RebuiltRows`, `RebuildAgreement`, `ReplayStateAgreement`, and `NarrowAdvicePending`.
No existing helper gained a hypothesis.
No limit was raised and no new `bv_decide`, `native_decide`, or `decide +kernel` was used.

`lake -f /private/tmp/tape-rebuild-lakefile.toml build JoltBytecode JoltConstraints` passed all 8,802 jobs using the isolated build cache.
The complete `TapeRebuild.lean` timing and axiom-audit check took 28.14 seconds wall time while the full build was still running.
Lake reported 21 seconds for its `TapeRebuild.lean` job during that build.
`git diff --check` passed.
`TapeRebuild.lean` has no `sorry`; its only warnings are two pre-existing `simpa` style suggestions.
`#print axioms narrow_load_shape` reports only `propext`, `Classical.choice`, and `Quot.sound`.
`#print axioms untrustedAnswerLanguage_implies_inLanguage` reports those three axioms plus the existing `sys_enable_experimental_extensions`, with no `sorryAx`.
A dependency traversal also rejects any occurrence of `sorryAx` and passed for the reverse inclusion.
The generic materialization property and the migrated shift-pair theorem have only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

The following are all added or changed declarations, measured with `#time` and `Elab.async=false` after loading imports.

| Declaration | File | Elaboration (ms) |
|---|---|---:|
| `expand_instruction_property` | `expansion_facts.lean` | 6 |
| `expand_program_shiftPairs` | `trace_interface.lean` | 45 |
| `regidx_eq_of_beq` | `TapeRebuild.lean` | 3 |
| `advicePairsOk_head` | `TapeRebuild.lean` | 65 |
| `advicePairsOk_narrow` | `TapeRebuild.lean` | 57 |
| `narrow_load_shape` | `TapeRebuild.lean` | 40 |
