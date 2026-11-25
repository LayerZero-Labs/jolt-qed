# Guidance for agents

This repository proves completeness and soundness of the Jolt zkVM in Lean.
Ari reviews the work; read this file before starting any task.

## How the work is done

The soundness proof is built top-down.
State each lemma with `sorry` first, prove its caller from it, build, and stop for Ari's review before proving the lemma itself.
Never write a bottom-up lemma that no staged statement needs.

The state of the proof lives in the repository, not in any one session:

- `methods/soundness.md`: the plan, the layers, and the current status.
- `JoltConstraints/documentation/model_review.md`, "Proofs owed": every remaining `sorry` and what it needs.
- `reports/`: dated audit reports, named `YYYY-MM-DD-<topic>.md`.
  Read the newest before starting.
  `reports/2026-10-29-soundness-statement-audit.md` checks the soundness statement against Jolt at `5def437f`.

File every audit or closing report in `reports/`, never in `methods/`.
State the date, the Jolt commit and the Lean commit it checked.
Git keeps old reports; delete a plan or report once its content is in the code or in the three places above.

## Review

Claude, in a separate session, is the auditor.
It reviews every staged statement and every report before Ari approves it.
It checks for drift from Jolt's Rust code, false or weak statements, new assumptions, proof quality against this file, and whether the docs match the code.
Write your reports so they can be checked: name each declaration with its file and line, and list every statement change, added hypothesis, `bv_decide` use and any proof slower than about ten seconds.

## When stuck, discuss first

Stop and bring the problem to Ari before doing any of the following:

- a brute-force case split;
- copying an existing proof for another case;
- raising any limit;
- changing a statement or definition;
- continuing after about 30 to 45 minutes without progress on one lemma.

Report the goal state, what you tried, why it failed, and the generalization or statement change you propose.
Do not work around the problem alone.
If you believe a staged statement is false, stop and report the exact missing fact.

## Rules

- Do not change L (`JoltInstance.InLanguage`), core definitions, restrictions, or any statement Ari has approved.
  Avoid drift between the model and Jolt's code.
- Do not add premises to a theorem.
  A lemma's hypotheses must be ones its caller can prove.
- Never write a theorem or `sorry` you know to be false.
- Never leave `sorry` inside a proof body; make each gap its own named, stated lemma.
- Never replace a proved fact with `sorry`.
- Do not use `native_decide` or `decide +kernel`, and never raise `maxHeartbeats`.
- `bv_decide` is accepted for now, to make progress; it will be removed later.
  List every new use in your report, and add it to the `bv_decide` list in "Proofs owed" (`JoltConstraints/documentation/model_review.md`).
- Delete every lemma no proof uses.
- For now (Ari, 2026-10-22), correctness comes before speed: the first goal is to learn whether the soundness theorem is true.
  There is no time target for proofs; list any proof that takes more than about ten seconds in your report, so it can be sped up later.
  This never allows raising `maxHeartbeats`, `native_decide` or `decide +kernel`.
- Commit only when Ari asks, and add no Co-Authored-By lines.
- Keep git worktrees under `/Users/ari.biswas/Lean/`, never in `/private/tmp`, which macOS clears.

## Making proofs general

1. Before writing a second proof that looks like an earlier one, stop.
   Extract the shared part as a lemma whose varying part is a parameter, then prove both cases from it.
2. State each lemma over only what its proof uses: the bytecode only, one relation, one width.
   Do not pass the whole witness context to a bytecode fact.
3. Prove a property of a constructor or combinator once, then derive the instances.
   For example, if every expansion is built from a few combinators, show they preserve "no control row" or "no store row" rather than checking each expansion separately.
4. Split cases on a small classification proved once, such as `stable_stall_control_flow` (a stall is a JAL, a JALR or a branch), not on the whole instruction set inside each lemma.
5. Use the existing frameworks before writing new ones:
   - `StatePreservation.Preserves` and `preservation_auto` (`JoltBytecode/InstructionEquivalence/ProofSupport/Preservation.lean`) for frame properties;
   - `expand_program_layout` and `ExpansionRows` (`JoltConstraints/theorems/program_facts.lean`) for bytecode layout;
   - the Layer 1 to 4 witness lemmas under `JoltConstraints/theorems/Soundness/`.
6. Treat these as signs that a lemma is missing:
   - a proof longer than about 60 lines;
   - a blanket `cases … <;> simp_all` with `all_goals try`;
   - a block of near-identical declarations.

## Before staging a statement

Each of these has made a staged statement false before.

1. A trace row or state given on its own carries no execution certificate.
   A property of its post-state, such as whether it recorded a halt kind, says nothing about its instruction unless the lemma also has the run (`last ∈ run.rows.back?`) or an explicit execution fact.
2. Witness values are field sums that do not wrap; Sail stores 64-bit words that do.
   Comparing them needs a bound, such as `NextPCNoWrap` (`joltInstance.program.next_pc_no_wrap`), as in `theorems/Soundness/Layer5/Jal.lean`.
3. Some flags are set per row, not per source instruction.
   `stamp_sequence` sets `is_compressed` only on an expansion's last row; use `source_is_compressed` for any row.
4. A fact about "every row at an address" needs unique addresses: `pc_map_ok` with `pc_map_ok_distinct_addresses`.

## Writing

- Give every definition and public theorem a docstring that defines each term it uses and gives a concrete example.
- Cite Jolt's code by file and function or item name at the pinned commit, for example `jolt/tracer/src/emulator/cpu.rs` (`Cpu::tick`).
  Add line numbers only where they help someone find the code.
  When the pin moves, update a citation only if the cited code itself changed; do not spend work refreshing line numbers of unchanged code.
- In prose, name the actor: Jolt's tracer, prover or verifier, not "Rust".
- In Markdown files, put each sentence on its own line.

## Sources

- Jolt's Rust code: `/Users/ari.biswas/Work-with-A16z/jolt`.
  The model is pinned to the commit recorded in `methods/soundness.md` (currently `ff6fc6568`), which may not be the checked-out HEAD.
  Read pinned files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show <pin>:<path>`.
- A run stops at its first explicit halt (`jolt.success` or EBREAK), as Jolt's tracer does at `ff6fc6568` (a16z/jolt#2417 and #2451).

## Re-pinning Jolt

The theorems are proved about one Jolt commit, the pin.
`assumptions.toml` lists every premise, `sorry`, scope premise and field of `Rv64ProgramImage` the headline theorems depend on, with the Jolt functions each one cites (see `reports/2026-11-25-stale-assumptions.md`).
On every re-pin:

1. Read the open issue "Drift against Jolt main" (label `jolt-drift`).
   The nightly workflow `.github/workflows/jolt-main-drift.yml` writes it: the registry entries whose anchor files changed since the pin, the regenerated constraint data, and the state of each upstream issue.
2. Move the pin in one commit: `jolt_rev` in `assumptions.toml`, `JOLT_REV` in `.github/workflows/constraint-generation.yml`, and the pin in `methods/soundness.md`.
   `scripts/check-assumptions.py` fails when the first two differ.
3. Run `python3 scripts/check-assumptions.py --jolt-dir <Jolt checkout>`.
   It fails when an anchor's file is gone at the new pin or no longer mentions the anchor's function; update or remove that anchor.
4. For each new Jolt check, and for each entry the issue flags, ask which registry entry the check makes provable.
   A premise that Jolt now guarantees must be removed, not kept.
   Its necessity witness (`JoltConstraints/Audit/Necessity.lean`) stops building once the check is transcribed; that failure is the signal, not a proof to repair.
   Removing a premise changes a theorem statement, so it needs Ari's approval.
5. When a binder or field changes, the build of `JoltConstraints/Audit/Premises.lean` fails and prints the new list.
   Update that list and the entry's `appears_in` in `assumptions.toml` together.
6. Rerun the reproducer of each bug-report folder whose header says `status = "open"` or `"unknown"`, and update `status`, `reproduced_at` and `fixed_by`.
   An entry whose upstream issue closed needs the same check.

Anchors are compared file by file for now; function-level anchors build on #56 and come later.
