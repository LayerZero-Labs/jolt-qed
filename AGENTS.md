# Guidance for agents

This repository proves completeness and soundness of the Jolt zkVM in Lean.
Ari reviews the work; read this file before starting any task.

## How the work is done

The soundness proof is built top-down.
State each lemma with `sorry` first, prove its caller from it, build, and stop for Ari's review before proving the lemma itself.
Never write a bottom-up lemma that no staged statement needs.

The state of the proof lives in the repository, not in any one session:

- `methods/soundness.md`: the plan, the layers, and the current status.
- `JoltConstraints/model_review.md`, "Proofs owed": every remaining `sorry` and what it needs.

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
  List every new use in your report, and add it to the `bv_decide` list in "Proofs owed" (`JoltConstraints/model_review.md`).
- Delete every lemma no proof uses.
- Report each new declaration's elaboration time.
  Aim for about one second or less.
  A slower proof is acceptable only if it is significantly simpler than any faster one; say so in your report, with the time and why the faster version would be worse.
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
   - `expand_program_layout` and `ExpansionRows` (`JoltConstraints/program_facts.lean`) for bytecode layout;
   - the Layer 1 to 4 witness lemmas under `JoltConstraints/Soundness/`.
6. Treat these as signs that a lemma is missing:
   - a proof longer than about 60 lines;
   - an elaboration time over about one second, unless the proof is already as simple as it can be;
   - a blanket `cases … <;> simp_all` with `all_goals try`;
   - a block of near-identical declarations.

## Before staging a statement

Each of these has made a staged statement false before.

1. A trace row or state given on its own carries no execution certificate.
   A property of its post-state, such as `StableStall`, says nothing about its instruction unless the lemma also has the run (`last ∈ run.rows.back?`) or an explicit execution fact.
2. Witness values are field sums that do not wrap; Sail stores 64-bit words that do.
   Comparing them needs a bound, such as `NextPCNoWrap` (`assumptions.pcNoWrap`), as in `Soundness/Layer5/Jal.lean`.
3. Some flags are set per row, not per source instruction.
   `stamp_sequence` sets `is_compressed` only on an expansion's last row; use `source_is_compressed` for any row.
4. A fact about "every row at an address" needs unique addresses: `pc_map_ok` with `pc_map_ok_distinct_addresses`.

## Writing

- Give every definition and public theorem a docstring that defines each term it uses and gives a concrete example.
- Cite Jolt's code as `jolt/<path>:<lines>` at the pinned commit.
- In prose, name the actor: Jolt's tracer, prover or verifier, not "Rust".
- In Markdown files, put each sentence on its own line.

## Sources

- Jolt's Rust code: `/Users/ari.biswas/Work-with-A16z/jolt`.
  The model is pinned to the commit recorded in `methods/soundness.md` (currently `8bbb2357`), which may not be the checked-out HEAD.
  Read pinned files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show <pin>:<path>`.
- The stopping rule follows a16z/jolt PR #2109 (head `d2995380`) until it merges: `gh pr diff 2109 --repo a16z/jolt`.
