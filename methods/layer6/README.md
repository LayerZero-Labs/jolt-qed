# Closing Layers 5b and 6: the execution-prefix agreement

This directory is the plan for the last large piece of the soundness proof.
Each agent reads this file, then its own file (`agent-1.md` to `agent-5.md`), then `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, whose rules apply to everything.
Ari's runbook for starting the agents is the section "Running the Layer 6 agents" in `methods/soundness.md`.

## What is left

The soundness theorem `JoltInstance.soundness` is proved except for three declarations:

- `JoltInstance.soundness_execution_prefix_agreement` (`JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean:60`), the subject of this plan;
- helper C, `soundness_prover_accepts` (`Soundness/TopLevel.lean`), marked ⚠️ DANGER and assumed on purpose;
- helper D, `soundness_spoil_asserts_pass` (`Soundness/TopLevel.lean`), out of scope here.

`soundness_execution_prefix_agreement` says that the witness really is a run of the program.
From the witness it builds a relaxed run (`UntrustedAnswerRun`, `Soundness/Layer5/TapeTrace.lean`) whose rows are the witness's cycles, up to the first stable stall, the first padding cycle or the last cycle.
It must deliver, for that run:

- the same bytecode as the constraint context;
- `RepresentsPrefix` (`Layer6/ExecutionPrefix.lean:15-45`): at every retained row the witness's PC, Rs1Value, Rs2Value and RamAddress equal the run's, and at the cut the witness's RAM equals the run's final RAM at every word except the termination word, device words included;
- every retained row is real (`IsNoop = 0`), and no retained row before the last is a stable stall;
- the cut is one of the three cases above;
- every row's runtime advice is the honest tracer's (`honestTracerAdviceAtStepN`).

Its consumer is helper A (`Soundness/TopLevel.lean:29`), which is proved from it and from the proved stopping lemma.
Do not change its statement.

## What exists

- Step lemmas for 77 of the 88 row kinds, one family per file in `Soundness/Layer5/`.
  Each takes the selected bytecode row at a cycle and full `RegisterAgreement witness t pre` (`Layer5/Registers.lean:21`), and returns the run's execution and `RegisterAgreement` at the next cycle.
  LD and SD (`LoadDoubleword.lean`, `StoreDoubleword.lean`, `RamStoreAgreement.lean`) also carry `OrdinaryRamAgreement` (`Layer5/RamAgreement.lean`), and cover ordinary RAM only.
  HostIO (`HostCallRegisterFrame.lean:285`) returns agreement on every register except temporary 40.
- Two kinds are proved unreachable: VirtualROTRI and VirtualROTRIW (`Layer4/Reachable.lean:20`).
- Witness facts about single rows: Layers 1 to 4 under `Soundness/` (selection, registers, RAM, lookups), and Layer 6's `BytecodePC.lean` (entry slot, next slot inside an expansion, padding).
- Layer 7 already proved witness facts about single JAL, JALR and branch rows (lookup targets, branch decisions, link values, register frames) in `Layer7/StallSuffix.lean` and `Layer7/LastJump.lean`, and run-prefix helpers (`UntrustedAnswerRun.truncate`, `soundness_prefix_next_step`) in `Layer7/TerminationStore.lean`.
- The per-expansion checker `ExpansionFacts.sequenceOk` (`JoltConstraints/expansion_facts.lean`) and `expand_ok`, with the generic adjacent-row lift in `Layer7/AdjacentRows.lean`.

## What is missing

1. The induction itself: an invariant, its initialization, a dispatcher that routes each row to its step lemma, the source-boundary transition, and the cut.
   None of it exists in Lean yet; the prose plan is "Agreement is proved by induction on the step" in `methods/soundness.md`.
2. Register agreement over live registers.
   HostIO leaves temporary 40 disagreeing until its next write, possibly many rows later, so the full-agreement step lemmas do not compose; see "Register agreement must be over live registers" in `methods/soundness.md`.
3. Step lemmas for 9 row kinds: JALR, the six branches, VirtualAdviceLoad and VirtualAdvice.
4. Honesty of runtime advice: the eight expansions that use VirtualAdvice (DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW) must be shown to force the honest tracer's advice.
5. Device memory: RAM agreement at the input, advice, output and panic words, and LD and SD on device addresses.
6. The SC.W and SC.D expansions, so the temporary restriction `NoStoreConditional` can be removed.

## The agents

| Agent | File | Owns | Starts |
|---|---|---|---|
| 1 | `agent-1.md` | File restructuring, the interfaces, the induction, the dispatcher, the source-boundary transition, integration | First, alone |
| 2 | `agent-2.md` | JALR and the six branches | After Phase 0 is approved |
| 3 | `agent-3.md` | VirtualAdviceLoad, VirtualAdvice, advice honesty for the eight division expansions | After Phase 0 is approved |
| 4 | `agent-4.md` | Device memory, LD and SD on all addresses, SC.W and SC.D | After Phase 0 is approved |
| 5 | `agent-5.md` | Porting the existing step lemmas to live-register agreement, and their adapters to the induction's step interface | After Phase 0 is approved |

## Phases

- Phase 0, agent 1 alone: restructure files so the proof can import what it needs, and stage every interface the other agents build against, with `sorry`.
  Agent 1 then stops for Ari's review.
  This phase decides the register-agreement design and the invariant; nothing else starts before Ari approves it.
- Phase 1, agents 2 to 5 in parallel, and agent 1 on its own Phase 1 items: each proves the staged statements it owns.
- Phase 2, agent 1: merge the branches in the order its file gives, build, run the axiom audit and update the documentation.

## Working rules for all agents

- Each agent works in its own git worktree under `/Users/ari.biswas/Lean/`, on its own branch, created from the commit agent 1 names at the end of Phase 0.
  Never use `/private/tmp`.
- Edit only the files your agent file lists.
  If you need a change in a file you do not own, stop and report it; agent 1 coordinates.
- Do not change the statement of any staged interface.
  If one is false or insufficient, stop and report the exact missing fact.
- Commit on your branch when a piece builds (Ari authorizes these commits; no Co-Authored-By lines), and report the hash.
- Reuse before writing: Layers 1 to 4, `BytecodePC.lean`, and the shared Layer 7 facts agent 1 moves into `Layer6/ControlRows.lean` in Phase 0.

## Sources

- Constraints: `JoltConstraints/Constraints/`, numbered in `JoltConstraints/constraints.md`.
- The instruction set: `JoltBytecode/JoltISA/Instruction.lean:64-156`; semantics: `JoltBytecode/JoltISA/Semantics.lean`; generated expansions: `JoltBytecode/JoltISA/ExpansionsAutomated.lean`.
- Restrictions: `Soundness/Assumptions.lean` (`TemporaryRestrictions`), `Layer5/MemoryAccessRestriction.lean`, `Layer5/HostCallRestriction.lean`, `Layer5/TerminationRestriction.lean`, `Layer5/PanicRestriction.lean`.
- Jolt's Rust code: `/Users/ari.biswas/Work-with-A16z/jolt`, pinned at `8bbb2357`; read files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 8bbb2357:<path>`.
  The stopping rule follows a16z/jolt PR #2109 (`gh pr diff 2109 --repo a16z/jolt`).
- Plan and status: `methods/soundness.md`; remaining gaps: "Proofs owed" in `JoltConstraints/model_review.md`.
