# Layer 6, stage 6d: the division program results

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and `methods/layer6/stage-6a-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in `DivisionAppend.lean`; do not edit it.
Edit only `Soundness/Layer6/DivisionDefs.lean`, `Soundness/Layer6/DivisionBlock.lean` and one new file `Soundness/Layer6/DivisionPrograms.lean`.

## Why

`division_block` (`DivisionBlock.lean`) is proved from five staged lemmas.
Two of them are facts about the eight generated division programs alone, with no witness: `division_program_result` (`DivisionDefs.lean`) and `division_program_honest` (`DivisionBlock.lean`).
The arithmetic is already proved in `JoltBytecode`: each `*Program_sound` and `*Program_concrete` theorem under `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/`.

## The task

Move both staged statements unchanged into `DivisionPrograms.lean`, which imports `DivisionDefs.lean` and which `DivisionBlock.lean` imports, and prove them there.

1. `division_program_result`: split on the eight kinds.
   REM, REMU, REMW, REMUW and DIVUW: their `*Program_sound` gives the final Sail state directly.
   DIV, DIVU and DIVW: their `*Program_sound` gives the advice, then their `*Program_concrete` gives a run with that advice and its final Sail state, and the two runs agree because execution is a function of its start state.
   Register presence (`present`) supplies the successful reads `rX_bits` the theorems require.
   Each case should be a few lines; if they repeat, extract the shared part as a lemma.
2. `division_program_honest`.
   - The honest advice `kind.honestAdvice rd rs1 rs2 pre` is the head of `SourceInstruction.honestTracerAdvice` (`JoltConstraints/honest_trace.lean`); check that it equals, for each kind, the advice argument of that kind's `*Program_concrete`.
     `reuse.md` says they match; this is the place to prove it.
   - `*Program_concrete` gives the honest run and its final Sail state, which equals the witness run's (`result`).
   - The other fields of `DivisionFinalAgreement` (device, tape, host settings, virtual registers that are not temporaries) hold because neither run changes them.
     Prove that once for any program whose instructions are all `DivisionArithmeticRow` kinds and write only temporaries and `rd`, with `StatePreservation.Preserves` and `preservation_auto` (`JoltBytecode/InstructionEquivalence/ProofSupport/Preservation.lean`).
     The device-setup frame `JoltIOSetupFrame` does not cover every device field.
     `division_program_honest` has no bytecode hypothesis, so take these facts from the eight programs themselves (`JoltBytecode/JoltISA/ExpansionsAutomated.lean`): each instruction is a `DivisionArithmeticRow` kind and writes only a temporary or `rd`.
     Prove them once over a program's instruction list, not once per program.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.division_block`; it should reach `sorryAx` only through the lemmas still staged after stage 6a.
Write `methods/layer6/stage-6d-report.md` with each new or moved declaration (file and line, staged or proved), any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
