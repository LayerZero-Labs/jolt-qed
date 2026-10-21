# Agent 3: tape reads, runtime advice and advice honesty

Read `README.md` in this directory first, then `AGENTS.md`, then agent 1's Phase 0 report `methods/layer6/phase0_report.md`.
Start only after Ari has approved Phase 0.
Work in a worktree under `/Users/ari.biswas/Lean/` on a branch `layer6-agent-3`, created from the commit named in the Phase 0 report.

## Your task

Prove the `RowStep` lemmas agent 1 staged for VirtualAdviceLoad (`Layer5/AdviceLoad.lean`) and VirtualAdvice (`Layer5/Advice.lean`), and the completion hook `division_advice_honest`.

## VirtualAdviceLoad

In the relaxed run a tape read returns an arbitrary 64-bit answer (`execWithTapeAnswer`, `Layer5/TapeSemantics.lean:21`).
So the step takes the run's answer to be the value the witness writes: `RdWriteValue` at that cycle, as a 64-bit word.
Show:
- the read succeeds;
- the destination now holds that value, so register agreement extends to it;
- nothing else changes, apart from the tape cursor advancing by the width.

This is why the relaxed run exists.
The witness may write 300 after a one-byte read, and the relaxed run accepts it.
Facts: `writeDst_run` (`JoltBytecode/InstructionEquivalence/ProofSupport/NativeDispatch.lean:42`), `afterWriteDst` (`Layer5/RegisterWrite.lean:15`).

## VirtualAdvice

The witness's VirtualAdvice row writes an advice value; the run records it as runtime advice.
The step itself is a register write, like shape W in the existing step lemmas (`Layer5/LookupWrite.lean:65`, `registerWrite_step`).
Its honesty is not decided at this row, because the asserts that check the advice come later in the same expansion.
So `PrefixState` exempts the rows of the instruction in progress, and honesty is proved when the expansion ends.

## `division_advice_honest`

Eight generated expansions use VirtualAdvice: `divProgramAuto`, `divuProgramAuto`, `divwProgramAuto`, `divuwProgramAuto`, `remProgramAuto`, `remuProgramAuto`, `remwProgramAuto` and `remuwProgramAuto` (`JoltBytecode/JoltISA/ExpansionsAutomated.lean`).
For each, show that if all of the expansion's assert rows pass in the witness, the advice values written equal the honest tracer's values (`honestTracerAdviceAtStepN`, `JoltConstraints/honest_trace.lean:194`), computed from the state at the start of the expansion.

This is a uniqueness argument: the asserts allow only one quotient and remainder, including the RISC-V cases of division by zero and signed overflow.
The assert step lemmas give each pass fact:
- `binaryAssertion_step` (`Layer5/AssertionsBinary.lean:111`: equality, `AssertValidDiv0`, `AssertValidUnsignedRemainder`);
- `mulAssertion_step` (`Layer5/AssertionMulOverflow.lean:70`);
- `assertLTE_step` (`Layer5/AssertLessThanEqual.lean:66`).

The bytecode project proves the forward direction for DIV, DIVU and DIVW: honest advice passes and gives the RISC-V result (`JoltBytecode/InstructionEquivalence/`).
Reuse its arithmetic, and prove the converse.
Do not add a restriction for any of this: honesty must be proved (see "Closing Layer 5b" in `methods/soundness.md`).

Generalize across the eight: they come in signed and unsigned, 64-bit and 32-bit variants of one scheme.
Prove the scheme once, parameterized by signedness and width, and instantiate it.

## Files you own

`Layer5/AdviceLoad.lean`, `Layer5/Advice.lean`, and new files under `Layer5/` whose names start with `AdviceHonesty`.

## Report

Per-declaration timings, any helper hypotheses you added, any new `bv_decide` use, and your branch's head commit.
