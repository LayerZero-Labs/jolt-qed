# Fix: the witness need not record the honest advice

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` first.
This is a statement fix, done before any Layer 6 work.
Change only what this file lists, build, report and stop.

Jolt's Rust code is in `/Users/ari.biswas/Work-with-A16z/jolt`.
Its working tree is now at a16z's latest main merged with Ari's own work, not at our pin, so do not read files from the working tree.
Read the pinned files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 8bbb2357:<path>`, and do not modify that checkout.

## The problem

Helper A (`soundness_reconstruct_trace`, `JoltConstraints/Soundness/TopLevel.lean:29`) and `JoltInstance.soundness_execution_prefix_agreement` (`Soundness/Layer6/ExecutionPrefix.lean:60`) are false as stated.
Both ask for one trace that uses the honest tracer's advice and whose Rs1Value and Rs2Value equal the witness's at every row (`RepresentsRows`, `ExecutionPrefix.lean:15`).

Counterexample: `rem a0, a1, zero`.
Its expansion (`remProgramAuto`, `JoltBytecode/JoltISA/ExpansionsAutomated.lean`) writes the advice `q` to register 40, then checks `q * |divisor|` does not overflow (reading register 40 as rs1), `q * |divisor| ≤ |a1|`, and that the remainder is valid.
With divisor 0 every `q` passes: Jolt's own check is `assert!(divisor == 0 || remainder < divisor)` (`tracer/src/instruction/virtual_assert_valid_unsigned_remainder.rs:25` at `8bbb2357`).
The honest tracer picks `q = 0` (`rem_advice_value`, `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/Div_math.lean:55`).
A witness may write `q = 5`; the advice row's lookup operand is free (the `Advice` flag, `JoltConstraints/metadata.lean:189`).
Then the witness's Rs1Value at the overflow-check row is 5, while every trace with honest advice has 0 there.
The result `a0 = a1` is the same either way, so Jolt is sound here; our statement is too strong.

The same holds for REMU, REMW and REMUW with a zero divisor, and for DIVUW with a zero 32-bit divisor, where the advice's upper 32 bits are free.
This is why `remProgram_sound`, `remuProgram_sound`, `remwProgram_sound`, `remuwProgram_sound` and `divuwProgram_sound` conclude only the final Sail state, while `divProgram_sound`, `divuProgram_sound` and `divwProgram_sound` conclude that the advice is honest.

The honest advice cannot be dropped instead: `soundness_stopping` takes it (`Soundness/Layer7/Stopping.lean:38`), and every restriction is stated over runs with honest advice (`UntrustedAnswerRun.NextStep`, `Soundness/Layer5/MemoryAccessRestriction.lean:29`).

## The fix

The witness represents the honest run's machine state, not its instruction temporaries.
Instruction temporaries are virtual registers 40 to 47 (`JoltISA.joltRegisterSlot`, `JoltBytecode/JoltISA/VirtualRegisters.lean:215`, class `instructionTmp`).
Every expansion writes them before reading them (`ExpansionTempLiveness.tempsReadAfterWrite`, `JoltConstraints/expansion_temp_liveness.lean:80`, checked for every source by `ExpansionFacts.expand_temps_ok`, `JoltConstraints/expansion_facts.lean:913`), and the bytecode project's equivalence theorems also ignore them (`System.systemProject`, `JoltBytecode/JoltISA/SystemProjection.lean:25`).
A witness and the honest run can differ only in temporaries written from advice, inside one division expansion.

1. Add a predicate for instruction temporaries, defined from `joltRegisterSlot` so there is one classification, with a docstring and an example (register 40 is one; register 36, `mepc`, is not).
2. In `RepresentsRows`, compare Rs1Value only when the row's rs1 register (`bytecodeRs1Register`, `JoltConstraints/Constraints/BytecodeReadSelectors.lean:12`) is not an instruction temporary, and Rs2Value likewise with `bytecodeRs2Register` (line 46).
   A row with no such operand is still compared.
   Change nothing else in `RepresentsRows`, `RepresentsPrefix`, `Represents`, A or `soundness_execution_prefix_agreement`.
   Update the `RepresentsRows` docstring with the REM example.
3. Repair every use of `RepresentsRows.rs1` and `.rs2`.
   The only one is `represented_last_control_read` (`Soundness/Layer7/StallSuffix.lean:255`, projections at lines 296-297).
   Its statement accepts any row and any source register, so as stated it would become false (the REM row 4 example makes it require 5 = 0).
   Add to it one hypothesis: the source register (`TraceWitness.sourceRegisterAddress source`) is not an instruction temporary.
   This is allowed: it is a helper's hypothesis, and all three callers can prove it.
   The callers are `stall_suffix_initial_branch` (lines 2629 and 2641, the two branch operands) and `represented_last_jalr_base` (line 2693, the JALR base).
   Prove once, as a lemma about the expanded bytecode, that no branch or JALR row reads an instruction temporary, and discharge the hypothesis at the three callers from it.
   Branches in the expanded bytecode read only x registers; a JALR's base is an x register or a virtual register (`expanded_jalr_operand_forms`, line 2457), and the only virtual bases are `trapHandlerVReg` (register 34, ECALL) and `mepcVReg` (register 36, MRET) (`JoltBytecode/JoltISA/Expansions/System.lean:79,93`); `expanded_virtual_jalr_source` (line 2317) covers the virtual-base case.
   Check each of these facts against the expansions before relying on it.
   Search the whole repository for other uses before concluding there are none.
4. Correct the documentation that claims every runtime advice value equals the honest tracer's:
   - `methods/soundness.md` lines 514, 614, 891-894 and 1288-1291.
     Line 1288 calls a non-unique advice value a soundness bug; it is not, as the REM example shows.
     Replace these with: the relaxed run uses the honest advice; in a division expansion the witness's advice may differ, the run's machine state after the expansion is still the honest one (`*Program_sound`), and `RepresentsRows` does not compare temporaries.
   - the row for `soundness_execution_prefix_agreement` under "Proofs owed" in `JoltConstraints/model_review.md`.
   Do not edit the section "Running the Layer 6 agents" in `methods/soundness.md`.

Do not prove A or the prefix theorem.
Do not add a restriction, or a premise to any theorem other than `represented_last_control_read` as step 3 describes.
If you find a consumer that needs Rs1Value or Rs2Value at a temporary, or another row where a witness can differ from the honest run outside temporaries, stop and report it.

## Before you stop

The working tree already holds uncommitted plan changes under `methods/` (deleted `methods/layer6/` files, this file, `methods/pin_update_plan.md`); leave them alone.
Build `JoltConstraints`.
Run `#print axioms JoltInstance.soundness`: `sorryAx` must come only through `soundness_execution_prefix_agreement`, helper C and helper D, as before.
Write `methods/advice_fix_report.md` with:
- each changed declaration, with file and line, and the old and new statement;
- why the new `RepresentsRows` holds for the REM witness with `q = 5` and the honest run with `q = 0`, row by row;
- the list of uses of `.rs1` and `.rs2` you searched, and how each was repaired;
- the build result and the axiom audit.

Do not commit.
Then stop.
