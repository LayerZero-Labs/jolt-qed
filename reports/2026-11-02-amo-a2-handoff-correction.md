AMO A2 handoff correction and build verification, 2026-11-02.

Lean revision checked: `7096dcaeb62e4a49d259b511dce76c3bc77bae5f`, with the existing uncommitted working tree and the proof fixes listed below.
Jolt source spot-checked: `c6703570588e88033b8722bd4dec47c7f46f3b16`, `crates/jolt-program/src/expand/memory/shared.rs` (`expand_amo_w` and `expand_amo_minmax_w`).
The recorded soundness pin remains `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`; this chunk checks equivalence against the generated Lean programs and does not audit their complete correspondence with that pin.

This report is written because one handoff claim differs from the files on disk.
The handoff describes `amo_word_swap_pre64_aligned_run_for` as called, but a repository-wide `rg -n 'amo_word_swap_pre64_aligned_run_for' --glob '*.lean'` finds only its declaration at `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/Amoswapw.lean:30`.
The helper is retained as explicitly requested.
No deleted helper was restored, and no helper was deleted in this chunk.

All declaration paths in the following table are relative to `JoltBytecode/InstructionEquivalence/Instructions/AtomicFamily/`.

| Declaration | File and line | Change in this chunk |
|---|---|---|
| `amo_word_sltu_sign_extend` | `WordSelectLane.lean:10` | Normalize `Int.ofNat` to natural-number casts before simplifying integer comparisons; retain the existing sign-bit case analysis and `omega` proof. |
| `amominwProgram_core_eq_sail` | `Amominw.lean:76` | Fix tactic indentation and close the remaining definitional equality with `rfl`; remove unused simp arguments. |
| `amomaxwProgram_core_eq_sail` | `Amomaxw.lean:76` | Fix tactic indentation and close the reversed comparison's definitional equality with `rfl`; remove unused simp arguments. |
| `amominuwProgram_core_eq_sail` | `Amominuw.lean:76` | Fix tactic indentation and remove the redundant `rfl` after `simp` closes the goal. |
| `amomaxuwProgram_core_eq_sail` | `Amomaxuw.lean:76` | Fix tactic indentation and remove unused simp arguments. |
| `amoswapwProgramAuto_eq_window` | `Amoswapw.lean:1192` | Remove an adjacent orphan doc comment that caused a parser error and an unused simp argument. |
| `amoswapwProgram_concrete_aligned` | `Amoswapw.lean:1206` | Attach its docstring to the declaration and include an upper-word example. |

Statement changes: none.
Added hypotheses, axioms, definitions and lemmas: none.
The nine public statement definitions and theorem signatures match both the initial working tree and Git HEAD.
The four binops still call `amo_word_binop_eq_sail`, the four selects still call `amo_word_select_eq_sail`, and swap still uses `amo_word_window_program_aligned_run` and `amo_word_program_eq_sail`.
No new window code or per-instruction execution proof was added.
No `sorry`, `native_decide`, `decide +kernel`, `bv_decide` or `maxHeartbeats` occurs in the AtomicFamily source files.

Each command below was `lake build JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.<module>`.
`pgrep -fl lake` preceded every build, and only one build ran at a time.
These are the final individual results, after fixing the intermediate failures.

| Module | Exit status | Lake jobs |
|---|---:|---:|
| `Amoaddw` | 0 | 3459 |
| `Amoandw` | 0 | 3459 |
| `Amoorw` | 0 | 3459 |
| `Amoxorw` | 0 | 3459 |
| `Amominw` | 0 | 3461 |
| `Amomaxw` | 0 | 3461 |
| `Amominuw` | 0 | 3461 |
| `Amomaxuw` | 0 | 3461 |
| `Amoswapw` | 0 | 3459 |
| `WordSelectLane` | 0 | 3458 |

A final combined build of the nine instruction modules plus `Word`, `WordLane`, `WordProgram`, `WordSelectLane` and `WordSelectRust` passed with exit status 0 and 3469 jobs.
No requested module remains failing, and no statement was found false.
No rebuilt module took more than 2.7 seconds in Lake's reported timings, so no proof exceeding ten seconds was observed.
The only build warnings were replayed warnings in `LeanRV64D.RiscvExtras` and `JoltBytecode.JoltISA.ExpansionsAutomated`.

`lake env lean /private/tmp/jolt-a2-axioms.lean` exited 0 and printed the axioms of all nine public equivalence theorems.
Each lists `plat_term_write`, `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
The source diff contains only the proof and comment changes listed above, and `git diff --check` passes for AtomicFamily.
No commit was made, and chunk A3 was not started.
