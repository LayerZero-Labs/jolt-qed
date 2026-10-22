# Step (c): integration report, 2026-10-21

## Status

The approved checker integration and Parts 2–4 are implemented.
The five original stopping gaps and the approved source-membership helper are proved.
The final axiom audit confirms that `soundness_stopping` is free of `sorryAx`.
Ari authorized the final commit on `feat/soundness`, without a Co-Authored-By trailer.

`program_facts.lean` proves the approved statement:

```lean
theorem expand_program_source_of_row (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList) :
    ∃ source ∈ image.instructions.toList, ∃ rows : List JoltInstructionRow,
      expand_instruction source = some rows ∧ row ∈ rows
```

Its caller, `expanded_jalr_operand_forms`, compiles.
This statement needs no `pc_map_ok` assumption: membership in materialized bytecode already gives an emitting source.
The proof extracts the existing `mapM`/flatten traversal from `ExpansionRows.expand_program_rowOk`.
Both `expand_program_rowOk` and `expanded_jalr_operand_forms` now use this shared certificate.
The approved statement is unchanged.

## Checker integration

`sequenceOk` now conjoins `rowsOk`, `shiftsOk`, `tempsReadAfterWrite`, `jumpEndNoStore`, `sequenceJalrsVirtual`, `virtualJalrBaseUnwritten` and `advicePairsOk`.
`nativeRowOk` retains its original checks and adds `nativeJalrBaseOk` and `advicePairsOk [instruction]`.
Seven named projections expose each checker.
The new definitions are in the `rows_ok`, `pure_rows_ok` and `native_ok` simplification sets.
The narrow-advice register equality is handled once in `rows_ok`, by unpacking the single `regidx` constructor when reflexivity alone does not close the goal.
There is no new per-instruction proof table.

The five planned positional sequence consumers were replaced by projections or removed with `Emission.lean`.
The three planned native consumers now use projections.
Integration also exposed a sixth sequence consumer, `expanded_branch_source_singleton`; it now uses `sequenceOk_rowsOk`.
The list-level materialization lift `expand_instruction_checks` is proved from the strengthened `expand_ok`.
The staged `expand_additional_checks` was proved from `expand_ok` and then deleted because `expand_ok` subsumes it.
The named lemma `ExpansionFacts.circuitFlag_store_eq_opcodeFlag` proves that a row's Store circuit flag equals its instruction's Store opcode flag.
`stable_stall_source_no_store` uses this bridge explicitly.

## Bytecode and replay proofs

- `expanded_jalr_operand_forms` excludes an architectural destination with a virtual base, using the proved source certificate and the native/sequence checks.
- `expanded_virtual_jalr_source` combines the unwritten-base check with canonical register encodings to exclude a write at the base's witness register address.
- `stable_stall_source_no_store` uses the jump-end check; the branch case uses the existing native singleton fact.
- `stall_system_jalr_step` preserves the virtual base with `register_unchanged_of_no_write`, then follows the remaining-row or final-target constraint.
- `stall_suffix_initial` dispatches through `stable_stall_control_flow` to the existing JAL and branch proofs and the new JALR proof.

`expanded_same_source_rows` moved to `program_facts.lean` without changing its statement or proof.
`expanded_arch_jalr_singleton` now lives with its caller in `StallSuffix.lean` and derives its sequence case from `sequenceJalrsVirtual`.
`Emission.lean` and its duplicate expansion table were deleted.

The 124-line `stall_jalr_written_base_step` proof is now 53 lines.
Its shared register-update argument is `selected_written_jalr_base_succ`, used by both replay and initial-cycle proofs.
The nonzero architectural register-address argument is a private helper.
`selected_source_after_stable` and `represented_read_register_succ` were deleted as unused.
`stamp_sequence_instruction_member` is used by the architectural JALR singleton proof.
The duplicate branch classifier `stall_branch_shape` was removed, and its callers use `branch_instruction_of_flag`.

## Statement changes

The only original stopping-gap statement changed is `expanded_virtual_jalr_source`, as approved in the plan and staging review.
It retains its hypotheses and the no-write conclusion, and drops the unused conclusion identifying the source as ECALL or MRET.
The other four original gaps retain their statements.
The staged materialization lift retains its approved statement.
`expand_additional_checks` was removed as subsumed, as requested.
No completeness theorem statement, language definition, restriction or core execution definition changed.

## Validation and axioms

`lake build JoltBytecode JoltConstraints` passed with 8800 jobs and no errors.
`git diff --check` passed.
There are no direct `sorry`s in `expansion_facts.lean`, `program_facts.lean` or `StallSuffix.lean`.

`JoltInstance.soundness_stopping` has exactly these axioms, with no `sorryAx`:

```text
propext
sys_enable_experimental_extensions
Classical.choice
Quot.sound
JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5
```

`JoltInstance.soundness_reconstruct_trace` has the same set plus `sorryAx`.
The only direct `sorry` user reachable from reconstruction is:

```text
JoltInstance.soundness_execution_prefix_agreement
```

No direct `sorry` user is reachable from stopping.

No new `bv_decide` use was added.
The existing `JoltConstraints.branch_target_toNat` use is recorded in the `bv_decide` list under `model_review.md`'s “Proofs owed.”
No `native_decide`, `decide +kernel` or increased `maxHeartbeats` was used.

## Tape-agent note

Ari will forward the final commit hash to the tape agent; no agent message is required from this session.
The previously prepared rule note is:

> AGENTS.md changed since you started; re-read its Rules section.
> Slower proofs are acceptable if needed to make progress, per Ari's latest instruction; report their timings.
> `bv_decide` is accepted temporarily: list every new use in your report and in `model_review.md` under “Proofs owed.”
> `native_decide`, `decide +kernel` and raising `maxHeartbeats` remain banned.

## Declaration timings

Measurements use `#time` on temporary copies, with `Elab.async=false` and one Lean worker.
Module elaboration totals sum the timed declarations, excluding imports and startup.
Whole-process times include imports and startup.
These are individual measurements, not performance guarantees.
The tables below include every added or changed declaration and every per-program checker proof affected by the stronger definitions.
After the final review, the source-membership proof measured 31 ms and its refactored row-validity caller measured 2 ms.


| `expansion_facts.lean` | Before staging | Separate checks staged | Integrated |
|---|---:|---:|---:|
| Total declaration elaboration | 11.375 s | 11.732 s | 44.287 s |
| Whole Lean process | 16.73 s | 17.53 s | 49.983 s |

The three checker proofs above about one second are `slli_ok` (1.739 s), `csrrw_ok` (4.481 s) and `csrrs_ok` (7.728 s).
Their proofs retain the existing shared-macro approach.
An attempted extra simplification of option defaults and Boolean conjunctions made CSRRS take 159.508 s; that change was reverted.
No faster proved variant of the final shared-macro proofs was established.
The straightforward versions are retained under Ari's explicit instruction that slow proofs are acceptable to make progress.
The 11 s to 44 s regression is recorded as deferred cleanup under “Proofs owed” in `model_review.md`, as requested.
Every added or changed stopping proof measured below one second, including the JALR initial-cycle proof at 853 ms.
Zero milliseconds in the tables means the measured command completed below the timer's millisecond resolution.

### Added or changed declarations

#### `expansion_facts.lean`

| Declaration | Elaboration (ms) |
|---|---:|
| `jumpEndNoStore` | 10 |
| `sequenceJalrsVirtual` | 10 |
| `virtualJalrBaseUnwritten` | 3 |
| `advicePairsOk` | 28 |
| `nativeJalrBaseOk` | 1 |
| `sequenceOk` | 2 |
| `sequenceOk_rowsOk` | 5 |
| `sequenceOk_shiftsOk` | 2 |
| `sequenceOk_tempsReadAfterWrite` | 2 |
| `sequenceOk_jumpEndNoStore` | 2 |
| `sequenceOk_sequenceJalrsVirtual` | 2 |
| `sequenceOk_virtualJalrBaseUnwritten` | 1 |
| `sequenceOk_advicePairsOk` | 1 |
| `rows_ok` | 60 |
| `pure_rows_ok` | 53 |
| `nativeRowOk` | 3 |
| `nativeRowOk_x0Ok` | 4 |
| `nativeRowOk_canonical` | 2 |
| `nativeRowOk_immShiftOk` | 2 |
| `nativeRowOk_not_registerShift` | 2 |
| `nativeRowOk_tempsReadAfterWrite` | 1 |
| `nativeRowOk_nativeJalrBaseOk` | 2 |
| `nativeRowOk_advicePairsOk` | 2 |
| `native_ok` | 44 |
| `expand_temps_ok` | 2 |
| `circuitFlag_store_eq_opcodeFlag` | 1 |
| `expand_instruction_checks` | 22 |

#### `Soundness/Layer7/StallSuffix.lean`

| Declaration | Elaboration (ms) |
|---|---:|
| `stall_branch_control_flags` | 148 |
| `expanded_branch_source_singleton` | 46 |
| `stall_branch_runs` | 356 |
| `stall_branch_model_target` | 769 |
| `stall_branch_replay_target` | 260 |
| `stall_branch_step` | 356 |
| `expanded_arch_jalr_singleton` | 13 |
| `xreg_address_ne_zero_of_notX0` | 21 |
| `selected_written_jalr_base_succ` | 558 |
| `stall_jalr_written_base_step` | 313 |
| `expanded_virtual_jalr_source` | 24 |
| `stall_system_jalr_step` | 568 |
| `expanded_jalr_operand_forms` | 15 |
| `stall_suffix_initial_jalr` | 853 |
| `stall_suffix_initial` | 8 |
| `stable_stall_source_no_store` | 279 |
| `stamp_sequence_instruction_member` | 8 |

#### `program_facts.lean`

| Declaration | Elaboration (ms) |
|---|---:|
| `expand_program_source_of_row` | 31 |
| `expanded_same_source_rows` | 30 |

#### `trace_interface.lean`

| Declaration | Elaboration (ms) |
|---|---:|
| `stamp_sequence_rowOk` | 30 |
| `expand_instruction_rowOk` | 14 |
| `expand_program_rowOk` | 2 |
| `expand_instruction_shiftPairs` | 12 |

#### `Soundness/Layer5/HostCallExpansion.lean`

| Declaration | Elaboration (ms) |
|---|---:|
| `host_not_in_sequence` | 1 |

### Per-program checker proofs and shared constructors

The source text of most per-program lemmas is unchanged; their conclusions are stronger because `sequenceOk` and `nativeRowOk` are stronger.
The table also includes the shared `ofProgram_ok`, `ofPureProgram_ok` and `expand_ok` proofs.
Both columns use synchronous declaration timings.

| Declaration | Before (ms) | Integrated (ms) |
|---|---:|---:|
| `slli_ok` | 1033 | 1739 |
| `srli_ok` | 14 | 222 |
| `srai_ok` | 13 | 219 |
| `sll_ok` | 28 | 234 |
| `srl_ok` | 28 | 235 |
| `sra_ok` | 28 | 233 |
| `slliw_ok` | 14 | 221 |
| `srliw_ok` | 13 | 224 |
| `sraiw_ok` | 13 | 227 |
| `sllw_ok` | 28 | 228 |
| `srlw_ok` | 29 | 233 |
| `sraw_ok` | 28 | 236 |
| `mulh_ok` | 58 | 262 |
| `mulhsu_ok` | 66 | 283 |
| `div_ok` | 76 | 293 |
| `divu_ok` | 62 | 279 |
| `rem_ok` | 59 | 271 |
| `remu_ok` | 58 | 265 |
| `divw_ok` | 78 | 288 |
| `divuw_ok` | 66 | 281 |
| `remw_ok` | 67 | 278 |
| `remuw_ok` | 58 | 265 |
| `lb_ok` | 74 | 476 |
| `lh_ok` | 92 | 487 |
| `lw_ok` | 91 | 488 |
| `lbu_ok` | 74 | 512 |
| `lhu_ok` | 93 | 571 |
| `lwu_ok` | 93 | 534 |
| `sb_ok` | 52 | 285 |
| `sh_ok` | 61 | 295 |
| `sw_ok` | 61 | 303 |
| `amoswapw_ok` | 184 | 677 |
| `amoaddw_ok` | 188 | 708 |
| `amoxorw_ok` | 191 | 698 |
| `amoandw_ok` | 188 | 656 |
| `amoorw_ok` | 189 | 652 |
| `amominw_ok` | 220 | 694 |
| `amomaxw_ok` | 222 | 695 |
| `amominuw_ok` | 219 | 704 |
| `amomaxuw_ok` | 220 | 704 |
| `amoswapd_ok` | 64 | 479 |
| `amoaddd_ok` | 78 | 495 |
| `amoxord_ok` | 79 | 491 |
| `amoandd_ok` | 77 | 492 |
| `amoord_ok` | 77 | 491 |
| `amomind_ok` | 103 | 527 |
| `amomaxd_ok` | 104 | 521 |
| `amominud_ok` | 103 | 527 |
| `amomaxud_ok` | 105 | 533 |
| `lrw_ok` | 120 | 588 |
| `lrd_ok` | 83 | 588 |
| `scw_ok` | 239 | 825 |
| `scd_ok` | 141 | 669 |
| `advicelb_ok` | 47 | 599 |
| `advicelh_ok` | 48 | 631 |
| `advicelw_ok` | 48 | 627 |
| `adviceld_ok` | 27 | 542 |
| `ecall_ok` | 46 | 314 |
| `ebreak_ok` | 14 | 251 |
| `mret_ok` | 16 | 266 |
| `csrrw_ok` | 442 | 4481 |
| `csrrs_ok` | 700 | 7728 |
| `lui_native_ok` | 227 | 231 |
| `auipc_native_ok` | 138 | 142 |
| `jal_native_ok` | 33 | 28 |
| `jalr_native_ok` | 32 | 29 |
| `beq_native_ok` | 15 | 16 |
| `bne_native_ok` | 16 | 16 |
| `blt_native_ok` | 16 | 16 |
| `bge_native_ok` | 16 | 17 |
| `bltu_native_ok` | 15 | 18 |
| `bgeu_native_ok` | 15 | 16 |
| `addi_native_ok` | 136 | 146 |
| `slti_native_ok` | 138 | 145 |
| `sltiu_native_ok` | 138 | 142 |
| `xori_native_ok` | 137 | 142 |
| `ori_native_ok` | 138 | 144 |
| `andi_native_ok` | 138 | 144 |
| `addiw_native_ok` | 137 | 142 |
| `add_native_ok` | 137 | 143 |
| `sub_native_ok` | 137 | 142 |
| `slt_native_ok` | 137 | 143 |
| `sltu_native_ok` | 136 | 143 |
| `xor_native_ok` | 138 | 142 |
| `or_native_ok` | 136 | 144 |
| `and_native_ok` | 137 | 142 |
| `andn_native_ok` | 136 | 142 |
| `addw_native_ok` | 136 | 143 |
| `subw_native_ok` | 137 | 144 |
| `mul_native_ok` | 136 | 142 |
| `mulhu_native_ok` | 136 | 143 |
| `mulw_native_ok` | 138 | 143 |
| `fence_native_ok` | 10 | 11 |
| `ld_native_ok` | 32 | 29 |
| `sd_native_ok` | 14 | 15 |
| `virtualRev8W_native_ok` | 135 | 141 |
| `virtualAssertEQ_native_ok` | 14 | 14 |
| `virtualHostIO_native_ok` | 32 | 30 |
| `ofProgram_ok` | 0 | 1 |
| `ofPureProgram_ok` | 9 | 9 |
| `expand_ok` | 223 | 231 |
