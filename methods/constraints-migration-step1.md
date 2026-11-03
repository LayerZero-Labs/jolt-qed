# Constraints migration, step 1: definitions

Ari approved this list on 2026-11-02.
Each approval holds only if the change matches Jolt's code at `c6703570`.
Check every change against the cited Rust, and stop if one does not match.
Delete this file once the step is reviewed and its content is in the code and in `JoltConstraints/constraints.md`.

## Context

- Jolt pin: `5def437f`.
  Migration target: `c6703570`, in `/Users/ari.biswas/Work-with-A16z/jolt`; read files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.
- Lean base commit: `5a48604`.
  JoltBytecode is already migrated and builds.
- Retired rows: `VirtualAlignAddr`, `VirtualAssertHalfwordAlignment`, `VirtualAssertWordAlignment`.
- New rows, declared in `JoltBytecode/JoltISA/Instruction.lean`: `VirtualLoadB/H/W (faultClass dst base imm fault)` and `VirtualStoreB/H/W (base value imm fault)`.
  `VirtualShiftDataB/H/W` gained an immediate: `(dst value address imm)`.
- Below, `ea` is `JoltISA.sourceValue base preState + imm`, wrapping at 64 bits.
  `mask` is 7, 6 and 4 for B, H and W.

## Approved changes

1. Flag set.
   In `InstructionFlags` (`JoltConstraints/witness.lean:21`), append `RightOperandIsRdWriteValue` after `IsNoop`.
   Rust: `crates/jolt-riscv/src/flags.rs` (`InstructionFlags`).
2. Constraint (01).
   Rename `ramAddrEqRs1PlusImmIfLoadStore` to `ramAddrEqRs1PlusImmMinusLookupIfLoadStore`, rename its file to match, and update `Constraints/All.lean`.
   New body: `(Load t + Store t) * (RamAddress t - Rs1Value t - Imm t + LookupOutput t) = 0`.
   Rust: row 0 in `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`.
3. Honest RAM address.
   In `TraceWitness.ramAccessAddress` (`JoltConstraints/witness_helpers/ram_address.lean`), LD and SD give `ea`, and the new loads and stores give `ea - (ea &&& mask)`.
   Rust: `tracer/src/instruction/floor_access.rs` (`addresses`) and `crates/jolt-witness/src/witnesses/ram.rs` (`ram_access_address`).
4. Recorded RAM address.
   `TraceRow.ram_address` (`JoltConstraints/trace.lean:50`) gets the same cases, as a `Nat`.
   Rust: `crates/jolt-riscv/src/trace_row.rs` (`ram_address`) and `crates/jolt-program/src/execution/trace.rs` (`ExecutionDimensions::from_rows`).
   The text of `InLanguage` does not change.
5. Constraint (33).
   In `rightInstructionInputEqSelection` (`Constraints/RightInstructionInputEqSelection.lean`), add `InstructionFlags .RightOperandIsRdWriteValue t * RdWriteValue t`.
   Rust: `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs`.
   Constraint (11) does not change; do not add the term to it.
6. Honest right input.
   In `TraceWitness.RightInstructionInput` (`witness_helpers/right_instruction_input.lean`), replace the if/else with the sum of three flag-guarded terms: `Rs2Value`, `Imm` and `RdWriteValue`.
   Rust: `to_instruction_inputs` in `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs` and `instructions/riscv/ld.rs`.
7. Immediate.
   In `JoltMetadata.immediate` (`JoltConstraints/metadata.lean:13`), the new loads, the new stores and ShiftData join LD and SD with `imm.toInt`.
   ShiftData leaves the `=> 0` group, and the retired rows are dropped.
   Rust: `crates/jolt-program/src/expand/memory/shared.rs` (`open`, `merge`) passes the signed `i128` offset; the formats are `FormatLoad`, `FormatS` and `FormatShiftData` in `tracer/src/instruction/format/`.
8. Lookup tables.
   In `LookupTableKind` (`witness.lean`), remove `HalfwordAlignment`, `WordAlignment` and `AlignAddr`, and append `AddressOffsetB`, `AddressOffsetH`, `AddressOffsetW` after `VirtualXORROTL1`.
   Rust: `crates/jolt-lookup-tables/src/tables/mod.rs`; the 55 names must match in order.
9. Table entries.
   In `JoltConstraints/lookup_table.lean`, delete `alignAddrTableEntry`, `halfwordAlignmentTableEntry`, `wordAlignmentTableEntry` and their arms in `lookupTableEntry`.
   Add one entry, `addressOffsetTableEntry (width : Nat) (address : Fin (2 ^ 128))`, equal to `((BitVec.ofFin address &&& BitVec.ofNat 128 (8 - width)).toNat : F)`, with arms B → 1, H → 2, W → 4.
   Rust: `tables/address_offset.rs` (`materialize_entry`).
10. Instruction flags, `JoltMetadata.instructionFlag` (`metadata.lean:49`).
    `RightOperandIsImm`: drop the retired rows; add the new loads, the new stores and ShiftData.
    `LeftOperandIsRs1Value`: drop the retired rows; add the new loads and stores.
    New arm `RightOperandIsRdWriteValue`: LD only.
    Rust: `crates/jolt-riscv/src/instructions/virt/{load,store,shift_data}_{b,h,w}.rs` and `instructions/i/ld.rs`.
11. Circuit flags, `JoltMetadata.opcodeFlag` (`metadata.lean:121`).
    `AddOperands`: drop the retired rows; add the new loads and stores.
    `Load`: LD and the new loads.
    `Store`: SD and the new stores.
    `WriteLookupOutputToRD`: drop `VirtualAlignAddr`.
    `Assert`: drop the two alignment asserts.
    Rust: the same files as change 10.
12. Table map, `JoltMetadata.lookupTable` (`metadata.lean:227`).
    Drop the retired rows; map the new B, H and W loads and stores to `AddressOffsetB`, `AddressOffsetH` and `AddressOffsetW`.
    LD and SD stay `none`, and ShiftData does not change.
    Rust: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs` and `instructions/riscv/ld.rs`.
13. Honest lookup index, `instructionLookupIndex` (`witness_helpers/lookup_index.lean:25`).
    ShiftData: `interleaveLookupOperands (source value) (source address + imm)`.
    New loads and stores: `BitVec.ofInt 128 ((source base).toNat + imm.toInt)`.
    LD: `interleaveLookupOperands 0 (capturedDestinationValue dst postState)`.
    SD, FENCE and HostIO stay 0; the retired rows are dropped.
    Rust: the `LookupQuery` defaults in `crates/jolt-lookup-tables/src/traits.rs`, `instructions/virt/floor_access.rs`, `instructions/riscv/ld.rs` and `instructions/riscv/sd.rs`.
14. Honest lookup output, `rowLookupOutput` (`witness_helpers/lookup_output.lean:15`).
    ShiftData: `jolt_virtual_shift_data_{b,h,w}_value (source value) (source address + imm)`.
    New loads and stores: `(source base + imm) &&& mask`.
    LD and SD stay 0; the retired rows are dropped.
    Rust: `to_lookup_output` in `instructions/virt/shift_data_b.rs` and `instructions/virt/floor_access.rs`.
15. Honest right lookup operand, `TraceWitness.RightLookupOperand` (`witness_helpers/right_lookup_operand.lean:11`).
    The branch for rows without combined operands uses the right input wrapped to 64 bits.
    Rust: the `to_lookup_operands` default in `traits.rs`, `(y as u64) as u128`, read by `crates/jolt-witness/src/witnesses/operands.rs` (`RightLookupOperand`).
16. Register check, `instructionIsCanonical` (`JoltConstraints/register_encoding.lean:43`).
    The new loads join the one-source, one-destination group (`dst`, `base`).
    The new stores join the two-source, no-destination group (`base`, `value`).
    The ShiftData patterns gain one `_`, and the retired rows are dropped.
    Rust: `FormatLoad`, `FormatS` and `FormatShiftData` in `tracer/src/instruction/format/`.
17. Register selectors.
    In `witness_helpers/` files `rs1_value`, `rs1_ra`, `rs2_value`, `rs2_ra`, `rd_value` and `rd_wa`, in `Constraints/BytecodeReadSelectors.lean`, and in `JoltConstraints/expansion_temp_liveness.lean`:
    the new loads join LD (rs1 `base`, rd `dst`, no rs2);
    the new stores join SD (rs1 `base`, rs2 `value`, no rd);
    the ShiftData patterns gain one `_`;
    the retired rows are dropped.
    Rust: `RegisterStateLoad` in `tracer/src/instruction/virtual_load_*.rs` and `RegisterStateS` in `virtual_store_*.rs`, the same as `ld.rs` and `sd.rs`.
18. RAM values.
    In `TraceWitness.RamWriteValue` (`witness_helpers/ram_write_value.lean:25`) and `HonestWitness.RamReadValue` (`honest_witness_helpers/ram_read_value.lean:29`), the new loads join LD and the new stores join SD.
    For a store, `RamReadValue` reads the old word at the accessed address: `ea` for SD and `ea &&& ~~~7` for the new stores.
    Rust: `tracer/src/instruction/floor_access.rs` (`store`, which calls `store_doubleword` on `ea & !7`).
    Widen `HonestTrace.store_word_present` (`JoltConstraints/memory_presence.lean:497`) into one theorem covering SD and the new stores, from the same premises.
    Do not copy the proof for each case.
19. Classifier helpers (`metadata.lean:215`, `:220`).
    Replace `opcodeFlag_load_requiresLD` and `opcodeFlag_store_requiresSD` with `opcodeFlag_load_cases` and `opcodeFlag_store_cases`.
    Each keeps its hypothesis; the conclusion becomes "LD or one of the new loads" (respectively "SD or one of the new stores").
    Their seven call sites are in proofs (`JoltConstraints/model_review.md`, "Classifier call sites"); leave them for the proof step and list them in the report.

20. Proof repairs on the build path (approved by Ari on 2026-11-02).
    `TraceRow.ram_address_lt` (`JoltConstraints/witness_params.lean:41`) gets a case for the new loads and stores; its statement does not change.
    `JoltNextPCFrame.instruction` (`JoltConstraints/nextpc_frame.lean`) handles the new rows the way `load_instruction` and `store_instruction` handle LD and SD: one lemma for the new loads and one for the new stores, each covering all three widths.
    Its statement does not change; `ordinary_instruction` may exclude the new rows, since `instruction` handles them.

Constraints (46) and (47) need no edit: (47) ranges over every instruction flag, and (46)'s circuit flags are unchanged.

## Out of scope

- Outline items 6, 8, 10 and 11 of `JoltConstraints/constraints.md`, except as listed above.
- Proofs under `Soundness/` and `Completeness/`.
- `InLanguage`, the assumption bundles, the restrictions and `TracerAddressChecks`.
- JoltBytecode.

## Rules

`AGENTS.md` applies.
In addition:

- No `sorry`, `native_decide`, `decide +kernel` or `bv_decide`, and never raise `maxHeartbeats`.
- No new premise on any theorem.
  Ari approves changes to any helper whose callers can derive it from their current premises.
- Do not commit.
- Give every new or changed definition a docstring that defines its terms and gives a concrete example.
- Cite `c6703570` code by file and item name.

## Approved without asking

Ari has approved, in advance, any proof repair or helper change that a module in the build list needs, when both of these hold:

- the statement of every completeness and soundness theorem, `InLanguage`, the assumptions and the restrictions stay as they are;
- every caller of a changed helper can still prove it from the premises it already has.

Make such changes without stopping, and list each one in the report.

## Stop and report to Ari

- A change on this list does not match the Rust.
- A needed change is outside this list and outside "Approved without asking", for example a change to a model definition, or a new premise.
- A rule in "When stuck, discuss first" of `AGENTS.md` applies.

## Build

Check for a running Lake process (`pgrep -fl lake`), then build serially.
These modules must build: `JoltConstraints.witness`, `JoltConstraints.lookup_table`, `JoltConstraints.metadata`, `JoltConstraints.register_encoding`, `JoltConstraints.trace`, `JoltConstraints.witness_helpers`, `JoltConstraints.Constraints.All`, `JoltConstraints.honest_witness`, `JoltConstraints.memory_presence`, `JoltConstraints.expansion_temp_liveness`.
Then run `lake build JoltConstraints` once, and record every failing module with its first error.
Do not fix those.

## Deliverables

1. The diff, uncommitted.
2. In `JoltConstraints/constraints.md`, update equations (01) and (33), and mark the finished outline items.
3. A report, `reports/YYYY-MM-DD-constraints-migration-definitions.md`, giving:
   - the date, the Jolt commits (`5def437f`, `c6703570`) and the Lean base commit `5a48604`;
   - for each change above, every declaration changed or removed, with file and line, and the Rust it follows;
   - every statement change;
   - the build commands and their results;
   - each failing module from the full build, with its first error;
   - any mismatch found between this list and the Rust.

Then stop for review.
