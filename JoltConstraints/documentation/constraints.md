# Jolt constraints

Source: the base RV64 relations at [the Rust pin `ff6fc6568`](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs), the merge of a16z/jolt#2509. GitHub links are documentation pointers; reviews of current behavior must scan the local Jolt checkout.
On 2026-10-29 all 62 base equations, the per-instruction flag tables and the 55 lookup tables were rechecked against Jolt's base verifier at the previous pin `5def437f` and match (`reports/2026-10-29-soundness-statement-audit.md`).

Steps 1 to 5 of the migration to `c6703570` were reviewed and committed in #34.
Step 2 repairs target `c6703570`; see [the completeness migration report](../../reports/2026-11-03-constraints-migration-completeness.md).
`lake build JoltConstraints.theorems.Completeness` and the assembled `theorems.Completeness.completeness` module both pass after the approved `WordEntry` repair.
Step 5 restates `JoltInstance.completeness` for the honest witness at the sizes Jolt's prover picks; see [the Step 5 report](../../reports/2026-11-03-completeness-jolt-prover.md).
At those sizes the verifier's RAM bounds are proved.
The RAM sizes follow the fix that #1951 item 4 proposes, which [a16z/jolt#2250](https://github.com/a16z/jolt/pull/2250) made in Jolt at the earlier pin `c97e9300`, and `HonestTrace.prover_config_holds_highest_slot` is proved.
Step 4 migrated the soundness proof; `JoltInstance.soundness` is proved with no `sorry`.
A `DONE` label records the individual theorem's proof status, not completion of the [migration outline](#migration-outline).

A checked box means the stated honest-witness theorem is proved in Lean without `sorryAx` under its stated premises.
The labels are `DONE:` for a checked proof, `TODO:` for unfinished proof or correspondence work, and `FIXME:` for a confirmed issue.
The original 62 base targets were checked by source inspection and `#print axioms`.
The review rechecked the assembled theorem's axioms against the target and confirmed its recorded `sorryAx` dependency.
The current checklist has 63 targets, all checked, including Akita's (63) added on 2026-11-10; the last three, (01), (08) and (11), were checked on 2026-11-25 with a fresh `#print axioms JoltInstance.completeness`.
The `ff6fc6568` re-pin retired (22), (57) and (62) and added (64), (65) and (66); the numbers of retired targets are not reused.

Each checklist item links to its constraint definition and matching completeness
module. [AllConstraints](../translation/Constraints/All.lean) bundles the 63 relations, and
[honestWitness_constraintEquations](../theorems/Completeness/All.lean) assembles their proofs
under the stated conditions.

The address-wrap issue [a16z/jolt#1949](https://github.com/a16z/jolt/issues/1949) used to block (01), (08) and (11); since 2026-11-25 all three are proved, because no honest memory row wraps its address.
At `ff6fc6568` Jolt has no termination word, and the re-pin proved (37) and (38) without changing their statements.
The checked boxes for (37), (38), (64), (65) and (66) rested on the successful build and a source search that found `sorry` only in the modules for (01), (08) and (11), not on a fresh `#print axioms`.
Constraint (16)'s theorem assumes the trace's last row is a jump, which Jolt's prover requires; without it, a [taken self-branch](../../bug-report/self-branch.md) as the last row is a counterexample.
Its checked box rests on a source search for `sorry`, not a fresh `#print axioms`.
Constraint (39), including the complete AddressOffset dispatch, now builds against the target and its fresh axiom check contains no `sorryAx`.

Constraint (12) has a proved conditional completeness theorem requiring
equality-assertion operands to match;
Rust's intentionally unsatisfiable spoil execution makes the unrestricted claim
false. Constraint (13) has a proved theorem for valid Lean trace rows; the
historical Rust counterexample was fixed in Jolt, as recorded in the
[CSRRS report](../../bug-report/issue.md). `expand_program_rows_valid` derives
Lean's program-row validity certificate from `SourceInstruction.expand`. Constraint (15)
has a proved honest-witness theorem for padded traces; its proof has no
`sorryAx` dependency. Some other targets need additional program/trace
validity conditions.
The completeness theorem for constraint (64) takes the padded trace length that Jolt's prover picks
(`WitnessParams.ProverPaddedFor`); the halt may fill the final witness row. The completeness theorem for (58) requires
at least one RAM chunk. The register targets (34)–(36) and (42) require zero
initial registers. Constraint (26) needs no advice premise: its public array
holds only input and output words.

Equations (43)–(47) were rechecked against public Rust pin `8bbb2357`. Their honest-witness targets now require the exact Rust bytecode domain, including the leading no-op and power-of-two padding.

The remaining equations (23)–(26), (37)–(38), (40)–(41), (48)–(53), and (59)
were also checked against public Rust pin `8bbb2357`.
This checklist covers the base RV64 relations and the `akita` build's
instruction-address canonicality condition (63). The `akita` build's other
changes (fused increments, digit-zero hamming weights, advice openings) only
re-encode or add constraints, so the model does not need them for soundness.
Constraint (53) takes the public entry slot
explicitly and requires the trace to start there. Constraint (50) selects the
destination recorded in the final bytecode row, including x0. The
[`JoltTraceRow` load-capture condition](../translation/trace.lean) separately requires a load's
captured RAM value to equal its captured destination value; it rejects a raw
`LD x0` of a nonzero word without rewriting that destination.

A checked box above only excludes `sorryAx` from that particular target.

The current model audit and changes to previously accepted definitions are recorded in
[model_review.md](model_review.md). Matching constraint equations does not
certify every current completeness statement.

## Migration outline

This outline is historical: it covers the move from the pin `5def437f` to the migration target `c6703570`.
The `ff6fc6568` re-pin later removed the `TracerAddressChecks` premise of item 10 and every other temporary restriction.
All steps are committed and `lake build JoltConstraints` passes.
The target's facts below were read from `git show c6703570:<path>` in the local Jolt checkout, which is `origin/main` of the fork `abiswas3/jolt`.

Current definition state after Step 1:

- `InstructionFlags` has seven constructors; the 55 lookup-table names match the target in order.
- Metadata, register selectors and trace witness helpers use floor rows and the ShiftData immediate.
- `witness`, `lookup_table`, `metadata`, `register_encoding`, `trace`, `witness_helpers`, `Constraints.All`, `honest_witness`, `memory_presence` and `expansion_temp_liveness` build.
- One shared store-presence proof covers SD and all floor stores; next-PC framing and the recorded-address bound cover the new rows without changing their main statements.
- The Step 1 review repaired the renamed (01) import and recorded all 17 full-build failures in its report.
- Step 2 repairs the affected completeness proofs and records the remaining full-build failures in its own report.

1. **Flag set — implemented and built; Step 1 reviewed.**
   Append `RightOperandIsRdWriteValue` after `IsNoop` in `InstructionFlags` (`translation/witness.lean:26`), matching `crates/jolt-riscv/src/flags.rs` (`InstructionFlags`).
   The target and Lean type both have seven instruction flags.
2. **RAM-address equation, Jolt R1CS row 0, Lean (01) — definition implemented and built.**
   Renamed the definition and its `translation/Constraints/All.lean` field to `ramAddrEqRs1PlusImmMinusLookupIfLoadStore`, with the matching module name.
   The matching completeness theorem, module, import and assembly field now use the new name; its #1949 gap was proved on 2026-11-25.
   Its target right side is `Rs1Value + Imm - LookupOutput`, from the row's comment in `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`.
3. **Right-input routing, (33) and (11) — definitions and proofs migrated.**
   Add the summand `RightOperandIsRdWriteValue * RdWriteValue` to (33), as in `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs`.
   (33) builds; (11) builds from the explicit ShiftData address-wrap obligation approved on 2026-11-03.
   Do not add the term again to (11) as a separate term, or it counts twice.
4. **Bytecode flag reads, (46) and (47) — definition domain and metadata implemented and built.**
   The instruction-flag domain and metadata now include the new flag.
   `translation/Constraints/BytecodeReadData.lean` and (47) already range over the whole flag type; (46) uses the unchanged circuit-flag type, so neither definition needed an edit.
   Their existing proofs build with the enlarged flag type.
   `RightOperandIsRdWriteValue` belongs to (47), not to (46)'s circuit flags.
   In the target's stage-3 combination it has gamma power 7, with `VirtualInstruction` and `IsFirstInSequence` at powers 8 and 9.
5. **Lookup tables — implemented and built; Step 1 reviewed.**
   Replace `AlignAddr`, `HalfwordAlignment` and `WordAlignment` in `witness.lean` and `lookup_table.lean` with `AddressOffsetB`, `AddressOffsetH` and `AddressOffsetW`.
   Match `crates/jolt-lookup-tables/src/tables/mod.rs` and `address_offset.rs`.
   The target has 55 tables; the three new ones are at zero-based indices 52, 53 and 54.
6. **Lookup-entry theorems — migrated and built.**
   Retired `lookupEntryCorrect_AlignAddr`, `lookupEntryCorrect_HalfwordAlignment` and `lookupEntryCorrect_WordAlignment` and their unused alignment helpers.
   `addressOffset_entry` proves the width-parametric mask equation without new premises or `sorry`.
   `lookupEntryCorrect_AddressOffsetB/H/W` instantiate widths 1, 2 and 4.
   The complete dispatch and (39) build after removal of the retired `alignAddr_entry` theorem from `theorems/Soundness/Layer4/WordEntry.lean`, approved for Step 2.
7. **Metadata and row observations — implemented and built; Step 1 reviewed.**
   Give LD `RightOperandIsRdWriteValue` (`crates/jolt-riscv/src/instructions/i/ld.rs`).
   Give floor loads `[Load, AddOperands]` and floor stores `[Store, AddOperands]`, each with `[LeftOperandIsRs1Value, RightOperandIsImm]` and the width's AddressOffset table (`instructions/virt/{load,store}_{b,h,w}.rs`).
   Give `VirtualShiftDataB/H/W` `RightOperandIsImm` alongside their existing `LeftOperandIsRs1Value` and `RightOperandIsRs2Value`, and normalize their immediate.
   Remove the retired row cases.
   Check `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs` for the table assignments.
   Operand encodings, trace witness helpers, `TraceRow.ram_address` and temporary-source liveness now describe the new memory rows and build.
   `HonestWitness.RamReadValue` reads old store words at the accessed address, and the generalized store-presence proof builds from the existing honest-trace premises.
8. **Address helper uses — migrated.**
   Replace the four constraint-side uses of `jolt_virtual_align_addr_value64` with reasoning about AddressOffset and the floor rows.
   No use of `jolt_virtual_align_addr_value64` remains in `JoltConstraints`.
   `translation/witness_helpers/lookup_output.lean` now returns each floor row's offset.
   Do not replace an aligned address by an offset without checking the equation that consumes it.
9. **Classifier theorems — migrated.**
   Replaced `opcodeFlag_load_requiresLD` and `opcodeFlag_store_requiresSD` with `opcodeFlag_load_cases` and `opcodeFlag_store_cases`, covering floor constructors with unchanged hypotheses.
   Both load proofs use `MemoryValueFacts`; the store proof uses `opcodeFlag_store_cases`.
   Step 4 migrated the soundness callers; see [model_review.md](model_review.md#classifier-call-sites).
10. **Tracer address checks: approved temporary premise, added in the migration and removed at the `ff6fc6568` re-pin.**
    Ari approved on 2026-11-02 extending `TracerAddressChecks` to floor-row accesses as a temporary premise, added only to fit the new ISA; temporary premises are removed eventually, so that fit is acceptable.
    `theorems/Soundness/Layer5/MemoryAccessRestriction.lean` now checks LD, SD and the floor loads and stores.
    The predicate for a floor row follows `tracer/src/instruction/floor_access.rs` (`addresses`, lines 59–75 at `c6703570`).
    There, the recorded address is `ea - (ea & offset_mask)`, which the tracer asserts is a multiple of 8, outside its test-only misaligned mode.
    The accessed doubleword is `ea & !7`.
    Check the doubleword rules in `Mmu.load_doubleword` and `Mmu.store_doubleword` before writing the predicate.
    The premise must carry the FIXME comment described in [soundness.md](../../methods/soundness.md), Layer 5b, and be narrowed or removed as each case is resolved.
    Confirm the intended extension against `tracer/src/instruction/floor_access.rs` and the doubleword MMU checks before changing this restriction.
    For a floor row, distinguish the effective address, the recorded RAM address, the containing doubleword address and the alignment condition.
11. **Soundness and completeness proof repair.**
    Keep the main statements, `InLanguage`, the assumptions and the restrictions fixed; repair their dependencies after the definitions are audited.
    Preserve the four existing completeness obligations (01), (37), (38) and the RAM-bounds theorem.
    Step 5 proved the RAM-bounds theorem at Jolt's sizes (`HonestTrace.witness_params_ram_bounds`) and added the known-false #1951 item 4 lemma `HonestTrace.prover_config_holds_highest_slot`, as Ari decided on 2026-11-03.
    Ari approved the additional #1949 wrap lemmas for (08) and (11) on 2026-11-03; each is restricted to a matching row of an honest trace, and both were proved on 2026-11-25.
    The old arbitrary-bitvector admissions were deleted, and the field equalities are proved from the approved row bounds.
    No other new `sorry` was needed in Step 2.
    Reuse the frame, layout, row-composition and splice lemmas, then rebuild both libraries before declaring the migration complete.

Checked equation changes, written as the target's relations at one cycle:

```text
Implemented (01):   (Load + Store) * (RamAddress - Rs1Value - Imm + LookupOutput) = 0

Implemented (33):   RightInstructionInput = RightOperandIsRs2Value * Rs2Value
                                      + RightOperandIsImm * Imm
                                      + RightOperandIsRdWriteValue * RdWriteValue
```

For (11), write `g = 1 - AddOperands - SubtractOperands - MultiplyOperands - Advice`; the relation is `g * (RightLookupOperand - RightInstructionInput) = 0`, in both current and target form.
Expanding the target (33) into (11) includes the new contribution once.

The AddressOffset tables output an offset inside a doubleword, `index & (8 - WIDTH)`:

| Table | Width in bytes | Lookup output |
|---|---:|---|
| `AddressOffsetB` | 1 | `index & 7` |
| `AddressOffsetH` | 2 | `index & 6` |
| `AddressOffsetW` | 4 | `index & 4` |

The floor loads use `Rs1Value + Imm` for their AddressOffset lookup; LD selects the new source flag instead.
The target R1CS comment explains why subtracting the allowed offset leaves a misaligned low bit in `RamAddress`, which the RAM-address relation must reject.
Do not assume natural alignment follows from evaluating the lookup table.

## Notation

All equations are over the field. The variables are array entries (the polynomials' evaluations at Boolean indices).

- `T = {0, …, N−1}`: padded execution cycles.
- `R = {0, …, 127}`: architectural and virtual registers.
- `M = {0, …, K_RAM−1}`: remapped RAM word addresses.
- `B = {0, …, K_bytecode−1}`: padded, expanded bytecode rows.
- `X = {0, …, 2^128−1}`: instruction-lookup indices.
- `U = {0, …, 2^b−1}`: small address chunks, with the Rust layout's chunk width `b`.
- `D_I, D_B, D_M`: numbers of instruction, bytecode and RAM chunks.
- `digit_d(a)`: chunk `d` of the relevant address, most-significant first, with leading zero padding to the required number of chunks.
- `[P]`: 1 if the index/table predicate `P` holds, and 0 otherwise.

Flag names mean the corresponding Rust `OpFlags(CircuitFlags::…)` or `InstructionFlags(InstructionFlags::…)` columns. The suffix `Chunk` distinguishes the small `InstructionRa(d)`, `BytecodeRa(d)` and `RamRa(d)` arrays from the full-address/virtual selectors below.

## SpartanOuter — stage 1

- [x] (01) DONE: [RAM address for loads and stores](../translation/Constraints/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean) · [completeness](../theorems/Completeness/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean)
- [x] (02) DONE: [Zero RAM address for other instructions](../translation/Constraints/RamAddrEqZeroIfNotLoadStore.lean) · [completeness](../theorems/Completeness/RamAddrEqZeroIfNotLoadStore.lean)
- [x] (03) DONE: [Loads preserve RAM](../translation/Constraints/RamReadEqRamWriteIfLoad.lean) · [completeness](../theorems/Completeness/RamReadEqRamWriteIfLoad.lean)
- [x] (04) DONE: [Loads copy RAM to the destination](../translation/Constraints/RamReadEqRdWriteIfLoad.lean) · [completeness](../theorems/Completeness/RamReadEqRdWriteIfLoad.lean)
- [x] (05) DONE: [Stores copy the second source to RAM](../translation/Constraints/Rs2EqRamWriteIfStore.lean) · [completeness](../theorems/Completeness/Rs2EqRamWriteIfStore.lean)
- [x] (06) DONE: [Zero left lookup operand for add/subtract/multiply](../translation/Constraints/LeftLookupZeroIfAddSubMul.lean) · [completeness](../theorems/Completeness/LeftLookupZeroIfAddSubMul.lean)
- [x] (07) DONE: [Left lookup operand for other modes](../translation/Constraints/LeftLookupEqLeftInputOtherwise.lean) · [completeness](../theorems/Completeness/LeftLookupEqLeftInputOtherwise.lean)
- [x] (08) DONE: [Addition lookup operand](../translation/Constraints/RightLookupAdd.lean) · [completeness](../theorems/Completeness/RightLookupAdd.lean)
- [x] (09) DONE: [Subtraction lookup operand](../translation/Constraints/RightLookupSub.lean) · [completeness](../theorems/Completeness/RightLookupSub.lean)
- [x] (10) DONE: [Multiplication lookup operand](../translation/Constraints/RightLookupEqProductIfMul.lean) · [completeness](../theorems/Completeness/RightLookupEqProductIfMul.lean)
- [x] (11) DONE: [Right lookup operand for other modes](../translation/Constraints/RightLookupEqRightInputOtherwise.lean) · [completeness](../theorems/Completeness/RightLookupEqRightInputOtherwise.lean)
- [x] (12) DONE: [Assertion lookup output](../translation/Constraints/AssertLookupOne.lean) · [completeness](../theorems/Completeness/AssertLookupOne.lean)
- [x] (13) DONE: [Write lookup output to the destination](../translation/Constraints/RdWriteEqLookupIfWriteLookupToRd.lean) · [completeness](../theorems/Completeness/RdWriteEqLookupIfWriteLookupToRd.lean)
- [x] (14) DONE: [Jump return address](../translation/Constraints/RdWriteEqPCPlusConstIfJump.lean) · [completeness](../theorems/Completeness/RdWriteEqPCPlusConstIfJump.lean)
- [x] (15) DONE: [Next address after a jump](../translation/Constraints/NextUnexpandedPCEqLookupIfJump.lean) · [completeness](../theorems/Completeness/NextUnexpandedPCEqLookupIfJump.lean)
- [x] (16) DONE: [Next address after a taken branch](../translation/Constraints/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean) · [completeness](../theorems/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean)
- [x] (17) DONE: [Next address for other rows](../translation/Constraints/NextUnexpandedPCUpdateOtherwise.lean) · [completeness](../theorems/Completeness/NextUnexpandedPCUpdateOtherwise.lean)
- [x] (18) DONE: [Next expanded PC within a virtual sequence](../translation/Constraints/NextPCEqPCPlusOneIfInline.lean) · [completeness](../theorems/Completeness/NextPCEqPCPlusOneIfInline.lean)
- [x] (19) DONE: [Start virtual sequences at their beginning](../translation/Constraints/MustStartSequenceFromBeginning.lean) · [completeness](../theorems/Completeness/MustStartSequenceFromBeginning.lean)

[Rust: the 19 equality-conditional rows](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs#L121).

∀ t ∈ T; every column in this block is evaluated at t:

```text
(01) (Load + Store) · (RamAddress − Rs1Value − Imm + LookupOutput) = 0

(02) (1 − Load − Store) · RamAddress = 0

(03) Load · (RamReadValue − RamWriteValue) = 0

(04) Load · (RamReadValue − RdWriteValue) = 0

(05) Store · (Rs2Value − RamWriteValue) = 0

(06) (AddOperands + SubtractOperands + MultiplyOperands)
       · LeftLookupOperand = 0

(07) (1 − AddOperands − SubtractOperands − MultiplyOperands)
       · (LeftLookupOperand − LeftInstructionInput) = 0

(08) AddOperands
       · (RightLookupOperand − LeftInstructionInput − RightInstructionInput) = 0

(09) SubtractOperands
       · (RightLookupOperand − LeftInstructionInput + RightInstructionInput − 2^64) = 0

(10) MultiplyOperands · (RightLookupOperand − Product) = 0

(11) (1 − AddOperands − SubtractOperands − MultiplyOperands − Advice)
       · (RightLookupOperand − RightInstructionInput) = 0

(12) Assert · (LookupOutput − 1) = 0

(13) WriteLookupOutputToRD · (RdWriteValue − LookupOutput) = 0

(14) Jump · (RdWriteValue − UnexpandedPC − 4 + 2·IsCompressed) = 0

(15) Jump · (NextUnexpandedPC − LookupOutput) = 0

(16) ShouldBranch · (NextUnexpandedPC − UnexpandedPC − Imm) = 0

(17) (1 − ShouldBranch − Jump)
       · (NextUnexpandedPC − UnexpandedPC − 4
          + 4·DoNotUpdateUnexpandedPC + 2·IsCompressed) = 0

(18) (VirtualInstruction − IsLastInSequence) · (NextPC − PC − 1) = 0

(19) (NextIsVirtual − NextIsFirstInSequence) · (1 − DoNotUpdateUnexpandedPC) = 0
```

At `ff6fc6568` (15) is guarded by `Jump` instead of `ShouldJump`, which Jolt removed ([Rust](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs#L361-L367)).
A halt is a jump, so (15) also sets the next unexpanded PC of a halt row to its lookup output.

## SpartanProductVirtualization — stage 2

- [x] (20) DONE: [Product of instruction inputs](../translation/Constraints/ProductEqLeftInputMulRightInput.lean) · [completeness](../theorems/Completeness/ProductEqLeftInputMulRightInput.lean)
- [x] (21) DONE: [ShouldBranch product](../translation/Constraints/ShouldBranchEqLookupOutputMulBranch.lean) · [completeness](../theorems/Completeness/ShouldBranchEqLookupOutputMulBranch.lean)
- [x] (64) DONE: [Halt end rule](../translation/Constraints/HaltEndRule.lean) · [completeness](../theorems/Completeness/HaltEndRule.lean)

[Rust: the three product rows](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs#L430-L457); [halt-lane coefficients](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/spartan.rs#L194-L223) (`PRODUCT_HALT_LANE_LEFT_FACTOR`, `PRODUCT_HALT_LANE_OUTPUT`); [sumcheck](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/spartan/product_remainder.rs).

`Π` is the public panic claim: 1 when the claim is "panicked" and 0 otherwise.
`Halt` and `HaltPanic` are the circuit flags of the two halt instructions: `jolt.success` sets `Halt`, and EBREAK's `Panic` row sets both.

∀ t ∈ T:

```text
(20) Product(t) = LeftInstructionInput(t) · RightInstructionInput(t)

(21) ShouldBranch(t) = LookupOutput(t) · Branch(t)

(64) 2 · (NextIsNoop(t) − IsNoop(t)) = (2 − Π) · Halt(t) + HaltPanic(t)
```

At `ff6fc6568` (64) replaces the retired `ShouldJump` product (22), `ShouldJump(t) = Jump(t) · (1 − NextIsNoop(t))`.
With Boolean flags and a field characteristic above 5, (64) lets the witness enter padding only after a halt of the claimed kind, and forbids a halt row that is followed by a real row.

## RamReadWriteChecking — stage 2

- [x] (23) DONE: [RAM read-value selection](../translation/Constraints/RamReadValueEqRamRead.lean) · [completeness](../theorems/Completeness/RamReadValueEqRamRead.lean)
- [x] (24) DONE: [RAM write-value selection](../translation/Constraints/RamWriteValueEqRamReadWrite.lean) · [completeness](../theorems/Completeness/RamWriteValueEqRamReadWrite.lean)
- [x] (65) DONE: [No increment on write-protected words](../translation/Constraints/RamWriteProtected.lean) · [completeness](../theorems/Completeness/RamWriteProtected.lean)
- [x] (66) DONE: [RAM access count](../translation/Constraints/RamAccessCount.lean) · [completeness](../theorems/Completeness/RamAccessCount.lean)

[Rust: the four claims](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L73-L107); [mask C](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-program/src/preprocess/ram.rs#L126-L199) (`write_protected_word_intervals`).

`C(a)` is the public write-protection mask, `ramWriteProtectedMask` in Lean.
It is 1 when word `a` lies in the code region that Jolt's `code_region` computes from the bytecode, or overlaps the input, trusted advice, untrusted advice or stack-canary byte range; it is 0 otherwise.

∀ t ∈ T:

```text
(23) RamReadValue(t) = Σ_{a ∈ M} RamRa(a,t) · RamVal(a,t)

(24) RamWriteValue(t) = Σ_{a ∈ M} RamRa(a,t) · (RamVal(a,t) + RamInc(t))

(65) 0 = Σ_{a ∈ M} C(a) · RamRa(a,t) · RamInc(t)

(66) Load(t) + Store(t) = Σ_{a ∈ M} RamRa(a,t)
```

Constraints (65) and (66) are new at `ff6fc6568` (a16z/jolt#2408).
(66) is Jolt's only RAM one-hotness check; it replaces the retired RAM Hamming constraints (57) and (62).

## RamRafEvaluation — stage 2

- [x] (25) DONE: [RAM address reconstruction](../translation/Constraints/RamAddressEqRamRaf.lean) · [completeness](../theorems/Completeness/RamAddressEqRamRaf.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs#L133).

`lowest_address` is the memory layout's lowest byte address; remapped word `a` has byte address `lowest_address + 8a`.

```text
(25) ∀ t ∈ T:
       RamAddress(t) = Σ_{a ∈ M} (lowest_address + 8a) · RamRa(a,t)
```

## RamOutputCheck — stage 2

- [x] (26) DONE: [Public RAM output](../translation/Constraints/RamOutputEqPublicIo.lean) · [completeness](../theorems/Completeness/RamOutputEqPublicIo.lean)

[Rust: constraint](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs); [public arrays](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-program/src/preprocess/public_io.rs#L23-L70).

`IoMask(a) = [io_mask_start ≤ a < io_mask_end]`, where `io_mask_start` and `io_mask_end` are the remapped words of `input_start` and `output_end`.
`ValIo` contains the packed public input and output words; other entries are zero, exactly as in `PublicIoMemory::new`.
At `ff6fc6568` Jolt has no panic or termination word.

```text
(26) ∀ a ∈ M:
       IoMask(a) · (RamValFinal(a) − ValIo(a)) = 0
```

## SpartanShift — stage 3

- [x] (27) DONE: [NextUnexpandedPC shift](../translation/Constraints/NextUnexpandedPCEqShift.lean) · [completeness](../theorems/Completeness/NextUnexpandedPCEqShift.lean)
- [x] (28) DONE: [NextPC shift](../translation/Constraints/NextPCEqShift.lean) · [completeness](../theorems/Completeness/NextPCEqShift.lean)
- [x] (29) DONE: [NextIsVirtual shift](../translation/Constraints/NextIsVirtualEqShift.lean) · [completeness](../theorems/Completeness/NextIsVirtualEqShift.lean)
- [x] (30) DONE: [NextIsFirstInSequence shift](../translation/Constraints/NextIsFirstInSequenceEqShift.lean) · [completeness](../theorems/Completeness/NextIsFirstInSequenceEqShift.lean)
- [x] (31) DONE: [NextIsNoop shift](../translation/Constraints/NextIsNoopEqShift.lean) · [completeness](../theorems/Completeness/NextIsNoopEqShift.lean)

[Rust: constraint](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs#L103); [non-wrapping successor](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-poly/src/eq_plus_one.rs#L1).

∀ t ∈ T:

```text
(27) NextUnexpandedPC(t) =
       if t < N−1 then UnexpandedPC(t+1) else 0

(28) NextPC(t) =
       if t < N−1 then PC(t+1) else 0

(29) NextIsVirtual(t) =
       if t < N−1 then VirtualInstruction(t+1) else 0

(30) NextIsFirstInSequence(t) =
       if t < N−1 then IsFirstInSequence(t+1) else 0

(31) NextIsNoop(t) =
       if t < N−1 then IsNoop(t+1) else 1
```

## InstructionInputVirtualization — stage 3

- [x] (32) DONE: [Left instruction-input selection](../translation/Constraints/LeftInstructionInputEqSelection.lean) · [completeness](../theorems/Completeness/LeftInstructionInputEqSelection.lean)
- [x] (33) DONE: [Right instruction-input selection](../translation/Constraints/RightInstructionInputEqSelection.lean) · [completeness](../theorems/Completeness/RightInstructionInputEqSelection.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L102).

∀ t ∈ T:

```text
(32) LeftInstructionInput(t) =
       LeftOperandIsRs1Value(t) · Rs1Value(t)
       + LeftOperandIsPC(t) · UnexpandedPC(t)

(33) RightInstructionInput(t) =
       RightOperandIsRs2Value(t) · Rs2Value(t)
       + RightOperandIsImm(t) · Imm(t)
       + RightOperandIsRdWriteValue(t) · RdWriteValue(t)
```

## RegistersReadWriteChecking — stage 4

- [x] (34) DONE: [Destination register write-value selection](../translation/Constraints/RdWriteValueEqRegistersReadWrite.lean) · [completeness](../theorems/Completeness/RdWriteValueEqRegistersReadWrite.lean)
- [x] (35) DONE: [First source register value selection](../translation/Constraints/Rs1ValueEqRegistersRead.lean) · [completeness](../theorems/Completeness/Rs1ValueEqRegistersRead.lean)
- [x] (36) DONE: [Second source register value selection](../translation/Constraints/Rs2ValueEqRegistersRead.lean) · [completeness](../theorems/Completeness/Rs2ValueEqRegistersRead.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs#L97).

∀ t ∈ T:

```text
(34) RdWriteValue(t) = Σ_{r ∈ R} RdWa(r,t) · (RegistersVal(r,t) + RdInc(t))

(35) Rs1Value(t) = Σ_{r ∈ R} Rs1Ra(r,t) · RegistersVal(r,t)

(36) Rs2Value(t) = Σ_{r ∈ R} Rs2Ra(r,t) · RegistersVal(r,t)
```

## RamValCheck — stage 4

- [x] (37) DONE: [RAM value from preceding increments](../translation/Constraints/RamValEqInitialPlusPrefixRamInc.lean) · [completeness](../theorems/Completeness/RamValEqInitialPlusPrefixRamInc.lean)
- [x] (38) DONE: [Final RAM value from all increments](../translation/Constraints/RamValFinalEqInitialPlusRamInc.lean) · [completeness](../theorems/Completeness/RamValFinalEqInitialPlusRamInc.lean)

Before the `ff6fc6568` re-pin, (37) and (38) were `FIXME:` targets: the [termination-word RAM history bug](../../bug-report/ram-val-termination/README.md) and [a16z/jolt#1951](https://github.com/a16z/jolt/issues/1951) item 1 (a run that never stores to the termination word) blocked them.

[Rust: constraint](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135); [initial public RAM](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/ram.rs#L134).

`Init(a)` is the initial word array: the program image and public inputs, together with the trusted/untrusted advice words at their memory-layout addresses, zero elsewhere. Advice words are inputs to this array, not additional public constants.

```text
(37) ∀ a ∈ M, ∀ t ∈ T:
       RamVal(a,t) = Init(a) + Σ_{s ∈ T, s < t} RamRa(a,s) · RamInc(s)

(38) ∀ a ∈ M:
       RamValFinal(a) = Init(a) + Σ_{s ∈ T} RamRa(a,s) · RamInc(s)
```

## InstructionReadRaf — stage 5

- [x] (39) DONE: [Lookup output from the selected table](../translation/Constraints/LookupOutputEqInstructionReadRaf.lean) · [completeness](../theorems/Completeness/LookupOutputEqInstructionReadRaf.lean)
- [x] (40) DONE: [Left lookup operand reconstruction](../translation/Constraints/LeftLookupOperandEqInstructionRaf.lean) · [completeness](../theorems/Completeness/LeftLookupOperandEqInstructionRaf.lean)
- [x] (41) DONE: [Right lookup operand reconstruction](../translation/Constraints/RightLookupOperandEqInstructionRaf.lean) · [completeness](../theorems/Completeness/RightLookupOperandEqInstructionRaf.lean)
- [x] (63) DONE: [Canonical instruction address, Akita build only](../translation/Constraints/InstructionAddressCanonical.lean) · [completeness](../theorems/Completeness/InstructionAddressCanonical.lean)

[Rust: constraint](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/instruction/read_raf.rs#L90); [operand coefficients](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L180).

Let `Q` be the variants of [`LookupTableKind<64>`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-lookup-tables/src/tables/mod.rs#L137). The fixed array `Table_q(x)` is Rust's `q.evaluate_mle(bits(x))` at the 128-bit Boolean encoding of `x`.

For `x = Σ_{i=0}^{127} 2^(127−i) x_i`, define the two deinterleaved operands:

```text
Left(x)  = Σ_{i=0}^{63} 2^(63−i) x_{2i}
Right(x) = Σ_{i=0}^{63} 2^(63−i) x_{2i+1}
```

Each virtual instruction chunk groups `n` small chunks. Write `J = D_I/n`, and let `v_j(x)` be the `j`th `nb`-bit chunk of `x`, most-significant first. Abbreviate:

```text
LookupRa(x,t) = ∏_{j=0}^{J−1} InstructionRa_j(v_j(x),t)
```

∀ t ∈ T:

```text
(39) LookupOutput(t) =
       Σ_{x ∈ X} LookupRa(x,t) · Σ_{q ∈ Q} LookupTableFlag_q(t) · Table_q(x)

(40) LeftLookupOperand(t) =
       Σ_{x ∈ X} LookupRa(x,t) · (1 − InstructionRafFlag(t)) · Left(x)

(41) RightLookupOperand(t) =
       Σ_{x ∈ X} LookupRa(x,t)
         · ((1 − InstructionRafFlag(t)) · Right(x) + InstructionRafFlag(t) · x)
```

Constraint (63) is checked only when `ringChar F < 2^128`, matching Jolt, whose
`akita` feature selects both the field `p = 2^128 - 1780711455` and this check
([Rust: flag](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs); [verifier term](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L167-L180)).
With `U(x) = 1` when the upper 64 bits of `x` are all ones and `U(x) = 0` otherwise:

```text
(63) InstructionRafFlag(t) · Σ_{x ∈ X} LookupRa(x,t) · U(x) = 0
```

Without (63), a field with `p < 2^128` lets (41) hold for an address `x ≥ p`
that aliases `x − p`. With it, a selected identity-RAF address is below
`2^128 − 2^64`, which is below the characteristic whenever `JoltField F` holds.
Every index the honest prover forms with identity RAF is below that bound.

## RegistersValEvaluation — stage 5

- [x] (42) DONE: [Register value from preceding increments](../translation/Constraints/RegistersValEqPrefixRdInc.lean) · [completeness](../theorems/Completeness/RegistersValEqPrefixRdInc.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs#L69).

```text
(42) ∀ r ∈ R, ∀ t ∈ T:
       RegistersVal(r,t) = Σ_{s ∈ T, s < t} RdWa(r,s) · RdInc(s)
```

The empty sum at `t = 0` is zero.

## BytecodeReadRaf — stages 6a–6b

- [x] (43) DONE: [Expanded PC from bytecode](../translation/Constraints/PCEqBytecodeRead.lean) · [completeness](../theorems/Completeness/PCEqBytecodeRead.lean)
- [x] (44) DONE: [Unexpanded PC from bytecode](../translation/Constraints/UnexpandedPCEqBytecodeRead.lean) · [completeness](../theorems/Completeness/UnexpandedPCEqBytecodeRead.lean)
- [x] (45) DONE: [Immediate from bytecode](../translation/Constraints/ImmEqBytecodeRead.lean) · [completeness](../theorems/Completeness/ImmEqBytecodeRead.lean)
- [x] (46) DONE: [Circuit flags from bytecode](../translation/Constraints/OpFlagsEqBytecodeRead.lean) · [completeness](../theorems/Completeness/OpFlagsEqBytecodeRead.lean)
- [x] (47) DONE: [Instruction flags from bytecode](../translation/Constraints/InstructionFlagsEqBytecodeRead.lean) · [completeness](../theorems/Completeness/InstructionFlagsEqBytecodeRead.lean)
- [x] (48) DONE: [First source selector from bytecode](../translation/Constraints/Rs1RaEqBytecodeRead.lean) · [completeness](../theorems/Completeness/Rs1RaEqBytecodeRead.lean)
- [x] (49) DONE: [Second source selector from bytecode](../translation/Constraints/Rs2RaEqBytecodeRead.lean) · [completeness](../theorems/Completeness/Rs2RaEqBytecodeRead.lean)
- [x] (50) DONE: [Destination selector from bytecode](../translation/Constraints/RdWaEqBytecodeRead.lean) · [completeness](../theorems/Completeness/RdWaEqBytecodeRead.lean)
- [x] (51) DONE: [Lookup-table flags from bytecode](../translation/Constraints/LookupTableFlagEqBytecodeRead.lean) · [completeness](../theorems/Completeness/LookupTableFlagEqBytecodeRead.lean)
- [x] (52) DONE: [Instruction RAF flag from bytecode](../translation/Constraints/InstructionRafFlagEqBytecodeRead.lean) · [completeness](../theorems/Completeness/InstructionRafFlagEqBytecodeRead.lean)
- [x] (53) DONE: [Entry bytecode row](../translation/Constraints/BytecodeRaAtEntryEqOne.lean) · [completeness](../theorems/Completeness/BytecodeRaAtEntryEqOne.lean)

[Rust: row values](https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L594); [PC and entry](https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L360).

Abbreviate the full bytecode selector:

```text
BytecodeRa(k,t) = ∏_{d=0}^{D_B−1} BytecodeRaChunk_d(digit_d(k),t)
```

For each fixed, padded program row `k ∈ B`, `Addr_B(k)` and `Imm_B(k)` are its address and signed immediate. Decode the row as in `read_raf_row_values` (including its Noop fallback). Define:

```text
CircuitFlag_B(f,k)     = decoded row's circuit_flags()[f]
InstructionFlag_B(g,k) = decoded row's instruction_flags()[g]
Rs1_B(r,k)            = [row.operands.rs1 = Some(r)]
Rs2_B(r,k)            = [row.operands.rs2 = Some(r)]
Rd_B(r,k)             = [row.operands.rd  = Some(r)]
TableFlag_B(q,k)      = [decoded row's lookup_table() = Some(q)]
RafFlag_B(k)          = [!decoded row's circuit_flags().is_interleaved_operands()]
```

Here `f` ranges over all 16 `CircuitFlags`, `g` over all 7 `InstructionFlags`, `r ∈ R`, and `q ∈ Q`. Missing register/table operands give zero indicators.

∀ t ∈ T (and all f, g, r, q of the indicated types):

```text
(43) PC(t) = Σ_{k ∈ B} k · BytecodeRa(k,t)

(44) UnexpandedPC(t) = Σ_{k ∈ B} Addr_B(k) · BytecodeRa(k,t)

(45) Imm(t) = Σ_{k ∈ B} Imm_B(k) · BytecodeRa(k,t)

(46) OpFlags(f)(t) = Σ_{k ∈ B} CircuitFlag_B(f,k) · BytecodeRa(k,t)

(47) InstructionFlags(g)(t) =
       Σ_{k ∈ B} InstructionFlag_B(g,k) · BytecodeRa(k,t)

(48) Rs1Ra(r,t) = Σ_{k ∈ B} Rs1_B(r,k) · BytecodeRa(k,t)

(49) Rs2Ra(r,t) = Σ_{k ∈ B} Rs2_B(r,k) · BytecodeRa(k,t)

(50) RdWa(r,t) = Σ_{k ∈ B} Rd_B(r,k) · BytecodeRa(k,t)

(51) LookupTableFlag_q(t) = Σ_{k ∈ B} TableFlag_B(q,k) · BytecodeRa(k,t)

(52) InstructionRafFlag(t) = Σ_{k ∈ B} RafFlag_B(k) · BytecodeRa(k,t)
```

For the program's `entry_bytecode_index = e`:

```text
(53) BytecodeRa(e,0) = 1
```

## Booleanity — stages 6a–6b

- [x] (54) DONE: [Instruction chunk selector booleanity](../translation/Constraints/InstructionRaChunkBooleanity.lean) · [completeness](../theorems/Completeness/InstructionRaChunkBooleanity.lean)
- [x] (55) DONE: [Bytecode chunk selector booleanity](../translation/Constraints/BytecodeRaChunkBooleanity.lean) · [completeness](../theorems/Completeness/BytecodeRaChunkBooleanity.lean)
- [x] (56) DONE: [RAM chunk selector booleanity](../translation/Constraints/RamRaChunkBooleanity.lean) · [completeness](../theorems/Completeness/RamRaChunkBooleanity.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L25).

∀ t ∈ T, ∀ u ∈ U, and every chunk d in the respective family:

```text
(54) InstructionRaChunk_d(u,t) · (InstructionRaChunk_d(u,t) − 1) = 0

(55) BytecodeRaChunk_d(u,t) · (BytecodeRaChunk_d(u,t) − 1) = 0

(56) RamRaChunk_d(u,t) · (RamRaChunk_d(u,t) − 1) = 0
```

## RamRaVirtualization — stage 6b

- [x] (58) DONE: [RAM address selector from chunks](../translation/Constraints/RamRaEqChunkProduct.lean) · [completeness](../theorems/Completeness/RamRaEqChunkProduct.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/ram/ra_virtualization.rs); [chunk product](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/ram.rs#L163).

```text
(58) ∀ a ∈ M, ∀ t ∈ T:
       RamRa(a,t) = ∏_{d=0}^{D_M−1} RamRaChunk_d(digit_d(a),t)
```

## InstructionRaVirtualization — stage 6b

- [x] (59) DONE: [Virtual instruction selectors from small chunks](../translation/Constraints/InstructionRaEqChunkProduct.lean) · [completeness](../theorems/Completeness/InstructionRaEqChunkProduct.lean)

[Rust](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/instruction/ra_virtualization.rs); [chunk grouping](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs#L402).

```text
(59) ∀ t ∈ T, ∀ j ∈ {0, …, J−1}, ∀ v ∈ {0, …, 2^(nb)−1}:
       InstructionRa_j(v,t) =
         ∏_{h=0}^{n−1} InstructionRaChunk_{jn+h}(digit_h(v),t)
```

Here `digit_h(v)` splits the `nb`-bit virtual chunk into its `n` small chunks.

## Hamming weights — HammingWeightClaimReduction, stage 7

- [x] (60) DONE: [Instruction chunk hamming weights](../translation/Constraints/InstructionRaChunkHammingWeight.lean) · [completeness](../theorems/Completeness/InstructionRaChunkHammingWeight.lean)
- [x] (61) DONE: [Bytecode chunk hamming weights](../translation/Constraints/BytecodeRaChunkHammingWeight.lean) · [completeness](../theorems/Completeness/BytecodeRaChunkHammingWeight.lean)

[Rust: prescribed weights](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs#L82); [sumcheck](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-claims/src/protocols/jolt/relations/claim_reductions/hamming_weight.rs#L102).

∀ t ∈ T, and every chunk d in the respective family:

```text
(60) Σ_{u ∈ U} InstructionRaChunk_d(u,t) = 1

(61) Σ_{u ∈ U} BytecodeRaChunk_d(u,t) = 1
```

At `ff6fc6568` Jolt no longer checks RAM chunk Hamming weights; (66) replaces the retired (57) and (62).
