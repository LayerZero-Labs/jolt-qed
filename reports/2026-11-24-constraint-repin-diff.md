# Constraint generator repin to Jolt main

Date: 2026-11-24 (requested report date; work started 2026-11-23).
Lean baseline: `76cc2539fdc5b83cd8cbb88f53368cbece641cb4`, branch `repin/constraint-gen`.
Generator source: LayerZero-Labs/jolt-qed#56, `origin/inline/t2-decoder-sweep`, requested head `dd6b7b87e`.
Jolt target: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The handwritten model remains pinned to `c97e93004fbf804409f0374fe8457c8f1562ce71` in `methods/soundness.md`.

The generator has completed successfully: 22 rows over 40 variables, four relations with 14 claims, and 96 instruction kinds.
Both public panic-bit branches are generated and checked.
No handwritten constraint, bytecode file, Sail file, soundness statement or restriction has changed.

## Port scope

The port includes the T3 generator, its guide and shell scripts, the three generated Lean files, `Types.lean`, `Semantics.lean`, `Equiv.lean`, and the constraint-generation workflow.
The Cargo package excludes the expansion driver, decoder sweep, lookup-table generator, expansion recipes and inline crates.
The shared `rows.rs` is reduced to flag-order validation and production RAF extraction, the only helpers T3 calls.
Lean imports change to this branch's `JoltConstraints.translation` layout.
`JoltConstraints.lean` imports the equivalence module, as #56 did.
The workflow targets the full Jolt target hash above.

## Confirmed generated differences

Rows 00–13 and 15–20 have identical integer coefficients and variable names after ignoring column renumbering.
Row 14 changes `ShouldJump * (NextUnexpandedPC - LookupOutput) = 0` to `OpFlags_Jump * (NextUnexpandedPC - LookupOutput) = 0` (`rv64.rs:363-367`, #2451).
Row 21 changes `OpFlags_Jump * (1 - NextIsNoop) = ShouldJump` to `2 * (NextIsNoop - IsNoop) = (2 - claimedPanic) * OpFlags_Halt + OpFlags_HaltPanic` (`rv64.rs:444-458`; `geometry/spartan.rs:194-222`, #2451).
The latter requires genuinely new inputs, not a renaming of the old `ShouldJump` column.

RAM claims 0 and 1 and all register, instruction-input and shift claims have identical expressions, weights and offsets.
RAM claim 2 is new: `0 = sum_k C(k) * RamRa(k,t) * RamInc(t)` (`ram/read_write_checking.rs:88-93`, #2408, retaining #2418's tracer contract).
RAM claim 3 is new: `Load(t) + Store(t) = sum_k RamRa(k,t)` (`ram/read_write_checking.rs:95-106`, #2408).
The intermediate unmapped-word mask N claim added by #2408 is absent at the target because #2509 removes it.

All 92 old kind-table entries (91 modeled instruction kinds and NoOp padding) retain the same four outputs.
Four kinds are new: `VirtualXORROT2` and `VirtualXORROT61` from #2369, and `JoltSuccess` and `JoltPanic` from #2417, with halt flags added by #2451.
The two XOR-rotate kinds were found by reading history (`828b46c1d`), beyond the halt and RAM PRs named in the brief.
They must remain visible as coverage gaps even though this port does not import inline code or change the old ISA.

The comparison layer introduces `RepinInputs` for the halt columns and public mask C.
Its values remain explicit parameters; the old model cannot supply them yet.
Generated circuit-flag and lookup-table enumerations are separate from the old witness enumerations, with exhaustive bridges for old names.
No new flag or table is dropped or replaced with a dummy value.

## R1CS row inventory

Rows are numbered from zero, as in Jolt's `rv64_trace_constraints`.
Each Lean declaration below is in `JoltConstraints/ConstraintGen/Generated/R1CS.lean`; each handwritten definition is under `JoltConstraints/translation/Constraints/`.
The Rust references use `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` at the target commit.
“Match” compares the pointwise polynomial identity, permitting ring normalization, not a whole-execution equivalence.

| Row | Generated declaration | Handwritten definition | Result | Rust construction line |
| --- | --- | --- | --- | --- |
| 00 | `rv64Row00`:96 | `ramAddrEqRs1PlusImmMinusLookupIfLoadStore` (`RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean:16`) | Match | 261 |
| 01 | `rv64Row01`:103 | `ramAddrEqZeroIfNotLoadStore` (`RamAddrEqZeroIfNotLoadStore.lean:14`) | Match | 270 |
| 02 | `rv64Row02`:110 | `ramReadEqRamWriteIfLoad` (`RamReadEqRamWriteIfLoad.lean:14`) | Match | 278 |
| 03 | `rv64Row03`:117 | `ramReadEqRdWriteIfLoad` (`RamReadEqRdWriteIfLoad.lean:14`) | Match | 282 |
| 04 | `rv64Row04`:124 | `rs2EqRamWriteIfStore` (`Rs2EqRamWriteIfStore.lean:14`) | Match | 286 |
| 05 | `rv64Row05`:131 | `leftLookupZeroIfAddSubMul` (`LeftLookupZeroIfAddSubMul.lean:14`) | Match | 290 |
| 06 | `rv64Row06`:138 | `leftLookupEqLeftInputOtherwise` (`LeftLookupEqLeftInputOtherwise.lean:14`) | Match | 298 |
| 07 | `rv64Row07`:145 | `rightLookupAdd` (`RightLookupAdd.lean:14`) | Match | 310 |
| 08 | `rv64Row08`:152 | `rightLookupSub` (`RightLookupSub.lean:14`) | Match | 318 |
| 09 | `rv64Row09`:159 | `rightLookupEqProductIfMul` (`RightLookupEqProductIfMul.lean:14`) | Match | 327 |
| 10 | `rv64Row10`:166 | `rightLookupEqRightInputOtherwise` (`RightLookupEqRightInputOtherwise.lean:14`) | Match | 331 |
| 11 | `rv64Row11`:173 | `assertLookupOne` (`AssertLookupOne.lean:14`) | Match | 344 |
| 12 | `rv64Row12`:180 | `rdWriteEqLookupIfWriteLookupToRd` (`RdWriteEqLookupIfWriteLookupToRd.lean:14`) | Match | 348 |
| 13 | `rv64Row13`:187 | `rdWriteEqPCPlusConstIfJump` (`RdWriteEqPCPlusConstIfJump.lean:14`) | Match | 352 |
| 14 | `rv64Row14`:194 | `nextUnexpandedPCEqLookupIfShouldJump` (`NextUnexpandedPCEqLookupIfShouldJump.lean:16`) | Mismatch, #2451 | 363 |
| 15 | `rv64Row15`:201 | `nextUnexpandedPCEqPCPlusImmIfShouldBranch` (`NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean:14`) | Match | 370 |
| 16 | `rv64Row16`:208 | `nextUnexpandedPCUpdateOtherwise` (`NextUnexpandedPCUpdateOtherwise.lean:14`) | Match | 378 |
| 17 | `rv64Row17`:215 | `nextPCEqPCPlusOneIfInline` (`NextPCEqPCPlusOneIfInline.lean:14`) | Match | 410 |
| 18 | `rv64Row18`:222 | `mustStartSequenceFromBeginning` (`MustStartSequenceFromBeginning.lean:14`) | Match | 417 |
| 19 | `rv64Row19`:229 | `productEqLeftInputMulRightInput` (`ProductEqLeftInputMulRightInput.lean:13`) | Match | 436 |
| 20 | `rv64Row20`:236 | `shouldBranchEqLookupOutputMulBranch` (`ShouldBranchEqLookupOutputMulBranch.lean:14`) | Match | 440 |
| 21 | `rv64Row21`:243 | `shouldJumpEqJumpMulNotNextIsNoop` (`ShouldJumpEqJumpMulNotNextIsNoop.lean:14`) | Mismatch, #2451 | 444 |

The exact row-14 forms are:

- Old `nextUnexpandedPCEqLookupIfShouldJump`: `w.ShouldJump t * (w.NextUnexpandedPC t - w.LookupOutput t) = 0`.
- New `Generated.rv64Row14`: `w.OpFlags .Jump t * (w.NextUnexpandedPC t - w.LookupOutput t) = 0`.

The exact row-21 forms are:

- Old `shouldJumpEqJumpMulNotNextIsNoop`: `w.ShouldJump t = w.OpFlags .Jump t * (1 - w.NextIsNoop t)`.
- New `Generated.rv64Row21 claimedPanic`: `2 * (w.NextIsNoop t - w.InstructionFlags .IsNoop t) = (2 - Π) * extra.halt t + extra.haltPanic t`, where Π is 0 or 1 according to `claimedPanic`.

For Π = 0, row 21's C coefficients are `(OpFlags_Halt, 2), (OpFlags_HaltPanic, 1)`.
For Π = 1, they are `(OpFlags_Halt, 1), (OpFlags_HaltPanic, 1)`.
Jolt defines these coefficients in `crates/jolt-claims/src/protocols/jolt/geometry/spartan.rs:194-222` (`PRODUCT_HALT_LANE_LEFT_FACTOR`, `PRODUCT_HALT_LANE_OUTPUT`), and constructs the row in `rv64.rs:444-458`.
Both changes came with #2451 (`1503f64a6`).
The generated column count rises from 38 to 40: remove `ShouldJump`, add `OpFlags_Halt`, `OpFlags_HaltPanic`, and `IsNoop`; column renumbering alone changes no old equation.
The fields `RepinInputs.halt` and `.haltPanic` denote new columns independently, and `IsNoop` reads the existing `InstructionFlags.IsNoop` column.

## Relation claim inventory

All declarations are in `JoltConstraints/ConstraintGen/Generated/Relations.lean`.
Claim indices are zero-based within each generated relation.
The common Rust prefix here is `crates/jolt-claims/src/protocols/jolt/relations/`.
The names EqCycle, EqProduct and EqPlusOne below abbreviate the exact generated `RelationWeight` constructors; every claim retains its input relation and offset unless stated otherwise.

| Relation / claim | Handwritten definition or old form | New expression and weight | Result | Rust source at target |
| --- | --- | --- | --- | --- |
| `ramReadWriteChecking` 0 | `ramReadValueEqRamRead` | `RamReadValue(t) = Σ_k RamRa(k,t) * RamVal(k,t)`, `RamReadWrite_EqCycle`, offset false | Match | `ram/read_write_checking.rs:73-79` |
| `ramReadWriteChecking` 1 | `ramWriteValueEqRamReadWrite` | `RamWriteValue(t) = Σ_k RamRa(k,t) * (RamVal(k,t) + RamInc(t))`, `RamReadWrite_EqCycle`, offset false | Match | `ram/read_write_checking.rs:80-87` |
| `ramReadWriteChecking` 2 | Absent; old relation had only the preceding two claims | `0 = Σ_k C(k) * (RamRa(k,t) * RamInc(t))`, `RamReadWrite_WriteProtectedEqCycle`, offset false | New constraint, #2408 | `ram/read_write_checking.rs:88-94` |
| `ramReadWriteChecking` 3 | Absent; RAM chunk Hamming constraints were separate | `OpFlags_Load(t) + OpFlags_Store(t) = Σ_k RamRa(k,t)`, `RamReadWrite_EqCycle`, offset false | New constraint, #2408 | `ram/read_write_checking.rs:95-107` |
| `registersReadWriteChecking` 0 | `rdWriteValueEqRegistersReadWrite` | `RdWriteValue(t) = Σ_r RdWa(r,t) * (RegistersVal(r,t) + RdInc(t))`, `RegistersReadWrite_EqCycle`, offset false | Match | `registers/read_write_checking.rs` (`unbatched_relation`, first claim) |
| `registersReadWriteChecking` 1 | `rs1ValueEqRegistersRead` | `Rs1Value(t) = Σ_r Rs1Ra(r,t) * RegistersVal(r,t)`, same weight/offset | Match | `registers/read_write_checking.rs` (second claim) |
| `registersReadWriteChecking` 2 | `rs2ValueEqRegistersRead` | `Rs2Value(t) = Σ_r Rs2Ra(r,t) * RegistersVal(r,t)`, same weight/offset | Match | `registers/read_write_checking.rs` (third claim) |
| `instructionInputVirtualization` 0 | `rightInstructionInputEqSelection` | `RightInstructionInput = RightOperandIsRs2Value * Rs2Value + RightOperandIsImm * Imm + RightOperandIsRdWriteValue * RdWriteValue`, `InstructionInput_EqProduct`, offset false | Match | `instruction/input_virtualization.rs` (`unbatched_relation`, first claim) |
| `instructionInputVirtualization` 1 | `leftInstructionInputEqSelection` | `LeftInstructionInput = LeftOperandIsRs1Value * Rs1Value + LeftOperandIsPC * UnexpandedPC`, same weight/offset | Match | `instruction/input_virtualization.rs` (second claim) |
| `spartanShift` 0 | `nextUnexpandedPCEqShift` | `NextUnexpandedPC = shift(UnexpandedPC)`, `SpartanShift_EqPlusOneOuter`, offset true | Match | `spartan/shift.rs:76-82` |
| `spartanShift` 1 | `nextPCEqShift` | `NextPC = shift(PC)`, same weight/offset | Match | `spartan/shift.rs:83-89` |
| `spartanShift` 2 | `nextIsVirtualEqShift` | `NextIsVirtual = shift(OpFlags_VirtualInstruction)`, same weight/offset | Match | `spartan/shift.rs:90-98` |
| `spartanShift` 3 | `nextIsFirstInSequenceEqShift` | `NextIsFirstInSequence = shift(OpFlags_IsFirstInSequence)`, same weight/offset | Match | `spartan/shift.rs:99-107` |
| `spartanShift` 4 | `nextIsNoopEqShift` | `1 - NextIsNoop = shift(1 - InstructionFlags_IsNoop)`, `SpartanShift_EqPlusOneProduct`, offset true | Match | `spartan/shift.rs:108-117` |

Here `shift` reads the next cycle and is zero at the last cycle.
Consequently the last shift claim still requires `NextIsNoop = 1` at the final cycle; changing row 21 does not change this shift identity.
C is a public address mask, not a witness constant guessed by the port.
Jolt constructs C from code, input, trusted advice, untrusted advice and canary words in `crates/jolt-program/src/preprocess/ram.rs:127-165` (`write_protected_word_intervals`).
The verifier evaluates `WriteProtectedEqCycle` as `eq_cycle * mask_mle(C, r_address)` in `crates/jolt-verifier/src/stages/stage2/ram_read_write_checking.rs:107-108`.
`RelationClaim.Holds` therefore keeps C inside the RAM-address sum.
#2418 (`8e210795f`) supplies the tracer's value-preserving store contract; #2408 (`4e0163f78`) adds the verifier constraint.
#2509 removes the intermediate #2408 claim `0 = Σ_k N(k) * RamRa(k,t)` and its `UnmappedEqCycle` weight, where N selected inaccessible words.
The final target has four RAM claims, not five: the I/O gap and heap padding are now accessible RAM, and no N mask is emitted.

## Kind-table inventory

Each row lists the exact outputs of `Generated.kindCircuitFlags`, `kindInstructionFlags`, `kindLookupTable`, and `kindRafFlag` at the canonical stamp.
These declarations and `JoltKind` are in `JoltConstraints/ConstraintGen/Generated/KindTables.lean`.
A match compares all four outputs with `JoltMetadata` on the corresponding old `JoltISA.Instr` constructor; NoOp compares with the padding rules.
CF and IF lists use constructor names without their leading dot.
The two new circuit flags are kept in `Generated.CircuitFlag`; the two new lookup tables are kept in `Generated.LookupTable`.

| Kind | CF | IF | Lookup table | RAF | Old model |
| --- | --- | --- | --- | --- | --- |
| `NoOp` | `[DoNotUpdateUnexpandedPC]` | `[IsNoop]` | `none` | `false` | Match |
| `ADD` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `RangeCheck` | `true` | Match |
| `ADDI` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `RangeCheck` | `true` | Match |
| `AND` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `And` | `false` | Match |
| `ANDI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `And` | `false` | Match |
| `ANDN` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `Andn` | `false` | Match |
| `AUIPC` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsPC, RightOperandIsImm]` | `RangeCheck` | `true` | Match |
| `BEQ` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `Equal` | `false` | Match |
| `BGE` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `SignedGreaterThanEqual` | `false` | Match |
| `BGEU` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `UnsignedGreaterThanEqual` | `false` | Match |
| `BLT` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `SignedLessThan` | `false` | Match |
| `BLTU` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `UnsignedLessThan` | `false` | Match |
| `BNE` | `[]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value, Branch]` | `NotEqual` | `false` | Match |
| `FENCE` | `[]` | `[]` | `none` | `false` | Match |
| `JAL` | `[AddOperands, Jump]` | `[LeftOperandIsPC, RightOperandIsImm]` | `RangeCheck` | `true` | Match |
| `JALR` | `[AddOperands, Jump]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `RangeCheckAligned` | `true` | Match |
| `LD` | `[Load]` | `[RightOperandIsRdWriteValue]` | `none` | `false` | Match |
| `LUI` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm]` | `RangeCheck` | `true` | Match |
| `MUL` | `[MultiplyOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `RangeCheck` | `true` | Match |
| `MULHU` | `[MultiplyOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `UpperWord` | `true` | Match |
| `OR` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `Or` | `false` | Match |
| `ORI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `Or` | `false` | Match |
| `SD` | `[Store]` | `[]` | `none` | `false` | Match |
| `SLT` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `SignedLessThan` | `false` | Match |
| `SLTI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `SignedLessThan` | `false` | Match |
| `SLTIU` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `UnsignedLessThan` | `false` | Match |
| `SLTU` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `UnsignedLessThan` | `false` | Match |
| `SUB` | `[SubtractOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `RangeCheck` | `true` | Match |
| `XOR` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `Xor` | `false` | Match |
| `XORI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `Xor` | `false` | Match |
| `VirtualAdvice` | `[WriteLookupOutputToRD, Advice]` | `[]` | `RangeCheck` | `true` | Match |
| `VirtualAdviceLoad` | `[WriteLookupOutputToRD, Advice]` | `[]` | `RangeCheck` | `true` | Match |
| `VirtualAssertEQ` | `[Assert]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `Equal` | `false` | Match |
| `VirtualAssertLTE` | `[Assert]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `UnsignedLessThanEqual` | `false` | Match |
| `VirtualHostIO` | `[]` | `[]` | `none` | `false` | Match |
| `VirtualAssertValidDiv0` | `[Assert]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `ValidDiv0` | `false` | Match |
| `VirtualAssertValidUnsignedRemainder` | `[Assert]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `ValidUnsignedRemainder` | `false` | Match |
| `VirtualAssertMulUNoOverflow` | `[MultiplyOperands, Assert]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `MulUNoOverflow` | `true` | Match |
| `VirtualZeroExtendWord` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `LowerHalfWord` | `true` | Match |
| `VirtualSignExtendWord` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `SignExtendWord` | `true` | Match |
| `VirtualPow2W` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `Pow2W` | `true` | Match |
| `VirtualPow2IW` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm]` | `Pow2W` | `true` | Match |
| `VirtualMovsign` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `SignMask` | `false` | Match |
| `VirtualMULI` | `[MultiplyOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `RangeCheck` | `true` | Match |
| `VirtualPow2` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `Pow2` | `true` | Match |
| `VirtualPow2I` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm]` | `Pow2` | `true` | Match |
| `VirtualRev8W` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `VirtualRev8W` | `true` | Match |
| `VirtualROTRI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualROTR` | `false` | Match |
| `VirtualROTRIW` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualROTRW` | `false` | Match |
| `VirtualShiftRightBitmask` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `ShiftRightBitmask` | `true` | Match |
| `VirtualShiftRightBitmaskI` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm]` | `ShiftRightBitmask` | `true` | Match |
| `VirtualSRA` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualSRA` | `false` | Match |
| `VirtualSRAI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualSRA` | `false` | Match |
| `VirtualSRL` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualSRL` | `false` | Match |
| `VirtualSRLI` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualSRL` | `false` | Match |
| `VirtualXORROT32` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT32` | `false` | Match |
| `VirtualXORROT24` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT24` | `false` | Match |
| `VirtualXORROT16` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT16` | `false` | Match |
| `VirtualXORROT63` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT63` | `false` | Match |
| `VirtualXORROTW16` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW16` | `false` | Match |
| `VirtualXORROTW12` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW12` | `false` | Match |
| `VirtualXORROTW8` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW8` | `false` | Match |
| `VirtualXORROTW7` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW7` | `false` | Match |
| `ADDW` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `SignExtendWord` | `true` | Match |
| `ADDIW` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `SignExtendWord` | `true` | Match |
| `SUBW` | `[SubtractOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `SignExtendWord` | `true` | Match |
| `MULW` | `[MultiplyOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `SignExtendWord` | `true` | Match |
| `VirtualMULIW` | `[MultiplyOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `SignExtendWord` | `true` | Match |
| `VirtualWindowMaskW` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `WindowMaskW` | `true` | Match |
| `VirtualPextSigned` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `PextSigned` | `false` | Match |
| `VirtualNegateIf` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualNegateIf` | `false` | Match |
| `VirtualXORROTW22` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW22` | `false` | Match |
| `VirtualXORROTW19` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW19` | `false` | Match |
| `VirtualXORROTW6` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTW6` | `false` | Match |
| `VirtualShiftRightBitmaskW` | `[AddOperands, WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value]` | `ShiftRightBitmaskW` | `true` | Match |
| `VirtualSRLW` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualSRLW` | `false` | Match |
| `VirtualSRLIW` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualSRLW` | `false` | Match |
| `VirtualSRAW` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualSRAW` | `false` | Match |
| `VirtualSRAIW` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `VirtualSRAW` | `false` | Match |
| `VirtualPext` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `Pext` | `false` | Match |
| `VirtualWindowMaskB` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `WindowMaskB` | `true` | Match |
| `VirtualWindowMaskH` | `[AddOperands, WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `WindowMaskH` | `true` | Match |
| `VirtualShiftDataB` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `ShiftDataB` | `false` | Match |
| `VirtualShiftDataH` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `ShiftDataH` | `false` | Match |
| `VirtualShiftDataW` | `[WriteLookupOutputToRD]` | `[RightOperandIsImm, LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `ShiftDataW` | `false` | Match |
| `VirtualXORROTL1` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROTL1` | `false` | Match |
| `VirtualLoadB` | `[AddOperands, Load]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetB` | `true` | Match |
| `VirtualLoadH` | `[AddOperands, Load]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetH` | `true` | Match |
| `VirtualLoadW` | `[AddOperands, Load]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetW` | `true` | Match |
| `VirtualStoreB` | `[AddOperands, Store]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetB` | `true` | Match |
| `VirtualStoreH` | `[AddOperands, Store]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetH` | `true` | Match |
| `VirtualStoreW` | `[AddOperands, Store]` | `[RightOperandIsImm, LeftOperandIsRs1Value]` | `AddressOffsetW` | `true` | Match |
| `VirtualXORROT2` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT2` | `false` | Absent, #2369 |
| `VirtualXORROT61` | `[WriteLookupOutputToRD]` | `[LeftOperandIsRs1Value, RightOperandIsRs2Value]` | `VirtualXORROT61` | `false` | Absent, #2369 |
| `JoltSuccess` | `[Jump, Halt]` | `[]` | `none` | `false` | Absent, #2417 / #2451 |
| `JoltPanic` | `[Jump, Halt, HaltPanic]` | `[]` | `none` | `false` | Absent, #2417 / #2451 |

For each of the four absent kinds, the exact old form is “no `JoltISA.Instr` constructor, no old kind entry”; inventing an old definition would hide the gap.
The generated names are `JoltKind.VirtualXORROT2`, `.VirtualXORROT61`, `.JoltSuccess`, and `.JoltPanic`.
Their kind names and canonical identifiers appear in `crates/jolt-riscv/src/lib.rs:247-250`.
The new XOR-rotate flag declarations are `instructions/virt/xor_rot2.rs:3-8` and `instructions/virt/xor_rot61.rs:3-8` under `crates/jolt-riscv/src/`, added by #2369 (`828b46c1d`).
Their selected tables are `LookupTable.VirtualXORROT2` and `.VirtualXORROT61`, mapped at `crates/jolt-lookup-tables/src/instructions/virt/xor_rot.rs:13-14`.
The halts' `none` table entries are at `crates/jolt-lookup-tables/src/instructions/virt/halt.rs:6-7`, and both lookup outputs are 0 there at lines 14-15 and 24-25.
The halt kinds are introduced by #2417 (`8005bf4e9`), and their `Jump`, `Halt`, `HaltPanic` flags implement #2451.
The exact halt flag declarations are in `crates/jolt-riscv/src/instructions/virt/halt.rs:3-17` (`Success`, `Panic`).
RAF is extracted with `InstructionRafFlag::extract` in `crates/jolt-witness/src/witnesses/flags.rs:121` for every kind and every checked stamp.

The generated flag order now has 16 entries rather than 14, appending `Halt` and `HaltPanic` (`crates/jolt-riscv/src/flags.rs:49-52,92-93`).
All 16 emitted stamp-table entries retain their old flags, including the two example nonzero sequence counts 1 and 65535.
The generator also checks all 4,108 stamps over all 96 kinds, retaining the original NoOp exception for invalid stamped padding trace rows.
New halt kinds have the same stamp additions as the old non-NoOp kinds.
The exact total-coverage gap is recorded separately from the per-old-instruction metadata equalities; those equalities do not claim an old constructor for a new kind.

## The 29 handwritten conjuncts outside T3

`ConstraintEquations` at `JoltConstraints/translation/Constraints/All.lean:74` has 63 fields at the Lean baseline.
T3 originally compared 34 fields (22 R1CS identities and 12 relation claims), leaving the following 29.
At this repin, 32 of those old 34 identities retain their formulas; row 14 and row 21 differ, and the two new RAM claims are additional obligations.
The aggregate RAM equivalence must also be admitted because its generated side now includes the new obligations.
“Context” below means the identity itself has not been shown to change, but the old domain, initialization, metadata, or instruction coverage on which it depends needs review.
It is not a claim that the whole handwritten conjunct matches Jolt main.
Every Rust reference in this section is at `ff6fc6568`.

| Handwritten conjunct | Effect of the repin; source evidence |
| --- | --- |
| `ramAddressEqRamRaf` | Context: the affine unmap `lowest + 8*k` remains (`relations/ram/raf_evaluation.rs:69-74` under `crates/jolt-claims/src/protocols/jolt/`), but #2509 makes I/O-gap and padded-heap words accessible within that RAM domain; the global selector sum now enforces no selection off memory rows (`relations/ram/read_write_checking.rs:95-106`). |
| `ramOutputEqPublicIo` | Changed: the public mask and words change as detailed below; #2451 removes flag words and #2509 releases the I/O gap. See `crates/jolt-program/src/preprocess/public_io.rs:9-13,27-45`. |
| `ramValEqInitialPlusPrefixRamInc` | Context: the recurrence still reconstructs RAM from its initial value and increment prefix, but #2451 removes the synthetic termination/panic words and #2509 makes gap/padding values observable RAM. Public initialization contains code and inputs, not flag words (`crates/jolt-program/src/preprocess/ram.rs:353-382`). |
| `ramValFinalEqInitialPlusRamInc` | Context: the same initialization and domain changes affect final RAM and its consumers; final I/O equality no longer forces old flag or gap values (`public_io.rs:9-13,27-45` above). |
| `lookupOutputEqInstructionReadRaf` | Context: #2417/#2451 add two table-free halt kinds whose lookup output is zero; see `crates/jolt-lookup-tables/src/traits.rs` (`InstructionLookupTable`, table-free `LookupQuery`) and `crates/jolt-riscv/src/instructions/virt/halt.rs:3-17`. #2369 also adds two lookup tables that the old table type lacks. |
| `leftLookupOperandEqInstructionRaf` | Context: metadata/lookup domains expand for the new kinds, including #2369; the old kinds' table and RAF selections are unchanged by generation. No changed operand-RAF identity established here. |
| `rightLookupOperandEqInstructionRaf` | Context: the same metadata and lookup-domain issue as the left operand; no changed operand-RAF identity established here. |
| `instructionAddressCanonical` | No direct change identified in these PRs; this field's identity-RAF canonical-address bound is outside T3. |
| `registersValEqPrefixRdInc` | Context: halt rows can write their link to `rd`, including nonzero `rd` (`tracer/src/emulator/cpu.rs:546-554`, #2417); no changed register-prefix recurrence established here. |
| `pcEqBytecodeRead` | Context: #2451 uses address-zero padding as the halt target; lookup selection and the bytecode domain now include halt kinds (`crates/jolt-riscv/src/instructions/virt/halt.rs:4-8,12-16`). The PC selection identity is not itself reported as changed. |
| `unexpandedPCEqBytecodeRead` | Context: same new halt bytecode rows and address-zero target; row 14 changes its guard independently. |
| `immEqBytecodeRead` | Context: the new halt bytecode rows need metadata even though the old-kind table entries retain their values; no changed immediate-read identity established. |
| `opFlagsEqBytecodeRead` | Changed type/domain: the old `CircuitFlags` has 14 constructors; the generated flag list has 16, adding `Halt` and `HaltPanic` (`crates/jolt-riscv/src/flags.rs:49-52,92-93`, #2451). The two new columns must be authenticated from bytecode, not supplied as free extra witnesses in a final model. |
| `instructionFlagsEqBytecodeRead` | Context: new halt kinds have no operand-selection flags (`instructions/virt/halt.rs:8,16` under `crates/jolt-riscv/src/`); old kinds' seven-flag entries match. |
| `rs1RaEqBytecodeRead` | Context: new halt rows have no source-selection flags; no changed register-selector read equation established. |
| `rs2RaEqBytecodeRead` | Context: same halt metadata addition; no changed register-selector read equation established. |
| `rdWaEqBytecodeRead` | Context: the halt's link register is written unless it is x0 (`tracer/src/emulator/cpu.rs:549-552`); new halt rows must be representable before certifying the old bytecode register-selector map. |
| `lookupTableFlagEqBytecodeRead` | Changed domain: the old `LookupTableKind` lacks `VirtualXORROT2` and `VirtualXORROT61` (#2369); both halts select no table. See the four missing-kind entries above and `crates/jolt-lookup-tables/src/traits.rs` (`InstructionLookupTable`). |
| `instructionRafFlagEqBytecodeRead` | Context: new kinds need the RAF metadata authenticated from bytecode; `InstructionRafFlag::extract` remains `!is_interleaved_operands()` (`crates/jolt-witness/src/witnesses/flags.rs:121-128`). |
| `bytecodeRaAtEntryEqOne` | No direct formula change identified; the entry certificate is outside these generated rows and relations. |
| `instructionRaChunkBooleanity` | No direct formula change identified; RA chunk Booleanity remains `x²-x` in `crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs:38-62`. |
| `bytecodeRaChunkBooleanity` | No direct formula change identified; the same RA Booleanity fold applies. |
| `ramRaChunkBooleanity` | Retained, not retired: #2408 removes RAM Hamming-weight Booleanity, while committed RAM selector chunks remain Boolean. The retained RAM opening is `crates/jolt-claims/src/protocols/jolt/relations/booleanity/monolith.rs:22`; its fold is `geometry/booleanity.rs:38-62`. |
| `ramHammingWeightBooleanity` | Retired by #2408: old `∀ t, RamHammingWeight(t)*(RamHammingWeight(t)-1)=0` (`RamHammingWeightBooleanity.lean:14-17`); no corresponding target column/relation. Global RAM access count is now claim 3 (`relations/ram/read_write_checking.rs:95-106`). |
| `ramRaEqChunkProduct` | Retained product shape; review its interaction with the new access-count claim. `crates/jolt-claims/src/protocols/jolt/relations/ram/ra_virtualization.rs:68-69` still uses `committed_ram_ra_product`; Booleanity plus the global product-selector sum replaces RAM chunk-weight constraints. |
| `instructionRaEqChunkProduct` | No direct formula change identified; it remains outside this generator's four extractor relations. |
| `instructionRaChunkHammingWeight` | Retained Hamming leg: `crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs:110-117` gives instruction chunks a constant-one Hamming claim. |
| `bytecodeRaChunkHammingWeight` | Retained Hamming leg: the same function retains bytecode chunks' constant-one claim. |
| `ramRaChunkHammingWeight` | Retired by #2408: old `∀ chunk t, Σ_entry RamRaChunk(chunk,entry,t) = RamHammingWeight(t)` (`RamRaChunkHammingWeight.lean:17-22`); new `has_hamming_weight_leg(.Ram _) = false` (`geometry/claim_reductions/hamming_weight.rs:110-117`). The target checks the total product selector's sum, not each chunk's weight. |

Rust paths abbreviated as `geometry/` or `relations/` in the last rows start at `crates/jolt-claims/src/protocols/jolt/`.
These are all 29 uncovered fields, with direct changes distinguished from dependencies that plausibly need repair.
No untouched conjunct has been silently certified by the T3 build.

### Exact RAM output, termination and panic changes

The old `ramPublicIoMask` is defined in `JoltConstraints/translation/Constraints/RamReadData.lean:27`.
It equals one on remapped words corresponding to `[input_start, RAM_START_ADDRESS)`.
The new `PublicIoMemory::new` sets the mask to the remapped `[input_start, output_end)` interval (`crates/jolt-program/src/preprocess/public_io.rs:27-28`).
#2509 (`ff6fc6568`) therefore removes the I/O gap from the RAM output check.
The verifier uses this exact interval in `crates/jolt-verifier/src/stages/stage2/ram_output_check.rs:58-65`.
For example, a gap word that the old equation forced to zero can now retain a guest store and is not part of the public output claim.

The old `ramPublicIoWord` (`RamReadData.lean:38-48`) overlays inputs and outputs, then a panic word `if io.panic then 1 else 0`, then a termination word equal to 1 on success (zero on panic).
The new public RAM words contain only input and output segments (`public_io.rs:32-46` above), removing both flag words under #2451.
There is no standalone termination or panic field in this branch's 63-field `ConstraintEquations`: both were part of `ramOutputEqPublicIo` through these helpers.
The new panic binding is row 21's halt lane, whose public coefficient is `SpartanProductVirtualizationPublic.ClaimedPanic` (`crates/jolt-claims/src/protocols/jolt/geometry/spartan.rs:175-180,194-222`).
The halt flags must also be authenticated through bytecode; proving a final model from arbitrary `RepinInputs` is not a replacement for that obligation.

#2418 accepts only value-preserving stores to protected words, rather than banning every store to input or advice regions.
The tracer's `assert_write_protected_store` checks the old doubleword before mutation (`tracer/src/emulator/mmu.rs:747-784`), and device admission explicitly allows input/advice stores for this later check (`mmu.rs:135-143`).
#2408 enforces preservation in the verifier through C, including code and canary words (`crates/jolt-program/src/preprocess/ram.rs:127-165`).
#2509 permits I/O-gap reads/writes (`mmu.rs:147-156`) and heap padding through the padded RAM-domain end (`mmu.rs:270-282`, `Mmu::assert_effective_address`, and the heap-padding regression at `mmu.rs:1846-1921`).
The old soundness restrictions on tracer addresses, old stable-stall stopping rule, and initial/final flag-word arguments must be reconsidered in the next task, not changed in this port.

## Validation status

The generator passes all original checks at the target, plus a check that the public panic bit changes only row 21.
The targeted Lean build passed after removing redundant `OpFlags_Load` and `OpFlags_Store` alternatives accidentally introduced during the port.
The completed comparison has four marked mismatch admissions; their precise declarations are listed below.
The aggregate comparisons depend on these admissions and are not certificates that the old handwritten model matches Jolt main.
No handwritten constraints or files under `JoltBytecode/` or `LeanRV64D/` have changed.

## Statement and trust changes

No existing handwritten definition, approved theorem, hypothesis, restriction or language predicate changed.
The imported comparison API differs from #56 only to express Jolt main's new data:

- `R1CSVar.value` and `R1CSRow.Holds` take explicit `RepinInputs` for the halt columns.
- `RelationClaim.Holds` and `Relation.Holds` take the same input record for the public address mask C.
- `rv64Row21`, `rv64Rows` and their equivalences take the statement's Boolean `claimedPanic` parameter; `ConstraintEquations.generated` uses `io.panic`.
- `kindCircuitFlags`, the stamp table and their comparisons use generated `CircuitFlag`, whose type includes the two halt flags.
- `kindLookupTable` uses generated `LookupTable`, preserving the two new XOR-rotate names; `liftLookupTable` embeds each old table by name.
- `legacyOpcodeFlag` and `legacyCircuitFlag` read every old flag by name and return false for the halt flags on old instructions, whose constructors cannot represent halts.
- The old metaprogram's exact constructor-name check is retained, while its total-coverage expectation is now a marked mismatch theorem.
  The executable check requires the missing-kind set to be exactly `VirtualXORROT2`, `VirtualXORROT61`, `JoltSuccess`, `JoltPanic`; any additional or changed gap fails elaboration.

The explicit new inputs are data parameters, not extra premises on an existing theorem.
They intentionally do not claim a verifier-certified value for C or bytecode-certified halt flags in the old model.
Those certificates belong in the subsequent handwritten-model update.
The user authorized the false equivalence placeholders for this repin; treating these admitted comparisons as proved equivalences would be unsound.
For example, row 14's old equation can hold with ShouldJump = 0 while its new equation fails with Jump = 1 and NextUnexpandedPC - LookupOutput = 1.
Similarly, the two old RAM value equations do not imply zero increments on protected words or selection of an address on memory rows.

No new `native_decide`, `bv_decide`, `decide +kernel`, `axiom`, raised `maxHeartbeats` or raised `maxRecDepth` occurs in the Lean changes.
The existing finite-enumeration proofs and structural `decide` checks from #56 remain kernel checked.
No soundness or completeness theorem imports this new module through its own source; the root library imports it as #56 did.
The generated-comparison aggregate, not the unchanged soundness proof, is the part depending on the mismatch admissions.

## Build and reproducibility evidence

The generator's final local run exited 0: 22 R1CS rows over 40 columns, four relations with 14 claims, 96 kinds, all 12 recorded checks passing (the three R1CS checks run once per panic value).
A second generation produced byte-identical files; SHA-256 hashes are:

| Generated file | SHA-256 |
| --- | --- |
| `R1CS.lean` | `47bccc19fcc94cc401904bd604c80fb3e531b97592bd03b7728dca01472d7369` |
| `Relations.lean` | `00318135f23a0e2350d63c57b30303b9a89c60e4240cd93fb979fe0e52f450de` |
| `KindTables.lean` | `9adbaa1bb87abc1a3b97d211a4cf09494281d72182bf8d2874ae3cbc669b38ca` |

Only the requested target, `JoltConstraints.ConstraintGen.Equiv` and its imports, was built through `~/claude-work/track-t-build.sh`.
The first uncached build was killed by the orchestrator; a later cache-backed build exposed only the duplicate mapping arms, then passed after their removal.
The successful profile run reported 32 s for `Semantics` and 13 s for `Equiv`, both whole-module times.
With Lean's profiler temporarily enabled, the largest reported command/tactic event was 533 ms (metadata check elaboration), and the stamp proof's largest reported simp step was 488 ms.
No individual proof was measured above about ten seconds; module time is not proof time.
The profiler option is removed from the committed sources.
The local build retains baseline dependency linter warnings and the four intentional admission warnings.
The GitHub workflow has not been run remotely.
The next task must update the handwritten constraints, certify the new flag/mask inputs, port the affected proof callers, and discharge or retire each mismatch placeholder after review.

## Declaration index and admission inventory

All proof declarations below are in `JoltConstraints/ConstraintGen/Equiv.lean`.
“Admitted mismatch” denotes a proof replaced by the marked placeholder authorized for this repin.
“Assembled” denotes a proved proof term that depends on the row/RAM mismatch declarations.
Every other listed declaration is proved without using those mismatch declarations.

| Declaration | Line | Status |
| --- | --- | --- |
| `rv64Row00_holds_iff` | 57 | Proved |
| `rv64Row01_holds_iff` | 63 | Proved |
| `rv64Row02_holds_iff` | 69 | Proved |
| `rv64Row03_holds_iff` | 75 | Proved |
| `rv64Row04_holds_iff` | 81 | Proved |
| `rv64Row05_holds_iff` | 87 | Proved |
| `rv64Row06_holds_iff` | 93 | Proved |
| `rv64Row07_holds_iff` | 99 | Proved |
| `rv64Row08_holds_iff` | 105 | Proved |
| `rv64Row09_holds_iff` | 111 | Proved |
| `rv64Row10_holds_iff` | 117 | Proved |
| `rv64Row11_holds_iff` | 123 | Proved |
| `rv64Row12_holds_iff` | 129 | Proved |
| `rv64Row13_holds_iff` | 135 | Proved |
| `rv64Row14_holds_iff` | 141 | Admitted mismatch |
| `rv64Row15_holds_iff` | 147 | Proved |
| `rv64Row16_holds_iff` | 153 | Proved |
| `rv64Row17_holds_iff` | 159 | Proved |
| `rv64Row18_holds_iff` | 165 | Proved |
| `rv64Row19_holds_iff` | 171 | Proved |
| `rv64Row20_holds_iff` | 177 | Proved |
| `rv64Row21_holds_iff` | 183 | Admitted mismatch |
| `rv64Rows_holds_iff` | 189 | Assembled from admitted comparisons |
| `ramReadWriteChecking_holds_iff` | 225 | Admitted mismatch |
| `registersReadWriteChecking_holds_iff` | 232 | Proved |
| `instructionInputVirtualization_holds_iff` | 242 | Proved |
| `spartanShift_holds_iff` | 253 | Proved |
| `mem_circuitFlagOrder` | 274 | Proved |
| `mem_instructionFlagOrder` | 278 | Proved |
| `kindCircuitFlags_kindOf` | 283 | Proved |
| `kindInstructionFlags_kindOf` | 289 | Proved |
| `kindLookupTable_kindOf` | 296 | Proved |
| `kindRafFlag_kindOf` | 302 | Proved |
| `kindCoverage_matches` | 340 | Admitted mismatch |
| `mem_kindCircuitFlags_kindOf` | 346 | Proved |
| `mem_kindInstructionFlags_kindOf` | 352 | Proved |
| `mem_stampFlags_stampClass` | 359 | Proved |
| `circuitFlag_iff_generated` | 385 | Proved |
| `padding_circuitFlag` | 395 | Proved |
| `padding_instructionFlag` | 400 | Proved |
| `padding_lookupTable_rafFlag` | 406 | Proved |
| `ConstraintEquations.generated` | 417 | Assembled from admitted comparisons |

The row-14 admission names #2451 and the new `Jump` guard.
The row-21 admission names #2451 and the panic-dependent halt lane.
The RAM-relation admission names `RamReadWriteChecking`, #2408 and #2509, whose final four-claim relation has no old-model equivalent.
The kind-coverage admission names the two halt kinds from #2417 and the two XOR-rotate kinds from #2369.
The unchanged first two RAM claim expressions are checked by source/data comparison; the entire RAM relation's two-old-claim equivalence is the admitted declaration in the table.
No other admission was introduced.

The comparison-layer interfaces are in `JoltConstraints/ConstraintGen/Semantics.lean`:

| Declaration | Line |
| --- | --- |
| `RepinInputs` | 38 |
| `Generated.R1CSVar.value` | 50 |
| `lcValue` | 94 |
| `R1CSRow.Holds` | 98 |
| `liftLookupTable` | 106 |
| `legacyOpcodeFlag` | 165 |
| `legacyCircuitFlag` | 184 |
| `kindOf` | 204 |
| `stampClass` | 304 |
| `stampFlags` | 310 |
| `generatedCircuitFlags` | 315 |
| `Generated.RelationPoly.cycleValue` | 348 |
| `Generated.RelationPoly.ramValue` | 387 |
| `Generated.RelationPoly.registerValue` | 396 |
| `PolyDomain` | 405 |
| `Generated.RelationPoly.domain` | 412 |
| `Generated.RelationWeight.outputDomain` | 448 |
| `Generated.RelationWeight.outputRelation` | 455 |
| `Generated.RelationWeight.inputRelation` | 467 |
| `ClaimExpr.polys` | 475 |
| `ClaimExpr.eval` | 481 |
| `Generated.RelationWeight.offset` | 489 |
| `RelationClaim.WellFormed` | 497 |
| `RelationClaim.Holds` | 507 |
| `Relation.Holds` | 528 |

`Types.lean` defines `R1CSRow`, `ClaimExpr`, `RelationClaim` and `Relation`; each documents its representation and a concrete example.
The 22 generated row declarations and every generated relation/kind entry are enumerated in the inventories above.
No additional premise was added to an existing theorem, and no proved fact on the split-stack baseline was replaced with an admission.
These are new comparison declarations imported from #56, with only the identified incompatible comparisons admitted at the user's explicit request.



## Closing validation

Lean commit checked: `7e0e7bef0c4fee513a4bbcff96b1d8a37dcc83f7`.
Generator and generated-data commit: `1202a057344fcb0d546e4cdd0431fe1deecb0e25`.
Jolt commit checked: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The final required targeted build exited 0 with the four marked mismatch warnings and no comparison errors.
The file-presence, nonempty-report, protected-directory status/diff, Lean token-hygiene, exact four-admission, generated-file-diff, shell-syntax, and whitespace checks all exited 0.
Only the 15 files named in the port scope changed from `76cc253`.
The final build queued behind the bytecode worker through the shared build lock; neither build bypassed the lock.
The task ends with local commits only, with no push, PR, branch switch, handwritten-model update or soundness-proof repair.
