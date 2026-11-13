# Constraint generation: T3

Date: 2026-11-12.
T3 finds zero mismatches at a16z/jolt#2384 head `580084fcf`.
Lean now proves that each handwritten R1CS row, each handwritten claim of the four relations, and Lean's per-instruction flags, lookup table and RAF flag equal the data that a new generator extracts from Jolt's own code.
A new CI job regenerates that data at the pinned commit, fails on any diff, and rebuilds the proofs.

## Revisions

- jolt-qed: branch `inline/t3-constraints` on top of `inline/t1-driver` at `b648846`.
- Jolt: a16z/jolt#2384 at `580084fcfad4788ebf48413a92dd640ca090c45f` (`580084fcf`), the commit the T1 and T4 CI jobs check.
  The generator runs with the cargo feature `zicsr-remaining`, like the T1 driver.
- Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

When PR #59 moves the CI pin to `3cc6e7bd1`, rerun the generator there.
If the generated files change, the new CI job fails until someone commits them and the proofs build again.

## What is generated

`scripts/expansion-parity/src/bin/constraint-gen.rs` is a new binary in the T1 crate.
It links Jolt's crates and writes three files under `JoltConstraints/ConstraintGen/Generated/`.

| File | Contents | Jolt source at `580084fcf` |
| --- | --- | --- |
| `R1CS.lean` | The 38 per-cycle variables in column order, and the 22 rows of `rv64_trace_constraints` as `(variable, integer coefficient)` lists for A, B and C | `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`RV64_VARIABLE_NAMES` at line 77, `RV64_CONSTRAINT_NAMES` at 139, `rv64_trace_constraints` at 458) |
| `Relations.lean` | The four relations of `extracted_claims` in `zklean-extractor/src/sumchecks.rs:24`: 12 claims, each with input relation, input and output expressions, output weight and offset | `unbatched_relation` in `relations/ram/read_write_checking.rs:59`, `relations/registers/read_write_checking.rs:64`, `relations/instruction/input_virtualization.rs:73`, `relations/spartan/shift.rs:69` (under `crates/jolt-claims/src/protocols/jolt/`) |
| `KindTables.lean` | For all 92 `JoltInstructionKind`s: circuit flags at the canonical stamp, instruction flags, lookup table and RAF flag; plus the circuit flags each of 16 sequence stamps adds | `jolt_instruction!` and `NoOp` in `crates/jolt-riscv`, `InstructionLookupTable` in `crates/jolt-lookup-tables`, `InstructionRafFlag::extract` in `crates/jolt-witness` |

I reused `zklean-extractor`'s choice of relations and its source functions (`unbatched_relation`, `rv64_trace_constraints`), not its output.
Its output targets the ZkLean library, while jolt-qed states constraints over its own `WitnessType`.

The generator reads every coefficient from Jolt's field elements.
It prints each coefficient as an integer and then checks that `Fr::from_i128` of that integer gives back the same field element.
The one large coefficient is `-2^64` in row 8 (`RightLookupSub`).

The generator also runs these checks, and exits with status 1 if any fails:

- `r1cs_shape`: 22 rows over 38 variables.
- `r1cs_outer_is_prefix`: the Spartan outer matrices are the first 19 rows of the full matrices.
- `r1cs_variable_names_unique` and `kind_names_unique`.
- `relations_match_extractor`: the generator's four relations are the `X::unbatched_relation()` calls in the body of `extracted_claims` in `zklean-extractor/src/sumchecks.rs`, in the same order.
  The extractor is a binary crate, so the generator reads that list from its source.
  It removes comments first and accepts only a body of the form `vec![A::unbatched_relation(), …]`; any other body makes the generator exit with status 2.
  I tested this on a scratch copy of `sumchecks.rs`: with the `Shift` line commented out the check fails (status 1), and with `.clone()` appended to a call the generator exits with status 2.
- `relations_count`: exactly four relations.
- `stamp_uniformity`: over 4108 stamps (every `virtual_sequence_remaining` in `None`, `0..=1024` and `65535`, times both values of `is_first_in_sequence` and `is_compressed`):
  - for every kind, the circuit flags equal the kind's canonical flags plus the stamp's flags, and the instruction flags and lookup table do not change;
  - every stamp adds exactly the flags of its representative, the same stamp with a nonzero count replaced by `1`.
    This is the collapse `stampClass` uses in Lean.
- `raf_stamp_independent`: over the same 4108 stamps, the RAF flag does not change with the stamp.

All checks pass at `580084fcf`.

## How Lean reads the generated data

`JoltConstraints/ConstraintGen/Semantics.lean` is the trusted bridge.
It is handwritten and short, and a reviewer should read it in full.

- `R1CSVar.value` maps each Jolt variable to a witness column: `One` to `1`, `OpFlags_X` to `OpFlags .X`, `Branch` to the instruction flag `Branch`, and every other name to the column of the same name.
  A row holds when `A · B = C` at every cycle.
- `RelationPoly.cycleValue`, `ramValue` and `registerValue` map each relation polynomial to a witness column.
  The six address-indexed polynomials (`RamRa`, `RamVal`, `RdWa`, `RegistersVal`, `Rs1Ra`, `Rs2Ra`) read the address in the matching sum and are `0` elsewhere.
- `RelationClaim.Holds` reads each output weight pointwise:
  - `*_EqCycle` sums the output over all addresses at the same cycle (RAM addresses or the 128 registers).
  - `InstructionInput_EqProduct` equates input and output at each cycle.
  - `SpartanShift_EqPlusOne*` equates the input at cycle `t` with the output at `t + 1`, and with `0` at the last cycle.
  `RelationClaim.WellFormed` restricts this reading to claims that fit their weight: the input relation must be the one the weight's opening point comes from, `offset` must be true exactly for the shift weights, the input may mention only cycle polynomials, and the output only cycle polynomials and polynomials over the weight's address space.
  `Relation.Holds` also requires every claim's weight to belong to the relation.
  The two shift weights use different opening points (`crates/jolt-verifier/src/stages/stage3/spartan_shift.rs:102-110`), so a claim that paired `EqPlusOneOuter` with the product relation would fail these checks.
- `kindOf` maps each `JoltISA.Instr` constructor to the Jolt kind of the same name.
  A `run_meta` check in `Equiv.lean` confirms this name match for every constructor when the file elaborates, and also fails if a Jolt kind other than `NoOp` has no Lean constructor.
- `stampClass` replaces a nonzero `virtual_sequence_remaining` by `1`.
  Jolt's `jolt_instruction!` reads the count only through `is_some`, `== Some(0)` and `unwrap_or(0) != 0`.
  The generator's `stamp_uniformity` check confirms that counts `1..=1024` and `65535` add the same flags as count `1`.

Every map from a generated name is an exhaustive `match` on a generated inductive type.
If Jolt renames or adds a variable, polynomial or weight, the generated type changes and `Semantics.lean` stops compiling until someone maps the new name.
Kinds work the other way round, since `kindOf` matches on Lean instructions: a new Jolt kind fails the `run_meta` check in `Equiv.lean` until Lean gets an instruction of that name.
The relation reading also trusts one convention: an address-indexed polynomial outside its own sum evaluates to `0`.
`WellFormed` rules out every claim that would use it, so no current claim depends on it.

## What is proved equal

`JoltConstraints/ConstraintGen/Equiv.lean` proves these theorems.

| Theorem | Statement |
| --- | --- |
| `rv64Row00_holds_iff` … `rv64Row21_holds_iff` | Generated row `NN` holds iff the handwritten constraint holds (table below). |
| `rv64Rows_holds_iff` | All 22 rows hold iff the 22 handwritten R1CS constraints hold. |
| `ramReadWriteChecking_holds_iff` | iff `ramReadValueEqRamRead ∧ ramWriteValueEqRamReadWrite`. |
| `registersReadWriteChecking_holds_iff` | iff `rdWriteValueEqRegistersReadWrite ∧ rs1ValueEqRegistersRead ∧ rs2ValueEqRegistersRead`. |
| `instructionInputVirtualization_holds_iff` | iff `rightInstructionInputEqSelection ∧ leftInstructionInputEqSelection`. |
| `spartanShift_holds_iff` | iff the five `*EqShift` constraints. |
| `kindCircuitFlags_kindOf` | `kindCircuitFlags (kindOf i) = circuitFlagOrder.filter (opcodeFlag i)` for every instruction. |
| `kindInstructionFlags_kindOf` | The same for `instructionFlag`. |
| `kindLookupTable_kindOf` | `kindLookupTable (kindOf i) = lookupTable i`. |
| `kindRafFlag_kindOf` | `kindRafFlag (kindOf i) = instructionRafFlag i`. |
| `run_meta` check (no name) | `kindOf` maps every Lean instruction to the Jolt kind of the same name, and every Jolt kind except `NoOp` has a Lean instruction. |
| `circuitFlag_iff_generated` | For every bytecode row, `circuitFlag row f` is set iff `f` is in the kind's flags or the stamp's flags. |
| `padding_circuitFlag`, `padding_instructionFlag`, `padding_lookupTable_rafFlag` | The padding branch of `bytecodeCircuitFlag`, `bytecodeInstructionFlag`, `bytecodeLookupTableFlag` and `bytecodeRafFlag` equals Jolt's `NoOp` kind. |
| `ConstraintEquations.generated` | A witness that satisfies `ConstraintEquations` satisfies all 22 generated rows and the four generated relations. |

R1CS rows and their handwritten constraints (all in `JoltConstraints/Constraints/`):

| Row | Jolt name | Lean definition |
| --- | --- | --- |
| 0 | `RamAddrEqRs1PlusImmMinusLookupIfLoadStore` | `ramAddrEqRs1PlusImmMinusLookupIfLoadStore` |
| 1 | `RamAddrEqZeroIfNotLoadStore` | `ramAddrEqZeroIfNotLoadStore` |
| 2 | `RamReadEqRamWriteIfLoad` | `ramReadEqRamWriteIfLoad` |
| 3 | `RamReadEqRdWriteIfLoad` | `ramReadEqRdWriteIfLoad` |
| 4 | `Rs2EqRamWriteIfStore` | `rs2EqRamWriteIfStore` |
| 5 | `LeftLookupZeroUnlessAddSubMul` | `leftLookupZeroIfAddSubMul` |
| 6 | `LeftLookupEqLeftInputOtherwise` | `leftLookupEqLeftInputOtherwise` |
| 7 | `RightLookupAdd` | `rightLookupAdd` |
| 8 | `RightLookupSub` | `rightLookupSub` |
| 9 | `RightLookupEqProductIfMul` | `rightLookupEqProductIfMul` |
| 10 | `RightLookupEqRightInputOtherwise` | `rightLookupEqRightInputOtherwise` |
| 11 | `AssertLookupOne` | `assertLookupOne` |
| 12 | `RdWriteEqLookupIfWriteLookupToRd` | `rdWriteEqLookupIfWriteLookupToRd` |
| 13 | `RdWriteEqPCPlusConstIfWritePCtoRD` | `rdWriteEqPCPlusConstIfJump` |
| 14 | `NextUnexpPCEqLookupIfShouldJump` | `nextUnexpandedPCEqLookupIfShouldJump` |
| 15 | `NextUnexpPCEqPCPlusImmIfShouldBranch` | `nextUnexpandedPCEqPCPlusImmIfShouldBranch` |
| 16 | `NextUnexpPCUpdateOtherwise` | `nextUnexpandedPCUpdateOtherwise` |
| 17 | `NextPCEqPCPlusOneIfInline` | `nextPCEqPCPlusOneIfInline` |
| 18 | `MustStartSequenceFromBeginning` | `mustStartSequenceFromBeginning` |
| 19 | `Product` | `productEqLeftInputMulRightInput` |
| 20 | `ShouldBranch` | `shouldBranchEqLookupOutputMulBranch` |
| 21 | `ShouldJump` | `shouldJumpEqJumpMulNotNextIsNoop` |

The R1CS proofs unfold both sides and close each direction with `linear_combination`.
The relation proofs check `WellFormed` with `decide` and are otherwise definitional, except the `NextIsNoop` claim.
Jolt states that claim as `1 - NextIsNoop = shift(1 - IsNoop)`, which forces `NextIsNoop = 1` at the last cycle; that is the handwritten `else 1`.
The kind proofs are `cases i <;> rfl` over the 91 `JoltISA.Instr` constructors.

## Mismatches

None.
Every handwritten form equals the generated one.

Two Jolt names differ from what their rows say.
Neither is a mismatch, and I changed nothing.

- Row 5 is named `LeftLookupZeroUnlessAddSubMul` (`rv64.rs:145`), but its matrices (`rv64.rs:277-283`) say `(Add + Sub + Mul) · LeftLookupOperand = 0`: the operand is zero *if* the instruction adds, subtracts or multiplies.
  Lean's name `leftLookupZeroIfAddSubMul` (`JoltConstraints/Constraints/LeftLookupZeroIfAddSubMul.lean:14`) matches the math, and the proof `rv64Row05_holds_iff` holds.
  This looks like a naming slip in Jolt that may be worth reporting upstream.
- Row 13 is named `RdWriteEqPCPlusConstIfWritePCtoRD` (`rv64.rs:153`), while its guard is the `Jump` flag.
  Lean calls it `rdWriteEqPCPlusConstIfJump` (`JoltConstraints/Constraints/RdWriteEqPCPlusConstIfJump.lean`).

Jolt has 92 kinds and Lean has 91 instruction constructors.
The extra Jolt kind is `NoOp`, which Lean models as the padding branch of the bytecode reads; the `padding_*` theorems check it.

## Mutation check

I made each change below on its own, rebuilt `Equiv.lean`, and restored the file:

- Row 13's constant `-4` to `-2` in `R1CS.lean`: `rv64Row13_holds_iff` failed (`ring failed`).
- `ADD`'s lookup table from `RangeCheck` to `And` in `KindTables.lean`: `kindLookupTable_kindOf` failed (`rfl` failed).
- The `NextPC` claim's weight from `EqPlusOneOuter` to `EqPlusOneProduct` in `Relations.lean`: `spartanShift_holds_iff` failed.
- `kindOf`'s `FENCE` arm from `.FENCE` to `.NoOp` in `Semantics.lean`: the `run_meta` check failed with `kindOf maps JoltISA.Instr.FENCE to …JoltKind.NoOp`, and two kind theorems failed.

## What stays handwritten, and why

- `Semantics.lean`, as described above.
  It is the part of T3 a reader must trust.
  It is short and every map in it is exhaustive.
- The other 28 of the 62 conjuncts of `ConstraintEquations` (`JoltConstraints/Constraints/All.lean`): the bytecode reads, RAM and register value histories, `ramAddressEqRamRaf`, `ramOutputEqPublicIo`, instruction lookup reads, chunk products, booleanity and Hamming weights.
  They are not R1CS rows and not among `zklean-extractor`'s four relations, so T3 does not generate them.
  Generating them would mean extending the generator to more of Jolt's `unbatched_relation`s; the task did not ask for that.
- The bytecode read constraints still use `JoltMetadata` (`opcodeFlag`, `instructionFlag`, `lookupTable`, `instructionRafFlag`).
  T3 proves those functions equal the generated tables at every instruction, so I did not change the constraints to read the tables directly.
- The kind tables come from one row per kind (rd 5, rs1 6, rs2 7, imm 0, address `0x8000_0000`).
  Jolt's flags are static per kind in `jolt_instruction!`, so the operands should not matter, but the generator does not vary them.

## Proof checks

- No `sorry`, `native_decide`, `decide +kernel`, `bv_decide`, or raised `maxHeartbeats`/`maxRecDepth` in the new files.
- `Equiv.lean` elaborates in about 13 s wall time including imports on an unloaded Mac.
  With the profiler at a 200 ms threshold, the slowest steps are one `simp` (0.46 s) and attribute application (0.38 s).
  No proof takes over 10 s.

## How to run

Regenerate (needs a Jolt checkout at `580084fcf`):

```
JOLT_DIR=/path/to/jolt EXPANSION_PARITY_FEATURES=zicsr-remaining scripts/expansion-parity/run-constraint-gen.sh WORK_DIR
```

Then build the proofs:

```
lake build JoltConstraints.ConstraintGen.Equiv
```

`scripts/expansion-parity/CONSTRAINT-GEN.md` describes the generator, its exit statuses and what to do when Jolt changes.

## CI

`.github/workflows/constraint-generation.yml` checks out Jolt at `JOLT_REV = 580084fcf`, runs the generator, fails if any file under `JoltConstraints/ConstraintGen/Generated/` changes, and builds `JoltConstraints.ConstraintGen.Equiv`.
`JoltConstraints.lean` imports `Equiv`, so the existing `lean` job also builds the proofs.
I ran the generator and the Lean build locally on the Mac; the CI job has not run yet.
