# Coverage ledger

This ledger says which check stands behind each Jolt artifact that jolt-qed models.
It has one row per field of `AllConstraints` and one row per other modelled artifact.
Use it to keep claims of coverage no broader than the checks behind them: a row marked "audit by reading" has no machine check against Jolt.

It is phase T3b of the trust track (`docs/inline-precompiles.md`, section 7).
State: branch `inline/t2-decoder-sweep` (LayerZero-Labs/jolt-qed#56) after `a0372ce`, 2026-11-12.
Sections 4 and 5 record what later PRs in the stack add.
Every PR that adds a check, moves a pin or adds a modelled artifact updates its row here.

## How to read a row

Each row gives the Lean definition, the Jolt source it models, the kind of check, the CI job or test that runs the check, and the Jolt revision checked.

Kinds of check, strongest first:

| Kind | Meaning |
| --- | --- |
| Generated, proved equal | A generator reads Jolt's own code and writes Lean data. CI regenerates the data at the pinned revision and fails on a diff. A Lean theorem proves that the handwritten definition equals the generated data. |
| Generated, diffed | A generator writes the Lean definition itself from Jolt's code. CI regenerates it and fails on a diff, and a Lean test compares it with Jolt's output. No handwritten form exists. |
| Exhaustive test | A test compares Lean with Jolt on every input of a finite domain. |
| Sampled test | A test compares Lean with Jolt on chosen and random inputs. Agreement holds only on the inputs tried. |
| Audit by reading | A person read Jolt's source and wrote or reviewed the Lean. The Lean file cites the source; nothing compares the two by machine. |
| Outside the model | jolt-qed does not model the artifact; the theorems trust it or do not cover it. |

"Jolt revision checked" is the revision the check ran against.
For a CI check it is the job's `JOLT_REV`; the column also gives the revision of the last recorded clean result when that differs.
For an audit it is the `checked` revision that `provenance.toml` records for the Lean file, or "none named" when the file names no published Jolt revision.

Short names used below:

- `3cc6e7bd1`: a16z/jolt#2384 at `3cc6e7bd179900cfad6a052335c32ea1ef749536`, the `JOLT_REV` of every Jolt-facing CI job on this branch and the pin in `provenance.toml`.
- `580084fcf`: a16z/jolt#2384 at `580084fcfad4788ebf48413a92dd640ca090c45f`, the revision of the T1, T2 and T4 reports.
- `a6b6dc717`: a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`, the pin of the inline spec.
- `rv64.rs`: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`rv64_trace_constraints`).
- `claims/`: `crates/jolt-claims/src/protocols/jolt/`.
- `stage5/`: `crates/jolt-verifier/src/stages/stage5/`.

## 1. CI jobs

| Job | Workflow | What it checks | Jolt revision | Result recorded |
| --- | --- | --- | --- | --- |
| `expansion-parity` | `.github/workflows/expansion-parity.yml` | T1: every non-inline expansion and its row metadata against Lean; the generated inline rows regenerated and diffed; the inline round trip; a mutation check | `3cc6e7bd1` | Clean at `580084fcf` (`reports/2026-11-11-expansion-parity.md`, `reports/2026-11-11-inline-rows.md`). At `3cc6e7bd1` the run on `spec/inline-precompiles` at `5c7556a` failed on the generated row headers, which `2d30091` regenerated; no run at `3cc6e7bd1` had finished when this ledger was written. |
| `decoder-sweep` | `.github/workflows/decoder-sweep.yml` | T2: `joltDecode` and `joltUncompress` against `decode.rs` | `3cc6e7bd1` | Clean at `580084fcf` (`reports/2026-11-11-decoder-sweep.md`; CI run on `f76aafe`). No CI run at `3cc6e7bd1` had finished when this ledger was written. |
| `constraint-generation` | `.github/workflows/constraint-generation.yml` | T3: regenerates the R1CS rows, four relations and kind tables, fails on a diff, builds the equality proofs | `3cc6e7bd1` | Clean at `3cc6e7bd1`, run locally (`reports/2026-11-12-t3-constraint-generation.md`). No CI run had finished when this ledger was written. |
| `lookup-tables` | `.github/workflows/lookup-tables.yml` | T4: sampled `materialize_entry` vectors against the Lean tables' computable twin | `3cc6e7bd1` | Clean at `580084fcf` (`reports/2026-11-11-lookup-table-vectors.md`). CI passed at `3cc6e7bd1` on `8e4875f` and `5306348`. |
| `build` | `.github/workflows/lean.yml` | `lake build` (including `JoltConstraints.ConstraintGen.Equiv`); `lake build JoltAudit`, which fails if a headline theorem uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`; when a PR touches the Sail model or its inputs, regenerates `LeanRV64D/` and requires a byte-for-byte match | none | Passed on the PR branches below this one (for example `spec/inline-precompiles` at `5c7556a`); no run on this branch had finished when this ledger was written. |
| `provenance` | `.github/workflows/provenance.yml` | `scripts/check-provenance.py`: every Lean file has a manifest entry; no new local paths, fork citations or unlisted revisions | pin `3cc6e7bd1` | Passed at `a0372ce`. |
| `hygiene` | `.github/workflows/provenance.yml` | `scripts/check_hygiene.py`: `sorry`, `native_decide`, `decide +kernel`, `bv_decide`, raised limits and axioms against `scripts/hygiene-baseline.toml` | none | Passed at `a0372ce`. The nine `decide +kernel` proofs copied from EthLib are baselined. |
| `comparator (untested)` | `.github/workflows/provenance.yml` | Replays the frozen headline statements in `ci/comparator/` with `lake comparator` | none | Never passed; failures are warnings only (`ci/comparator/README.md`). |
| `ethlib-copies` | `.github/workflows/ethlib-copies.yml` | `scripts/check-ethlib-copies.sh`: the hash specifications in `JoltBytecode/Inlines/` equal the EthLib commit they were copied from | EthLib `5310b3e` | Passes on the PR branches that carry the copies. |

Local tests that no CI job runs:

| Test | What it checks | Jolt revision | Report |
| --- | --- | --- | --- |
| `scripts/inline-kat/` with `JoltTests/InlineKat/` | Jolt's tracer on the five hash inlines against the EthLib specifications: 354 cases | `a6b6dc717` | `reports/2026-11-11-inline-known-answer-hashes.md` |
| `scripts/secp256k1-kat/` with `JoltTests/Secp256k1Kat/` | Lean transcriptions of Jolt's secp256k1 advice functions against Jolt's Rust | `a6b6dc717` | `reports/2026-11-11-secp256k1-advice-transcriptions.md` |
| `scripts/expansion-parity/gen_frame_instances.py --check` | `JoltBytecode/Inlines/FrameInstances.lean` equals the output of its generator on the generated rows | rows at `3cc6e7bd1` | `reports/2026-11-11-inline-frame-statement.md` |
| `scripts/difftest/` | Jolt's tracer against Sail's C++ emulator on real binaries. Lean takes no part, so it checks no Lean definition. | as built | `scripts/difftest/README.md` |

## 2. Fields of `AllConstraints`

`AllConstraints` (`JoltConstraints/Constraints/All.lean`) is a `ConstraintContext` together with the 63 conjuncts of `ConstraintEquations`.
Each conjunct's Lean definition has the conjunct's name and lives in `JoltConstraints/Constraints/<Name>.lean` with the first letter capitalised.

### The context

| Field | Lean | Jolt source | Check | CI or test | Jolt revision |
| --- | --- | --- | --- | --- | --- |
| `context` (bytecode, initial RAM, public I/O, entry slot) | `ConstraintContext` (`JoltConstraints/constraint_context.lean`) | `crates/jolt-verifier/src/config.rs`, `crates/jolt-verifier/src/verifier.rs` | Audit by reading | none | `5def437f2` |

The bytecode the context names comes from `expand_instruction` and Jolt's preprocessing (section 3).

### The 22 R1CS rows

Generated, proved equal (T3).
`JoltConstraints/ConstraintGen/Generated/R1CS.lean` holds the rows of `rv64_trace_constraints`, and `JoltConstraints/ConstraintGen/Equiv.lean` proves `rv64RowNN_holds_iff` for each.
CI: `constraint-generation` regenerates and diffs the data and builds `Equiv`; `build` builds `Equiv` too.
Jolt revision: `3cc6e7bd1`.
The trusted bridge between generated names and witness columns is `JoltConstraints/ConstraintGen/Semantics.lean`, which a reviewer reads in full.

| Row | Field | Jolt name in `rv64.rs` | Completeness |
| --- | --- | --- | --- |
| 0 | `ramAddrEqRs1PlusImmMinusLookupIfLoadStore` | `RamAddrEqRs1PlusImmMinusLookupIfLoadStore` | `sorry`, waits on a16z/jolt#1949 |
| 1 | `ramAddrEqZeroIfNotLoadStore` | `RamAddrEqZeroIfNotLoadStore` | proved |
| 2 | `ramReadEqRamWriteIfLoad` | `RamReadEqRamWriteIfLoad` | proved |
| 3 | `ramReadEqRdWriteIfLoad` | `RamReadEqRdWriteIfLoad` | proved |
| 4 | `rs2EqRamWriteIfStore` | `Rs2EqRamWriteIfStore` | proved |
| 5 | `leftLookupZeroIfAddSubMul` | `LeftLookupZeroUnlessAddSubMul` | proved |
| 6 | `leftLookupEqLeftInputOtherwise` | `LeftLookupEqLeftInputOtherwise` | proved |
| 7 | `rightLookupAdd` | `RightLookupAdd` | `sorry`, waits on a16z/jolt#1949 |
| 8 | `rightLookupSub` | `RightLookupSub` | proved |
| 9 | `rightLookupEqProductIfMul` | `RightLookupEqProductIfMul` | proved |
| 10 | `rightLookupEqRightInputOtherwise` | `RightLookupEqRightInputOtherwise` | `sorry`, waits on a16z/jolt#1949 |
| 11 | `assertLookupOne` | `AssertLookupOne` | proved under a condition on equality-assertion operands |
| 12 | `rdWriteEqLookupIfWriteLookupToRd` | `RdWriteEqLookupIfWriteLookupToRd` | proved |
| 13 | `rdWriteEqPCPlusConstIfJump` | `RdWriteEqPCPlusConstIfWritePCtoRD` | proved |
| 14 | `nextUnexpandedPCEqLookupIfShouldJump` | `NextUnexpPCEqLookupIfShouldJump` | proved |
| 15 | `nextUnexpandedPCEqPCPlusImmIfShouldBranch` | `NextUnexpPCEqPCPlusImmIfShouldBranch` | proved, assuming the trace's last row is a jump |
| 16 | `nextUnexpandedPCUpdateOtherwise` | `NextUnexpPCUpdateOtherwise` | proved |
| 17 | `nextPCEqPCPlusOneIfInline` | `NextPCEqPCPlusOneIfInline` | proved |
| 18 | `mustStartSequenceFromBeginning` | `MustStartSequenceFromBeginning` | proved |
| 19 | `productEqLeftInputMulRightInput` | `Product` | proved |
| 20 | `shouldBranchEqLookupOutputMulBranch` | `ShouldBranch` | proved |
| 21 | `shouldJumpEqJumpMulNotNextIsNoop` | `ShouldJump` | proved |

The completeness column records the honest-witness direction (`JoltConstraints/Completeness/`, `JoltConstraints/constraints.md`).
It does not affect soundness: no soundness or whole-run theorem uses these `sorry`s.

### The 12 claims of the four relations

Generated, proved equal (T3).
`JoltConstraints/ConstraintGen/Generated/Relations.lean` holds the four relations that `extracted_claims` in `zklean-extractor/src/sumchecks.rs` lists; `Equiv.lean` proves one `*_holds_iff` theorem per relation.
CI: `constraint-generation` and `build`.
Jolt revision: `3cc6e7bd1`.
All twelve completeness proofs are complete.

| Field | Relation (`unbatched_relation` in) | Theorem |
| --- | --- | --- |
| `ramReadValueEqRamRead` | `claims/relations/ram/read_write_checking.rs` | `ramReadWriteChecking_holds_iff` |
| `ramWriteValueEqRamReadWrite` | same | same |
| `rdWriteValueEqRegistersReadWrite` | `claims/relations/registers/read_write_checking.rs` | `registersReadWriteChecking_holds_iff` |
| `rs1ValueEqRegistersRead` | same | same |
| `rs2ValueEqRegistersRead` | same | same |
| `leftInstructionInputEqSelection` | `claims/relations/instruction/input_virtualization.rs` | `instructionInputVirtualization_holds_iff` |
| `rightInstructionInputEqSelection` | same | same |
| `nextUnexpandedPCEqShift` | `claims/relations/spartan/shift.rs` | `spartanShift_holds_iff` |
| `nextPCEqShift` | same | same |
| `nextIsVirtualEqShift` | same | same |
| `nextIsFirstInSequenceEqShift` | same | same |
| `nextIsNoopEqShift` | same | same |

### The other 29 conjuncts

Audit by reading.
None of these is an R1CS row or one of the extractor's four relations, so T3 does not generate them.
No CI job compares them with Jolt; `build` only checks that the proofs about them still hold.

| Field | Jolt source cited | Jolt revision | Notes |
| --- | --- | --- | --- |
| `ramAddressEqRamRaf` | `crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs` | none named | |
| `ramOutputEqPublicIo` | `claims/relations/ram/output_check.rs` | none named | |
| `ramValEqInitialPlusPrefixRamInc` | `claims/relations/ram/val_check.rs` | none named | Completeness `sorry`: false until the termination-word RAM history bug is fixed (`bug-report/ram-val-termination/README.md`). |
| `ramValFinalEqInitialPlusRamInc` | `claims/relations/ram/val_check.rs` | none named | Completeness `sorry`: false until a16z/jolt#1951 item 1 is fixed. |
| `lookupOutputEqInstructionReadRaf` | none cited | none named | Gap: the file cites no Jolt path. Its siblings cite `stage5/instruction_read_raf.rs`. |
| `leftLookupOperandEqInstructionRaf` | `stage5/instruction_read_raf.rs` | none named | |
| `rightLookupOperandEqInstructionRaf` | `stage5/instruction_read_raf.rs` | none named | |
| `instructionAddressCanonical` | `claims/geometry/instruction.rs` (`CANONICAL_INSTRUCTION_ADDRESS`), `crates/jolt-akita/src/adapters.rs`, `stage5/instruction_read_raf.rs` | `c97e93004` | Applies only below characteristic `2^128` (the Akita build). |
| `registersValEqPrefixRdInc` | `claims/relations/registers/val_evaluation.rs` | none named | |
| `pcEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `unexpandedPCEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `immEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `opFlagsEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | The per-kind circuit flags it reads are generated and proved equal (section 3). The read itself is audited. |
| `instructionFlagsEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | The per-kind instruction flags are generated and proved equal (section 3). |
| `rs1RaEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `rs2RaEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `rdWaEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `lookupTableFlagEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | The per-kind lookup table is generated and proved equal (section 3). |
| `instructionRafFlagEqBytecodeRead` | `claims/geometry/bytecode.rs` | `5def437f2` | The per-kind RAF flag is generated and proved equal (section 3). |
| `bytecodeRaAtEntryEqOne` | `claims/geometry/bytecode.rs` | `5def437f2` | |
| `instructionRaChunkBooleanity` | `claims/geometry/booleanity.rs` | none named | |
| `bytecodeRaChunkBooleanity` | `claims/geometry/booleanity.rs` | none named | |
| `ramRaChunkBooleanity` | `claims/geometry/booleanity.rs` | none named | |
| `ramHammingWeightBooleanity` | `claims/relations/ram/hamming_booleanity.rs` | none named | |
| `ramRaEqChunkProduct` | `claims/geometry/ram.rs` | none named | |
| `instructionRaEqChunkProduct` | `claims/geometry/instruction.rs` | none named | |
| `instructionRaChunkHammingWeight` | `claims/geometry/claim_reductions/hamming_weight.rs` | none named | |
| `bytecodeRaChunkHammingWeight` | `claims/geometry/claim_reductions/hamming_weight.rs` | none named | |
| `ramRaChunkHammingWeight` | `claims/geometry/claim_reductions/hamming_weight.rs` | none named | |

Count: 22 rows and 12 claims (34 conjuncts) are generated and proved equal; 29 are audited.

## 3. Other modelled artifacts

| Artifact | Lean | Jolt source | Check | CI or test | Jolt revision | Gaps |
| --- | --- | --- | --- | --- | --- | --- |
| Built-in expansions | `SourceInstruction.expand` (`JoltConstraints/expansions.lean`), `expand_instruction` and `stamp_sequence` (`JoltConstraints/program.lean`), `JoltBytecode/JoltISA/ExpansionsAutomated.lean`, `JoltBytecode/JoltISA/Expansions/*.lean` | `crates/jolt-program/src/expand/` | Sampled test (T1): Jolt's 360 golden inputs, aliased operands, `rd = x0`, `rs1 = x0`, random operands and immediates, each native kind once; every row field compared | `expansion-parity` | `3cc6e7bd1`; last clean result `580084fcf` | T6 (symbolic recipes, which would make this a generated check) is not done. The header of `ExpansionsAutomated.lean` says "generated", but the generator at the pin cannot reproduce it (`JoltConstraints/model_review.md`). |
| System and CSR sequences | `JoltBytecode/JoltISA/Expansions/System.lean`, `JoltBytecode/JoltISA/SystemCSR.lean` | `crates/jolt-program/src/expand/control_flow/` | Sampled test (T1): ECALL, EBREAK, MRET, and the six Zicsr kinds on each of the six modelled CSRs with chosen `rd` and `rs1` values | `expansion-parity` | `3cc6e7bd1`; last clean result `580084fcf`. `provenance.toml` records `c336a6da7` for `System.lean` and no revision for `SystemCSR.lean`. | Lean transcribes a16z/jolt#2384, which is not on Jolt `main`. T6 is meant to bring these under generated data. |
| Per-kind circuit flags, instruction flags, lookup table, RAF flag | `JoltConstraints/metadata.lean` (`opcodeFlag`, `instructionFlag`, `lookupTable`, `instructionRafFlag`, `circuitFlag`) | `jolt_instruction!` in `crates/jolt-riscv`, `InstructionLookupTable` in `crates/jolt-lookup-tables`, `InstructionRafFlag::extract` in `crates/jolt-witness` | Generated, proved equal (T3) for all 91 `JoltISA.Instr` constructors and the `NoOp` padding row; also compared on every T1 row | `constraint-generation`, `expansion-parity` | `3cc6e7bd1` | The kind tables come from one operand choice per kind. The generator checks over 4,108 sequence stamps that the stamp adds the same flags for every count. |
| Inline rows (27 registered inlines) | `JoltBytecode/Inlines/Generated/*.lean` | `expand_instruction_with_provider` with `TracerInlineExpansionProvider`, `jolt-inlines/` | Generated, diffed. The driver also recomputes Jolt's inline fixture hashes; the Lean round trip compares 216 fixture records and 16,308 template instantiations | `expansion-parity` | `3cc6e7bd1` (file headers); last clean round trip `580084fcf` | |
| Inline frame instances | `JoltBytecode/Inlines/FrameInstances.lean`; the frame lemma `frame_of_run` in `JoltBytecode/Inlines/Frame.lean` | generated rows | Generated from the generated rows; the frame lemma is proved | `gen_frame_instances.py --check`, local only | rows at `3cc6e7bd1` | No CI job runs the `--check`. |
| Decoder | `joltDecode` (`JoltBytecode/Decode/Jolt.lean`) | `crates/jolt-program/src/image/decode.rs` | Sampled test with an exhaustive Rust-side argument (T2): 2,250,752 words over every selector class; the driver checks all 2^30 words with low bits `0b11` to show that the sample determines Jolt's result. That Lean's result has the same structure is argued by reading `joltDecode`, not checked. | `decoder-sweep` | `3cc6e7bd1`; last clean result `580084fcf`. `provenance.toml` records `c336a6da7`. | `joltDecode` returns `none` for opcodes `0x0B`, `0x2B` and `0x5B` (inlines and Jolt's custom instructions). The `field-inline` decoder for `0x7B` is not exercised and not modelled. |
| Uncompressor | `joltUncompress` (`JoltBytecode/Decode/Jolt.lean`), `JoltBytecode/Decode/Compressed.lean` | `crates/jolt-riscv/src/uncompress.rs` | Exhaustive test (T2): all 65,536 16-bit parcels | `decoder-sweep` | `3cc6e7bd1`; last clean result `580084fcf` | |
| ELF loader | `Rv64ProgramImage.DecodedFrom` and `ElfSections.layout?` (`JoltConstraints/WholeRun/Elf.lean`); `ImageDecoded` (`JoltConstraints/WholeRun/Decoded.lean`) is derived from it by proof | `decode_elf`, `merge_ranges`, `decode_text_section` in `crates/jolt-program/src/image/elf.rs` | Audit by reading | none | `c336a6da7` | The sections given to `DecodedFrom` are trusted to be what the `object` crate parses (outside the model). |
| Lookup tables (55) | `lookupTableEntry` (`JoltConstraints/lookup_table.lean`), `LookupTableKind` (`JoltConstraints/witness.lean`) | `LookupTableKind::materialize_entry` in `crates/jolt-lookup-tables` | Sampled test (T4): 162,551 (table, index) pairs at edge and seeded random indices. Lean proves the tested twin equal to the tables (`lookupTableEntry_eq_twin`) | `lookup-tables` | `3cc6e7bd1` (passed in CI); the lookup-table crate is the same at `580084fcf` and `a6b6dc717` | Agreement holds only at the sampled indices. The Lean file cites `c67035705` and, for `VirtualXORROTL1`, a fork. |
| Semantics of Jolt's rows (tracer) | `execProgram` (`JoltBytecode/JoltISA/Semantics.lean`), `MemoryAccess.lean`, `RegisterAccess.lean`, `DeviceMemory.lean`, `HostIO.lean`, `AdviceTape.lean` under `JoltBytecode/JoltISA/` | `tracer/src/instruction/`, `tracer/src/emulator/` | Audit by reading | none | `DeviceMemory.lean`: `5def437f2`; the others name no published revision | Difftest compares Jolt's tracer with Sail, not with these definitions. |
| Division and remainder advice | `SourceInstruction.honestTracerAdvice` (`JoltConstraints/honest_trace.lean`) | `tracer/src/instruction/div.rs`, `rem.rs` and the unsigned and word forms | Audit by reading | none | `5def437f2` | |
| secp256k1 advice functions | `joltAdvice` (`JoltBytecode/Inlines/Secp256k1/Advice.lean`), `JoltBytecode/Inlines/Secp256k1/Spec.lean` | `jolt-inlines/secp256k1/` | Sampled test (I0(d)) on random and edge-case inputs, including edge-case GLV scalars | `secp256k1-kat`, local only | `a6b6dc717` | Not in CI and not rerun at `3cc6e7bd1`. The soundness theorems quantify over every inline advice word (decision D2) and do not use these functions; the per-inline completeness theorems on LayerZero-Labs/jolt-qed#52 do. |
| Hash specifications | `JoltBytecode/Inlines/Sha256/`, `Keccak256/`, `Blake2b/` | EthLib `5310b3e`; the inlines in `jolt-inlines/` | Copies diffed against EthLib in CI. Sampled test (I0(b)) of Jolt's tracer against the copies: 354 cases | `ethlib-copies`; `inline-kat`, local only | EthLib `5310b3e`; tracer at `a6b6dc717` | The tracer comparison is not in CI and not rerun at `3cc6e7bd1`. |
| Memory layout and device | `MemoryLayout`, `JoltDevice` (`JoltBytecode/JoltISA/JoltDevice.lean`); `JoltConstraints/Constraints/MemoryLayout.lean` | `common/src/jolt_device.rs`, `common/src/constants.rs`, `tracer/src/lib.rs` | Audit by reading | none | `8bbb23578` (`JoltDevice.lean`), `5def437f2` (`MemoryLayout.lean`) | |
| Bytecode preprocessing and padding | `JoltInstance`, preprocessing in `JoltConstraints/program.lean` | `crates/jolt-program/src/preprocess/`, `crates/jolt-host/src/program.rs` | Audit by reading. The `NoOp` padding row is proved equal to Jolt's `NoOp` kind (T3 `padding_*` theorems), and T1 checks that no expansion emits a `NoOp` row | `constraint-generation`, `expansion-parity` for the padding facts | `8bbb23578`; padding facts at `3cc6e7bd1` | |
| Witness types | `WitnessType`, `WitnessParams` (`JoltConstraints/witness.lean`) | `claims/geometry/bytecode.rs`, `claims/geometry/dimensions.rs`, `crates/jolt-witness/src/`, `common/src/constants.rs` | Audit by reading; T5 review (section 4) | none | `c67035705` | |
| Prover configuration and verifier sizes | `JoltConstraints/prover_config.lean`, `JoltConstraints/verifier_sizes.lean` | `crates/jolt-prover/src/config.rs`, `crates/jolt-program/src/execution/trace.rs`, `crates/jolt-program/src/preprocess/ram.rs`, `crates/jolt-dory/src/scheme.rs` | Audit by reading | none | `5def437f2` | |
| RISC-V reference model | `LeanRV64D/` | riscv/sail-riscv (fork `abiswas3/sail-riscv` at `266473f8`), compiled by rems-project/sail `2ae2199f` | Generated, diffed: CI regenerates the model and requires a byte-for-byte match when a PR touches it or its inputs | `build` | not Jolt; inputs pinned in `sail-import/PROVENANCE.toml` | The Sail compiler is trusted to preserve the model's meaning. |

### Outside the model

- Jolt's verifier itself: sumchecks, reductions and the polynomial commitment scheme. `AllConstraints` checks the constraint equations directly on the whole witness.
- The tracer's own decoder. Difftest exercises it; nothing compares it with Lean.
- Jolt's `field-inline` instructions (opcode `0x7B`) and committed-program mode.
- The `object` crate's ELF parsing, and the claim that Jolt's preprocessing and verifier key were built from the program in the instance.
- The SDK guest code that calls the inlines (`docs/inline-precompiles.md`, section 12).

## 4. Untrusted advice as field words (T5, LayerZero-Labs/jolt-qed#58)

T5 is on branch `inline/i1b-advice` (LayerZero-Labs/jolt-qed#58), not on this branch.
Its review is `reports/2026-11-12-witness-column-typing.md` on that branch, against Jolt `a6b6dc717`.

| Input of `AllConstraints` | Lean on #58 | Jolt source | Check | Jolt revision | Status |
| --- | --- | --- | --- | --- | --- |
| Witness columns | `WitnessType F params`: every column is a field element | `claims/ids.rs` | Audit by reading | `a6b6dc717` | No gap: Jolt's verifier knows only a field element for each. |
| Untrusted advice | `AllConstraints joltInstance untrustedAdvice witness` with `untrustedAdvice : Nat → F`; `committedInitialValue` places the words in the initial RAM | `ram_val_check_advice_block` in `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs` | Audit by reading; the reduction to the byte relation is proved (`onBytes_of_allConstraints`, `allConstraints_of_onBytes`) | `a6b6dc717` | Fixed on #58. |
| Size of the untrusted-advice block | Premise `JoltInstance.UntrustedAdviceBlockFits` (`adviceBlockFits` of `JoltInstance.soundness`) | `MemoryLayout::new` in `common/src/jolt_device.rs`, `tracer/src/lib.rs` | Audit by reading | `a6b6dc717` | Temporary premise; a Jolt fix is proposed. |
| Trusted advice | `JoltInstance.trusted_advice`, bytes | `ram_val_check.rs` | Audit by reading | `a6b6dc717` | Gap, not fixed: correct only if the trusted party commits to packed bytes. |
| Inline advice | `JoltPrivateInputs.inline_advice` (I1b); the relation ignores it (`ConstraintContext.withInlineAdvice`) | `VirtualAdvice` rows of the secp256k1 inlines | Proved irrelevant to the relation | n/a | No gap. |
| Program image in committed-program mode | public `JoltInstance.program` | `ProgramImageInit`, `ProgramBytecode` commitments | Outside the model | n/a | Out of scope. |

## 5. Inline artifacts on later PRs

These rows describe branches stacked on LayerZero-Labs/jolt-qed#44.
They use the same CI jobs as this branch, with `JOLT_REV` `3cc6e7bd1`, but not the T2, T3, T4 or T7 jobs, which only this branch has.

| Artifact | Lean | PR | Check | Jolt revision | Gaps |
| --- | --- | --- | --- | --- | --- |
| Supported inline keys and encodings | `InlineKey` (`JoltBytecode/Inlines/Keys.lean`) and `JoltConstraints/inline_rows_ok.lean` | LayerZero-Labs/jolt-qed#55 | Generated by `scripts/expansion-parity/gen_inline_keys.py` from the driver's output | `3cc6e7bd1` (file header) | No CI job runs `gen_inline_keys.py --check`. |
| Inline rows in the source language | `SourceInstruction.inline`; its expansion is `InlineKey.expandRows` (`JoltConstraints/expansions.lean`) | LayerZero-Labs/jolt-qed#55 | The expansion takes the rows from the generated files, with no handwritten rows. The `rd = x0` rewrite in `expandRows` is audited against `materialize_inline` | `a6b6dc717` (citation); rows at `3cc6e7bd1` | |
| Inline row soundness and completeness | per-inline theorems over the generated rows | LayerZero-Labs/jolt-qed#52 (secp256k1), #55 (hashes) | Proved in Lean against the specifications of section 3 | rows at `3cc6e7bd1` | |
| Inline encodings in the ELF relation | `inlineEncodingOf`, the fourth `RowFromParcel` conjunct (`JoltConstraints/WholeRun/Elf.lean`) | LayerZero-Labs/jolt-qed#67 | Audit by reading of `decode.rs` (`format_inline_operands`) | as cited in `Keys.lean` | T2 classifies `0x0B` and `0x2B` as Jolt-only; it does not compare the combined decode and registration pipeline. |
| Platform step for inlines | `PlatformStep`, `InlineKey.Spec`, `InlineKey.Pre` (`JoltConstraints/WholeRun/Platform.lean`, `InlineContract.lean`) | LayerZero-Labs/jolt-qed#67 | Specification-level: the step runs each inline by its Lean specification (decision D1) | n/a | No theorem yet builds an honest trace with Jolt's inline advice (R4 completeness). |

## 6. Open gaps

- T6 is not done: the built-in and system expansions are checked only on T1's samples, and `ExpansionsAutomated.lean` cannot be regenerated.
- 29 of the 63 conjuncts of `ConstraintEquations` are audited, not generated (section 2).
- Five completeness proofs are `sorry`: three wait on a16z/jolt#1949, one on the termination-word RAM history bug, one on a16z/jolt#1951 item 1.
- The ELF loader, the tracer semantics, the memory layout, preprocessing and the witness types are audited only.
- The hash and secp256k1 known-answer tests and the frame and key generator checks run only locally, and the known-answer tests ran at `a6b6dc717`, not `3cc6e7bd1`.
- Many audited files name no published Jolt revision, or an older one than the pin (`provenance.toml` notes and `[[known]]` baseline).
- The comparator gate has never passed.
- Trusted advice is still modelled as bytes (section 4).
