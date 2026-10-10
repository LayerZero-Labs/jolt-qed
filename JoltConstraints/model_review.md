---
title: Jolt model in Lean, open issues
updated: 2026-10-10
rust: experiment/pr2039-sc; 43cc043 plus PR #2039 at 2a924239 (not the main model)
---

# Open issues

The final theorem is `HonestTrace.allConstraints_rust_sizes` (`Completeness/All.lean`):
it claims the modeled verifier checks and constraints hold at the sizes Rust's prover
picks, against the public I/O the verifier checks. This still depends on the `sorry`s
under "Proofs owed"; it is not a completed completeness proof.
Everything it rests on that is not proved is listed here.

**Source-language scope.** Completeness and soundness cover programs represented
by `SourceInstruction`: the modeled RISC-V instructions and the listed Jolt custom
instructions at opcode `0x5B`. Jolt's inline/precompile opcodes `0x0B` and `0x2B`,
including the SHA-256 and Keccak inlines, are outside this type. A guest using
these inlines is outside the theorems' scope by construction. This existing type
restriction is recorded in [`expansion_helpers.lean`](./expansion_helpers.lean);
it is not an additional premise or a verifier check.

`AllConstraints joltInstance privateInputs witness` binds the constraint data to
the instance through `ConstraintContext` (`constraint_context.lean`). Bytecode,
initial RAM, public I/O and the entry slot cannot be chosen independently of
these inputs. Trusted advice is part of the instance; Jolt's verifier holds a
commitment to it, and we model its contents directly. Untrusted advice is
prover-chosen. Both contribute to initial RAM without being public I/O.
The context also checks the instance's input/output sizes and lowest address,
the padded trace limit, the bytecode domain, and the verifier's RAM bounds.
`ConstraintEquations` is the underlying equation bundle over those data.

## Upstream issues

Jolt issues that stop a completeness proof. If one is still open when the main proofs
pass, escalate it.

| Issue | What breaks | In our model |
|---|---|---|
| [#1949](https://github.com/a16z/jolt/issues/1949) | A load/store address that wraps past 2^64 breaks the RAM-address constraint | (01) stays `sorry`; a fix PR is announced in the issue |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | A run that does not panic and never stores to the termination word: an SDK guest exiting through `platform_exit` or `std::process::exit`, or a bare ELF that reaches `j .` first. The tracer records no write to the word, but `jolt-witness`'s `final_ram_state` sets its `RamValFinal` slot to 1 from the panic flag alone, while initial RAM and the increments give 0 | (38) stays `sorry`. The fix proposed in the issue changes only the SDK's exit paths, so a bare ELF stays unprovable |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | A store to the termination word is recorded but the device ignores it, so a later load reads 0 (`bug-report/ram-val-termination/`) | (37) stays `sorry`; `HonestTrace.matches_outputs` leaves the termination word out |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the prover panics | such runs have no `HonestTrace.prover_config` (WARNING) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | FIXME: `HonestTrace.prover_config` uses the fixed formula `touched + 1`, so Lean differs from Rust here. Blocks the upper half of the verifier's RAM-size check (`ramSizeBounds`, via `HonestTrace.witness_params_ram_bounds`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | The emulator loads only some ELF section kinds into RAM, preprocessing loads every section | assumed to agree: `initialRam` TODO in `program.lean` |

## Device-memory soundness findings

The [Layer 5b audit](../methods/soundness.md#layer-5b-one-execution-step), at
Jolt revision `43cc043332762034b5f65379441576e06e7a3890`, distinguishes three
cases. Termination ignores writes (#1950/#1951 item 2); panic sets a flag
regardless of the first byte stored and ignores writes to the other bytes
(B6); input/advice stores are rejected by the MMU. The Lean execution model
matches those behaviours. RAM-table history alone does not establish them.

**Input/advice stores:** the candidate in
[#2041](https://github.com/a16z/jolt/issues/2041) now has a reproduction reported
by Ari in [#2044](https://github.com/a16z/jolt/issues/2044). At `00508a09`, the
tracer aborts at the input store, while a modified tracer records stores into
all three read-only regions and the unchanged verifier accepts outputs 7, 9
and 11 in clear/Dory mode. The report and patch have been read, but this session
has not independently rerun them. This contradicts soundness relative to the
tracer's execution semantics if the reported verification is reproduced.

Ari approved the broader temporary `TracerAddressChecks` premise. It supplies
`Mmu.effective_address_ok` for the next attempted LD or SD after an initialized
relaxed prefix with honest internal runtime advice, even if the attempt would
abort. It matches the tracer's starting-address check for RAM and eight byte
checks for device memory. No witness columns appear in the predicate.

The plan separately records four further candidates: stores at zero, the I/O
padding gap, stores to the stack canary, and loads/stores at or above `heap_end`.
No complete satisfying witness or verifier reproduction exists for those cases
in this work; #2044 does not establish them. Each has its own next check in the
plan. The FIXME links #2044 and these candidates and requires narrowing or
removal as each is resolved and proved. This replaces the input/advice-only
restriction. Alignment, unsupported peripheral dispatch, panic/termination
value agreement and stopping remain separate obligations; address assertions
alone do not establish successful execution.

## Assumptions

Premises or fields of the final theorem, with their source or reason below.

| Assumption | Where | Why |
|---|---|---|
| The field's characteristic exceeds `2^128` | `JoltInstance.soundness`, premise `charAbove2pow128` | Ari, 2026-10-10: the base relation must distinguish full 128-bit lookup addresses. BN254 satisfies this; model Akita's field and extra address guard separately. PCS security is outside this work |
| No source row is SC.W or SC.D (temporary) | `Rv64ProgramImage.NoStoreConditional`, soundness premise `noStoreConditional` | Ari, 2026-10-10: exclude the SC advice mismatch (#2037) while proving the remaining cases; remove this restriction after the constraints and model are fixed |
| Every attempted LD/SD passes the tracer's address assertions (temporary) | `JoltInstance.TracerAddressChecks` in `Soundness/Layer5/MemoryAccessRestriction.lean`, soundness premise `tracerAddressChecks` | Approved by Ari for #2044 and four separate candidates: zero stores, the I/O gap, canary stores and accesses at or above `heap_end`. Quantifies over every private input and relaxed prefix with honest internal runtime advice; checks the next attempted row without assuming it succeeds. Uses `Mmu.effective_address_ok` at the start for RAM, every byte for devices. FIXME to narrow or remove as each case is resolved and proved; not a verifier check |
| The PC does not wrap past 2^64 | `Rv64ProgramImage.NextPCNoWrap` | a16z, 2026-10-07: such an ELF is illegal |
| The maximum padded RAM region satisfies `lowest + 8 * maxRamSize ≤ 2^64` | `JoltInstance.RamRegionFits` in `Soundness/Layer3/Layout.lean`, soundness premise `ramRegionFits` | Approved by Ari, 2026-10-10, replacing the run-based address restriction. With the verifier's RAM-size check, all eight bytes of each in-domain word fit. The signed sum is then recovered from satisfying constraints, including address zero. NOTE: to confirm with a16z. This is an instance restriction, not a verifier check |
| A program is never empty: its memory image loads at least one byte | `Rv64ProgramImage.ImageNonempty` (premise `imageNonempty`) | a16z, by phone, 2026-10-08. Rust's prover does not reject an empty ELF: it traces it and picks `ram_K = 4`, and only Rust's verifier rejects that size (`InvalidRamK`, minimum 16 with a 64-byte output region; `bug-report/verifier-ram-minimum/`) |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | `JoltInstance.CodeUnchanged`, over every `ValidRun`; honest traces get it from `HonestTrace.code_unchanged`. Completeness does not use it | a16z, 2026-10-07 |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | ASSUMPTION in `finalRamWord` | a16z, 2026-10-07 |
| No spoil assert fails | `HonestTrace.SpoilAssertsPass` | by design: a failing spoil assert is meant to leave no proof |
| Rust's prover accepts the run | `HonestTrace.prover_config = some config` | by design for its own checks (last row a jump, #1968; length limit); also excludes #1951 item 3 |

## Proofs owed

Sorried theorems behind the final theorem; `#print axioms` shows `sorryAx` through them.

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` | false until #1949 is fixed |
| (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` | false until #1950 is fixed |
| (38) `honestWitness_ramValFinalEqInitialPlusRamInc` | false until #1951 item 1 is fixed |
| `HonestTrace.witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean`) | The empty program is excluded by the `ImageNonempty` assumption. Lower half: proved once the minimum computes successfully; still to prove that both bounds compute successfully. Upper half: false until #1951 item 4 is fixed, because the verifier's maximum rounds the word count down |

## Gaps in our model

- **Trusted base.** The semantics of each Jolt instruction are translated from Rust by
  hand. Native RV64 instructions are proved against Sail
  (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove
  against.
- **Not modeled.** The Akita build's 4096-cycle padding floor (`prover_config` uses the
  default build's 256), program commitments (BytecodeChunk, ProgramImageInit), and
  TrustedAdvice/UntrustedAdvice witness columns and commitment protocols. Trusted
  advice contents are modeled directly as part of the instance.
- **Akita soundness scope.** The base constraint relation also omits Akita's
  instruction-address canonicality guard, as recorded in `constraints.md`.
  At `43cc043332762034b5f65379441576e06e7a3890`, the `akita` feature enables
  `CANONICAL_INSTRUCTION_ADDRESS` in `jolt-claims`; the stage-5 verifier excludes
  identity-RAF addresses whose upper 64 bits are all ones. The source audit and
  separate-model plan are in [Layer 4](../methods/soundness.md#layer-4-lookups).
  The current soundness theorem uses `2^128 < ringChar F`; its earlier `2^127`
  bound did not justify full-address injectivity for the unguarded base relation.
- **Not modeled.** Rust can trace nonempty trusted-advice bytes without a commitment,
  then fail proving because the verifier expects zeros; Lean has no separate
  commitment-presence flag to express that mismatch.
- **Expansions.** `SourceInstruction.expand` (`expansions.lean`) uses the bytecode
  project's programs. All 57 generated programs, including LR.W, LR.D, SC.W and
  SC.D, are in `ExpansionsAutomated.lean` and match `jolt-lean-gen` on the
  experimental Rust checkout exactly. LR/SC are not proved against Sail. The older
  `JoltISA.lrwProgram`/`lrdProgram` (`Expansions/LoadReserved.lean`) follow the old
  tracer and are unused.
  The rows they emit are checked in `expansion_facts.lean`. Still relied on and not
  stated there: operand order is Rust's rs1/rs2, and `VirtualRev8W` has immediate 0.
- **SC success flag, PR #2039 experiment.** The new expansion computes success
  with XOR and SLTIU from virtual register 32 (SC.W) or 33 (SC.D) and the target
  address. The RAM guard remains. The patched tracer no longer supplies SC advice,
  so neither does `honestTracerAdvice`. No SC row is a `VirtualAdvice`; its
  runtime-advice agreement reduces to `none = none`. Constraint-to-execution
  soundness only needs the ordinary instruction proofs for SC's rows. Register
  agreement supplies the same values of registers 32 and 33 to the witness and
  run, without an invariant interpreting them as an emulator reservation.
  `NoStoreConditional` stays in this first review chunk pending that instruction
  coverage; the main theorem is still sorried. The follow-up steps are in the
  plan's PR #2039 section.
- **LR/SC reservation correspondence (model obligation).** Jolt's native
  execution methods `SCW::exec` and `SCD::exec` consult `cpu.reservation_covers`;
  the patched inline trace path and this model compute success from virtual
  registers 32 and 33. Their agreement remains to be proved at source-instruction
  boundaries: initialization, LR.W setting only the word reservation, LR.D
  setting both, either SC clearing both, and other instructions preserving them.
  Include reservation validity and width, source-register aliases, `rd = x0`,
  and the RAM guard excluding the cleared value zero. Do not assert this
  correspondence inside SC.W, which temporarily uses these registers for the
  success bit and store data. The previous `honestTracerAdvice` translation
  already relied on this unproved correspondence. It is an obligation relating
  the model to Jolt's execution paths, not a soundness premise or a prerequisite
  for removing `NoStoreConditional` from the constraint-to-execution theorem.
- **Soundness execution data.** The relation is proved independent of `advice_tape`
  (`AllConstraints.advice_tape_irrelevant`). Layer 5a now defines
  [`execWithTapeAnswer`](./Soundness/Layer5/TapeSemantics.lean) and
  [`UntrustedAnswerLanguage`](./Soundness/Layer5/TapeTrace.lean) separately from
  the fixed-tape specification. Each tape load or length query gets any 64-bit
  answer; load widths remain restricted to 1, 2, 4 or 8 bytes and advance the
  cursor, but neither rule enforces consistency with tape bytes or exhaustion.
  The answer sequence is private existential data in the relaxed trace.
  Fixed-tape inclusion is proved with identical states, outputs and stopping
  facts. `NarrowAdvice.lean` proves the narrow-load post-processing keeps only
  the signed low-width portion of an answer. `AdviceExpansion.lean` now proves
  the generated AdviceLB/LH/LW sequences and their full execution under the
  relaxed per-row rule, including cursor increments and x0's temporary-register
  branch. Connecting these states to a satisfying witness remains open.
  This implements Ari's provisional decision of 2026-10-10, based on Jolt's
  documented distrust of advice values. That documentation does not specify the
  contract of `bytes_remaining()`; a16z's confirmation is still needed.
  No complete satisfying witness with inconsistent length answers has been
  constructed. Fixed-tape soundness and internal runtime-advice agreement
  remain open; see B6 in `methods/review_completeness_and_soundness.md`.
- **RAM region restriction.** `RamRegionFits` now bounds the instance's maximum
  padded RAM region by `2^64`; Ari approved this replacement on 2026-10-10.
  NOTE: to confirm with a16z. The old run-based predicate and next-step helper
  are deleted. `Layer3/Layout.lean` transfers the bound to the witness domain
  using `ConstraintContext.ramSizeBounds`. `Layer5/MemoryAddress.lean` recovers
  the signed integer sum as the selected word address, or exactly zero when
  no word is selected, before deriving the machine address. No premise over
  fixed-tape or relaxed runs is needed. The remaining execution proof must
  establish source-register agreement and actual memory-access behavior.
- **Code-memory assumption.** `CodeUnchanged` also quantifies over fixed-tape runs,
  but the soundness proof executes bytecode rather than fetching it from memory.
  No proved soundness lemma uses this premise, and no relaxed counterpart is
  needed for that execution proof. It is retained as justification for relating
  the model to Jolt's tracer; its role in the final theorem can be reviewed
  separately. It is not a Layer 5b proof blocker.
- **Register agreement.** `Layer5/Registers.lean` now proves initialization,
  successful operand reads, and preservation through PC preparation and
  destination writes for the register part of the soundness invariant.
  It includes `AllRegistersPresent` because `sourceValue` defaults missing
  architectural registers to zero, while execution rejects missing reads.
  Presence follows from initialization and is preserved by writes; it is not
  a new premise. Instruction families still have to establish successful
  writes and their value's encoding in `RdWriteValue` before applying the
  shared update lemma. The new proofs use only Lean's three standard axioms.
- **ADDI soundness step.** `Layer5/AddImmediate.lean` now proves a selected
  ADDI row executes to the concrete destination-write state, writes the
  wrapped sum constrained by the lookup, and preserves register agreement
  whenever a next table column exists. Operands, metadata and write success
  are derived from bytecode validity, the constraints and current register
  agreement. `Layer5/RegisterWrite.lean` proves canonical destination writes
  succeed. Neither lemma adds a soundness premise. The ADDI result's axiom
  list contains the standard three plus the allowed uninterpreted Sail
  constant `sys_enable_experimental_extensions`; the write helper uses only
  the standard three. Other families, RAM agreement and control flow remain
  open.
- **To do.** Audit the model against upstream main `629ed77b` (decoder changes #1902
  and #1958, HostIO #1973, `MemoryLayout::try_new` #1978). Fix 75 comments that cite
  `/Users/ari.biswas/...` paths. Drop the unused `ramFits`, `traceFits` and
  `bytecodeDomain` arguments. `constraints.md` still calls (16) a statement.
