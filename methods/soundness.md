---
title: Plan for deterministic, non-succinct soundness
---

Our goal is to make Jolt secure through formal verification. Each intermediate
claim should give us a reusable proof or expose an edge case we can investigate
and fix.

Read these before beginning work:

1. [The high-level account of Jolt](https://randomwalks.xyz/blog/jolt-qed/01-jolt-why/).
2. [The completeness proof and bug-finding workflow](./constraint_proving.md).
3. [Known model gaps and proof obligations](../JoltConstraints/model_review.md).

The local `blog/` is stale; use the published article for background.

## Soundness statement

The current target is [`JoltInstance.soundness`](../JoltConstraints/Soundness/soundness.lean).
It still uses the fixed-tape language. Layer 5a now defines the separate relaxed
language in [TapeTrace.lean](../JoltConstraints/Soundness/Layer5/TapeTrace.lean)
and proves fixed-tape language inclusion. The main theorem has not been switched
to that language. Layer 5a is built and reviewed by reading. Ari approved the
instance-only RAM-region premise below; Layer 5b begins by deriving nonwrapping
addresses from it and the constraints.

**Source-language scope.** Both targets cover programs represented by
[`SourceInstruction`](../JoltConstraints/expansion_helpers.lean): the modeled
RISC-V instructions and the listed Jolt custom instructions at opcode `0x5B`.
Jolt's inline/precompile opcodes `0x0B` and `0x2B`, including the SHA-256 and
Keccak inlines, are outside that type. Any guest using these inlines is outside
the theorem's scope by construction. This is an existing language restriction,
not an added soundness premise.

An instance is a claim about one program.
It gives the program, its public inputs and trusted advice, and the output bytes and panic flag the program is claimed to produce.
The private inputs are what the prover picks and Jolt's verifier never sees.
In the existing specification they are the untrusted advice, which is loaded into RAM, and the advice tape, which the guest reads while the program runs. The relaxed specification supplies independent answers in the existentially chosen trace (Layer 5a). It retains the tape state for exact inclusion, but the relaxed tape instructions do not consult its bytes or enforce exhaustion.
A step is one row of the expanded bytecode being run; an expandable instruction such as DIV takes several steps.
A witness `w` is a set of tables indexed by `params.traceLength` cycles.
The proof must establish which cycles describe execution steps and which are padding.
In the non-succinct model, the verifier receives `w` in the clear and checks every modeled constraint.

The planned theorem says: if some `w` satisfies every constraint, then there are private inputs and a trace under the untrusted-answer semantics whose final device holds the claimed output bytes, after trimming trailing zeros, and the claimed panic flag.
The existing `HonestTrace` describes Jolt's tracer running with a fixed tape: each step's bytecode row, its state before and after, the runtime advice Jolt's tracer computes, and the step where Jolt's tracer stops.
The relaxed trace allows independent tape answers while retaining the other execution, internal runtime-advice and stopping requirements. Its definition and the inclusion of fixed-tape traces are implemented in Layer 5a.
We aim to preserve the supplied untrusted advice in RAM and choose the tape answers from the witness; the audit has found no constraint linking those answers to one tape.

The premises are `2^128 < ringChar F`, `NextPCNoWrap`, `RamRegionFits`, `CodeUnchanged`, and the temporary restriction `NoStoreConditional`.
On 2026-10-10, Ari approved `RamRegionFits`: for the instance's layout and
successfully computed maximum RAM size, `lowest + 8 * maxRamSize ≤ 2^64`.
**NOTE: to confirm with a16z.** The definition is in
[Layer3/Layout.lean](../JoltConstraints/Soundness/Layer3/Layout.lean).
This restricts the instance's maximum padded RAM region, not its execution runs.
Together with `ConstraintContext.ramSizeBounds`, it bounds all eight bytes of
every in-domain word. Layer 5b recovers integer address sums from satisfying
constraints, including the unselected address-zero case; the argument applies
to both fixed-tape and independent-answer execution. The former run-based
RAM no-wrap predicate and its next-step helper have been deleted.
On 2026-10-10, Ari approved excluding `SC.W` and `SC.D` from every source row, including unreachable rows, while their advice mismatch is unresolved ([a16z/jolt#2037](https://github.com/a16z/jolt/issues/2037)). `LR.W` and `LR.D` remain allowed.
`NoStoreConditional` is a restriction on this theorem, not a check made by Jolt's verifier. Its `FIXME` calls for removal once Jolt's SC constraints enforce the honest tracer's outcome and the model reflects that fix.
The language and instance are unchanged by it. Stopping and panic remain open obligations; this restriction only excludes the SC cases.
On 2026-10-10, Ari also decided to treat every advice-tape answer as untrusted for the planned soundness theorem, pending a16z's confirmation. Retain the fixed-tape specification for completeness and add the relaxed specification alongside it, as recorded in Layer 5a.
On 2026-10-10, Ari chose to model Akita separately. The current theorem covers the base constraint relation over fields with characteristic above `2^128`, including BN254. Akita's prime is smaller and its extra lookup-address guard is outside this relation. The audit in Layer 4 records that distinction.
The separate Akita work will model its field and deterministic, non-succinct constraint relation, including that guard. PCS security, commitments, and opening protocols are outside the current proof scope.
Whether the modeled constraints are the ones Jolt's verifier checks is a separate question.

## Key ideas

### The trace comes from running the program

`w` holds field elements, not machine states, so the steps of the relaxed trace `T` cannot be read off it.
`T` starts from the state the instance and the private inputs give.
Each step's state after follows the chosen execution semantics: the existing `execInstr` for fixed-tape runs, and `execWithTapeAnswer` for runs with independent tape answers.
Once the private inputs are chosen, nothing else is free: Jolt's tracer computes the runtime advice, such as a division's quotient, from the state.

### Choosing the private inputs

Keep the `untrusted_advice` from the `privateInputs` supplied to `AllConstraints`; the context already binds initial RAM to those inputs.
Under the planned untrusted-answer semantics (decision of 2026-10-10, Layer 5a), no single consistent tape is needed.
The private inputs instead supply the answers the witness gives at each tape read and each `bytes_remaining()` query.

At each step that uses runtime advice, we must prove that the value in `w` agrees with the honest tracer's computation.
SC.W can report failure where Jolt's tracer reports success. The temporary `NoStoreConditional` premise excludes its source rows and those of SC.D; the execution proof must use that premise to eliminate these cases.

### The witness proves facts about the execution prefix

The main lemma extends an execution prefix while preserving `Agrees w t prefix state`, defined below.
It connects the prefix and its current state to these witness columns:

- **Bytecode selection:** `PC` and `BytecodeRaChunk`. A slot is an index into the bytecode as `w` sees it: slot `i + 1` holds `bytecode[i]`, and slot 0 and the trailing unused slots are no-ops.
- **Registers:** `RegistersVal r t`, the value `w` says register `r` holds before cycle `t`; the read selectors `Rs1Ra`, `Rs2Ra` and write selector `RdWa`; and the values `Rs1Value`, `Rs2Value`, `RdWriteValue`.
- **RAM:** `RamVal a t`, the value `w` says the memory word at RAM index `a` holds before cycle `t`; `RamAddress`, the selector `RamRa`, and the values `RamReadValue`, `RamWriteValue`. `RamValFinal a` is the claimed value at RAM index `a` after all cycles.

The register and RAM tables are compared in full, because cycle `t + 1` may read any register or address, not only the ones cycle `t` wrote.
The columns not listed above need not be unique.
Individual helpers that accept a plain `Trace`, such as `TraceWitness.PC`, can be reused when stating agreement.

For a fixed-tape trace `T : HonestTrace`, `f(T) := T.honestWitness params` is the modeled extraction at `w`'s `params`. An analogous extraction for relaxed traces is optional; the soundness proof uses column agreement directly.

### Execution cycles and padding

Let `N := params.traceLength`.
Call cycle `t < N` a padding cycle when `w.InstructionFlags .IsNoop t = 1`.
Define `n` to be the first such cycle, or `N` if there is none.
The proposed execution prefix uses cycles `0, …, n - 1`; it is empty when `n = 0`.

**Noop source audit:** at Jolt revision
`43cc043332762034b5f65379441576e06e7a3890`, the pseudo instruction
`jolt-riscv/src/instructions/i/noop.rs` does carry `IsNoop`. It is absent from
the modeled `JoltISA.Instr` constructors. No branch of
`jolt-program/src/image/decode.rs::decode_instruction` or its instruction-kind
helpers returns `SourceInstructionKind::NoOp`; the `NoOp` arm in `operands`
only handles an already-supplied kind. Nonzero compressed ELF instructions are normalized
and passed through that decoder too. Expansion's `expand/operands.rs::noop_for`
emits `ADDI x0, x0, 0`, which has `IsNoop = false`, rather than the pseudo Noop.
Preprocessing inserts pseudo Noops for slot 0 and trailing padding and maps a
pseudo Noop to slot 0. Thus the model's real-row/padding distinction matches
these decoded programs. If we later model manually supplied pseudo Noops or
additional inline instruction kinds, revisit this distinction. This source
audit resolves the TODO in `metadata.lean`; it is not the Layer 6 suffix proof.

This definition does not establish that padding forms a suffix.
Layer 6 must prove that every cycle from `n` to `N - 1` is padding, that these cycles preserve the register and RAM tables, and that each earlier cycle selects an actual bytecode row.
The case `n = N` has no padding cycle: the shift equation sets `NextIsNoop` to 1 at the last cycle even if that cycle is not a no-op, so it does not by itself force `n < N`.
Whether the execution stops at this boundary is a separate obligation in Layer 7.

### Agreement is proved by induction on the step

Use the private inputs chosen above, including the tape answers taken from the witness, for the whole execution.
At the start of a source instruction, `advance_pc` sets `PC` to that instruction's address and `nextPC` to the address plus its length, 2 or 4 bytes.
Within an expansion, the next row instead starts directly from the previous row's post-state.

Use a predicate `Agrees w t prefix state` on a plain execution prefix under the untrusted-answer semantics and its current state, before constructing a completed relaxed trace.
Here `0 ≤ t ≤ n`, and `prefix` contains exactly the `t` rows already executed.
For `t < n`, `state` is the pre-state for executing row `t`, with `advance_pc` already applied when that row starts a source instruction.
For `t = n`, `state` is the last post-state, or the initial state if `n = 0`; no further `advance_pc` is applied.
The predicate records successful execution and linkage of the prefix, agreement with the witness columns for its executed rows, and the runtime-advice equality required by `advice_from_honest_tracer` for each of those rows.
State agreement is retained through the endpoint `t = n`:

- For `t ≤ n` and `t < N`, compare `RegistersVal r t` and `RamVal a t` with the field encodings of the corresponding register and RAM word in `state`, for every register `r` and RAM index `a`.
- For `t = n = N`, compare `RamValFinal a` with the final state's RAM encoding for every RAM index `a`. There is no `RegistersVal` column at cycle `N`.

Also retain `AllRegistersPresent state.sail`: agreement with `sourceValue`
alone would not ensure a successful read, because that function defaults missing
architectural registers to zero. `Layer5/Registers.lean` defines the register
portion as `RegisterAgreement`, proves it for the initialized state, and
preserves it through PC preparation and destination writes. Register presence
is a proved induction invariant, not an added soundness premise.

The RAM comparison must account for address remapping and the device regions; it is a proof obligation, including the panic and termination cases discussed below.
The predicate also records that the prefix's tape answers are the witness's answers at its tape-reading rows.
For `t < n`, it requires the slot `w` selects at cycle `t` to be:

- the entry slot when `t = 0`;
- the slot immediately after the previous row's slot when the previous row has rows of its expansion left (`virtual_sequence_remaining.getD 0 ≠ 0`);
- the first slot of the source instruction at the previous post-state's `nextPC` otherwise.

For example, suppose `n ≥ 2`, cycle 0 selects `ADDI x5, x0, 7`, and cycle 1 reads `x5`.
`Agrees w 1 prefix state` then says both that `state` holds 7 in `x5` and that `RegistersVal x5 1` is its field encoding; the register-read equation forces cycle 1's read to return that value.

There are two induction obligations:

1. **Initialization:** the constraints select the entry slot, zero the register table, and supply the initial RAM. Use `initial_state_sourceValue` to show that the initial state's general-purpose and virtual registers are also zero. For `n > 0`, apply the entry instruction's `advance_pc` and prove that it preserves these register and RAM values. For `n = 0`, keep the initial state. Establish agreement for the empty prefix.
2. **Extension:** for `t < n`, use agreement at `t` and the required advice compatibility to prove that the step succeeds under the untrusted-answer semantics and returns a post-state matching the step's writes. Prove the new row's runtime-advice equality and preserve those for earlier rows, together with the tape-answer facts. If `t + 1 < n`, use the next slot and pre-state specified above to establish agreement at `t + 1`. If `t + 1 = n`, retain the post-state and establish the endpoint table comparisons above.

At a tape-reading step, recover a 64-bit answer from the witness and use it directly; no agreement with a fixed tape is required for the relaxed target. At an internal runtime-advice step (`VirtualAdvice`), prove that the value agrees with the honest tracer.
Local extension lemmas may take these facts as hypotheses; their application must justify them from the constraints, possibly using other rows of the same expansion.
These proofs work with the prefix and its state, before a completed relaxed trace exists.

## Workflow for each obligation

1. State the property and identify the exact constraints expected to enforce it.
   Start from an arbitrary satisfying witness. For model-dependent facts, check
   the Lean definitions against Jolt's code and record the checkout revision.
2. Try to prove the property with the existing premises. Examine boundary cases
   alongside the proof: field wraparound, unused address bits, absent reads or
   writes, padding, and the first and last cycles, as relevant.
3. If the proof stalls, distinguish a missing lemma, a model mismatch, an overly
   strong intermediate claim, and a constraint weakness. A free value is a
   security problem only if it permits behavior outside the claimed language.
   A counterexample to a subset of constraints need not satisfy `AllConstraints`.
4. For a suspected bug, construct the smallest counterexample, trace its effect
   on the claimed execution or outputs, and reproduce it against Jolt's code. Record
   whether the actual verifier accepted a proof. Preserve the reproducer; after
   a fix, rerun it and close the corresponding Lean obligation.

Use small lemmas and the default heartbeat limit; do not raise `maxHeartbeats`.
If an obligation is blocked, raise the exact missing fact or counterexample for discussion.
Do not add premises to the soundness theorem or instance without Ari's
permission, or change the language just to close a proof. Record each obligation
as proved, proof gap, model mismatch, intermediate claim to revise, or bug, with
its evidence and next step.
A proof counts as closed only after compilation and checking its dependencies
for remaining `sorry`s or unjustified axioms.
Run `#print axioms` on each layer's top lemmas and on the final theorem.
The axiom policy allows the three standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`, plus these named, uninterpreted Sail
constants declared in [`RiscvExtras.lean`](../LeanRV64D/RiscvExtras.lean):

| Constant | Role |
| --- | --- |
| `sys_enable_experimental_extensions : Unit → Bool` | Sail configuration flag |
| `load_reservation : Arch.pa → Nat → SailM Unit` | Reservation update hook |
| `match_reservation : Arch.pa → Bool` | Reservation query hook |
| `cancel_reservation : Unit → SailM Unit` | Reservation cancellation hook |
| `valid_reservation : Unit → Bool` | Reservation validity query hook |

These constants have inhabited types and impose no proposition about their
behavior. A proof that uses no additional assumptions about them holds for
every interpretation of them, with the semantics in its statement interpreted
accordingly. They cannot supply an unproved fact about execution, such as a
reservation hook preserving state or agreeing with Jolt's reservation model.
Such behavior still needs a proof; this policy does not authorize new soundness
premises or resolve the LR/SC equivalence gaps.

Forbid `sorryAx`, native-evaluation or compiler-trust axioms such as
`Lean.ofReduceBool` and `Lean.trustCompiler`, and every dependency outside this
list. A further Sail constant must be checked and explicitly named in this
policy before accepting a proof that depends on it; being declared with `axiom`
in a Sail file is not sufficient. Record the exact constants used by each layer
and by the final theorem. Prefer narrower lemmas when they avoid dependencies
the current proof does not need.

The `noEarlyNextPCChange` field of `expand_program_rows_valid` depends on
`sys_enable_experimental_extensions`. That dependency is acceptable under this
policy and may be needed in Layers 5b or 6; it is not yet established that the
final proof needs it. Layer 2 uses the narrower row-validity and canonicality
facts and therefore still has only the standard three axioms.
Before using instruction-equivalence results in Layer 5b, check their actual
dependencies: `RiscvInstruction.lean` and `Mret.lean` contain unfinished cases,
and the LR/SC modules document the reservation hooks declared in
`RiscvExtras.lean`. The quoted `axiom` lines in those module comments are not
additional declarations. Importing a module alone does not introduce a proof
dependency, but using its results can.

## Proof layers

Proofs live in `JoltConstraints/Soundness/Layer0/` through `Layer8/`, matching the
layers below. Create each directory as its proofs are added. The final theorem
stays in `JoltConstraints/Soundness/soundness.lean`.
Algebraic helpers shared across layers live in `JoltConstraints/Soundness/Helpers/`.
Layer 5 has two parts: 5a is the model change for untrusted tape answers, and
`Layer5/Step.lean` (5b) proves execution steps.
These are planned, not completed.

Layers 0 to 4 prove field bounds, selection, table histories and lookup facts.
Layer 5a adds the untrusted-answer semantics alongside the fixed-tape semantics and proves inclusion; the execution-prefix induction in Layers 5b and 6 then takes tape answers from the witness.
Runtime-advice agreement is established when extending the prefix and retained in `Agrees`.
Layer 7 collects the execution and advice facts, proves the stopping obligations, and assembles the relaxed trace; Layer 8 proves `matches_outputs`.

### Layer 0: field elements to numbers

What: distinct natural numbers below the field's characteristic stay distinct in the field, and each comparison needs a bound showing both sides are below it.
Also derive `2^chunkBits < ringChar F` from the verifier's setup check and `charAbove2pow127`.
Why: constraints are equations over the field `F`, but registers and memory hold 64-bit words.
To conclude `a = b` from `(a : F) = (b : F)`, both must be below the characteristic.
The existing Layer 0–1 lemmas use only `charAbove2pow127 : 2^127 < ringChar F`, which covers 64-bit words but not every 128-bit integer. Their bounds stay unchanged; the base soundness theorem supplies `charAbove2pow128 : 2^128 < ringChar F`, the stronger bound needed in Layer 4. `two_pow_127_lt_char` in `Layer0/Field.lean` provides the bridge; Layer 2's zero-lookup and x0 proofs already use it.
The chunk-width bound ensures that one-hot Hamming-weight sums cannot wrap in the field, so their field values determine the number of selected entries.
Uses: `charAbove2pow127`, `ConstraintContext.oneHotFitsSetup`, bounds on parameters and expressions.

### Layer 1: selection

What: (a) at each cycle, the bytecode chunks and instruction-lookup chunks are one-hot, and the RAM chunks are one-hot or all zero as `RamHammingWeight` says.
(b) Every cycle selects exactly one bytecode slot, and each `InstructionRa` lookup selector selects exactly one address.
`InstructionRa` is not committed: it is rebuilt from small chunks and has an address domain of `virtualChunkBits` bits. This use of "virtual" in the parameter name is unrelated to virtual instructions.
For RAM, the full selector is all zero exactly when `RamAddress` is zero; otherwise it selects exactly one RAM index.
The all-zero RAM case has zero read and write values and zero per-word increments.
(c) Each sum of the form "table entry times selector" collapses to the selected entry, or to zero for an all-zero RAM selector.
The lookup equations use the product of the `InstructionRa` selectors over a full 128-bit address; reconstruct that unique address before collapsing their sums.
Why: this identifies the bytecode slot `w` selects at cycle `t`, including no-op slots, and its registers, immediate and flags.
Later layers use this selection.
Uses: Booleanity, Hamming weights, `oneHotFitsSetup`, address encoding.

### Layer 2: registers

What: the register table is all zero at cycle 0.
From cycle `t` to cycle `t + 1`, only cycle `t`'s destination register changes, and it changes to `RdWriteValue t`.
A register read at cycle `t` returns the table's value at cycle `t`.
Prove separately that the x0 table entry stays zero: for every cycle,
`RdWa x0 t * RdInc t = 0`. The selected bytecode destination can be x0, while
Sail discards writes to x0. Derive
`JoltInstructionRow.Valid.x0DestinationIsNoOp` through
`ExpansionRows.expand_program_rowOk` and `ExpansionRows.RowOk.valid`, then use
the canonical no-op's constraints to prove the increment is zero.
Both of these narrower lemmas have only the standard three axioms. Prefer them
to the larger [`expand_program_rows_valid`](../JoltConstraints/trace_interface.lean)
bundle for this fact: its `noEarlyNextPCChange` field depends on
`sys_enable_experimental_extensions`. That named Sail constant is allowed by
the axiom policy above, but Layer 2 does not need it.
Validity must be proved from the program, not assumed from an honest trace.

**Proof order:** prove the small lookup fact needed for x0 within Layer 2(b),
before its cycle induction; the general lookup semantics stay in Layer 4.
When the selected row is `ADDI x0, x0, 0` and the current x0 table entry is zero,
the source-read and instruction-input equations give
`RightLookupOperand = Rs1Value + Imm = 0`. This row has identity RAF, so Layer 1(c)
and `charAbove2pow128` force its selected 128-bit address to zero. Prove that
the `RangeCheck` entry there is zero; the row's `WriteLookupOutputToRD` flag
then gives `RdWriteValue = LookupOutput = 0`. The write-value equation and the
induction hypothesis imply `RdInc = 0`. Other destinations and padding leave
the x0 entry unchanged. These lookup facts use selection and the field bound,
not a general register-history or execution theorem, so this order avoids a
circular dependency. The current x0 value being zero is an induction hypothesis,
not a new soundness premise.

For initialization, connect the zero table to the initial state's registers using [`initial_state_sourceValue`](../JoltConstraints/execution_facts.lean).
This existing lemma takes an `initial_state` equation and a source register; it does not require an `HonestTrace`.
Prove the connection for every register-table index using the register-address map, and prove that `advance_pc` preserves these values.
Prove the required encoding/decoding identities and injectivity on **canonical**
source and destination operands, using
[`register_encoding.lean`](../JoltConstraints/register_encoding.lean) and
[`register_address.lean`](../JoltConstraints/witness_helpers/register_address.lean).
Architectural registers occupy indices 0–31, and canonical virtual registers
occupy 32–127. The raw constructors can alias (for example, x0 and virtual
register 0), so unrestricted injectivity would be false. Derive each row's
operand canonicality from `ExpansionRows.expand_program_rowOk`'s `canonical`
field via `context.expands`. This is the narrower route to the fact also bundled
in `ExpansionRowsValid.registerOperandsCanonical`. Use those identities when
transferring a table update to the corresponding execution-state register.
Why: this makes the register table behave like a register file, so it can be compared with the registers in the run's state.
Uses: `RegistersValEqPrefixRdInc`, the register read and write equations, Layer 1.

Part (a) contains field-valued initialization, reads, and updates in
`Layer2/Registers.lean`. Part (b) adds the zero-lookup fact in `ZeroLookup.lean`,
the x0 induction in `ZeroRegister.lean`, the canonical index map in
`RegisterMap.lean`, and initialization and `advance_pc` agreement in `State.lean`.
Both parts are proved and Ari's Layer 2 review corrections have been addressed.
Agreement after executing an instruction remains part of Layer 5b.

### Layer 3: RAM

What: the RAM table starts at the instance's initial memory, which includes the untrusted advice.
Each cycle changes at most the word it accesses, a read returns the table's value, and `RamValFinal` is the initial RAM plus every increment.
Reuse `sum_before_succ` from
[`Soundness/Helpers/PrefixSum.lean`](../JoltConstraints/Soundness/Helpers/PrefixSum.lean)
for the RAM prefix sums; Layer 2 already uses this shared lemma for registers.
Cycles that do not touch memory and the remapping of addresses to RAM indices must be accounted for.
Prove the last-cycle update into `RamValFinal`, as well as updates between `RamVal` columns.
If the per-word increments `RamRa a t * RamInc t` vanish for `n ≤ t < N`, prove `RamVal a n = RamValFinal a` when `n < N`; Layer 6 must discharge that condition for padding.
Also prove that `advance_pc` preserves the RAM encoding used in agreement.
The initial state's layout must equal the context's public layout, so the RAM
indices in the initial-state and address-remapping lemmas refer to the same base.
The proved state lemmas compare the initial image and preserve every observation
of the memory map and device under `advance_pc`. They do not identify later
device reads with the last stored word: that execution obligation remains in
Layer 5b, including the known panic and termination discrepancies.
`ram_zero_effects` now supplies the zero-address updates;
the unused overlapping `ram_read_of_address_zero` lemma was removed.
Why: this does for memory what Layer 2 does for registers.
`RamValFinal` is also where `w` holds the output bytes.
Uses: the RAM equations, `ConstraintContext.initialized`, Layer 1.

**Address wraparound, derived from `RamRegionFits` (NOTE: to confirm with a16z):**
the address lemmas take `encoded : RamAddress = raw.toNat`.
The load/store constraint adds `Rs1Value` and the signed immediate in the field,
while execution wraps the sum at 64 bits. The layout premise states
`lowest + 8 * maxRamSize ≤ 2^64`. The verifier's RAM-size check then bounds the
entire witness RAM domain, including every byte of its last word.

[Layer5/MemoryAddress.lean](../JoltConstraints/Soundness/Layer5/MemoryAddress.lean)
derives `encoded` as follows. Write `base` for a 64-bit base-register value,
`imm` for the immediate, and `S := base.toNat + imm.toInt`, an integer.

1. The selected LD/SD bytecode row supplies the active Load/Store flag and the
   signed immediate column. Given source-column agreement, the address
   constraint yields `RamAddress t = (S : F)` without assuming no wrap.
2. If RAM index `c` is selected, recover `S = lowest + 8 * c` as integers. If
   every RAM selector is zero, recover `S = 0`. In both cases, shift the two
   integers by `2^63` into `[0, ringChar F)` before applying cast injectivity.
   Word and signed-immediate bounds justify that interval even when `S` might
   initially be negative. Equality of field residues alone is not enough.
3. The layout bound gives `0 ≤ S < 2^64` for a selected word; the zero case
   has the same bounds. Thus `((base + imm).toNat : Int) = S`.
4. Substitute that integer equality into the field equation to obtain
   `encoded`. `ld_address_encoded` and `sd_address_encoded` discharge the flag
   and immediate facts from the selected row; source agreement remains an
   execution-induction obligation.

For example, base `2^64 - 8` with immediate 8 gives `S = 2^64`. Under the new
layout premise, no satisfying LD/SD cycle can have these operand values. The
premise imposes no condition on unconstrained execution runs. In the selected
case, `c < ramSize ≤ maxRamSize` also puts all eight bytes below `2^64`.
Proving the actual memory instruction succeeds, including at address zero,
remains separate from this arithmetic result.

`MemoryLayout.new` and `maxRamSize` alone do **not** imply
`lowest + 8 * ramSize ≤ 2^64`. The kernel-checked example in
[layout_check.lean](../bug-report/ram-address-wraparound/layout_check.lean)
uses zero I/O, advice and stack sizes, an 8-byte program, and heap size `2^63`.
The layout succeeds with `lowest = 2^31 - 16` and
`heap_end = 2^63 + 2^31 + 136`; `maxRamSize = 2^61`. Its padded domain contains
the aligned byte address `2^64`. A source value `2^64 - 8` plus immediate 8
would address that word in the field equations but wrap to zero in execution.
This refutes the proposed bound from those checks; it is **not** a witness
satisfying `AllConstraints` or a reproduction against Jolt's verifier.

The source check at `43cc043` finds the same arithmetic in
`common/src/jolt_device.rs::MemoryLayout::new`,
`crates/jolt-program/src/preprocess/ram.rs::compute_max_ram_k`, and the RAM-size
checks in `crates/jolt-verifier/src/verifier.rs`.
The same wrap breaks completeness: [ram-address-wrap.md](../bug-report/ram-address-wrap.md) shows the honest witness failing the address constraint when the address wraps.
Ari chose a run-level no-wrap premise.
Ask a16z to confirm that Jolt programs never compute a wrapping load or store address.

### Layer 4: lookups

What: when a cycle uses a lookup table, recover the table and its operands from `w`, and show the lookup output is that table's operation on them.
Why: the constraints never compute an instruction's result directly; for example, ADDI's result reaches `rd` as a lookup output.
To match the run's state after a write with `RdWriteValue`, the lookup output must be the real operation.
Uses: the instruction read-raf equations, Layer 1, pure table identities.

Work in reviewable parts:

- **(a) Table selection and arithmetic RangeCheck:** identify the table from
  the selected bytecode slot (including absent tables and padding), recover an
  identity-RAF address, and interpret addition, biased subtraction and full
  multiplication followed by the low-64-bit RangeCheck table. The input-word
  agreement hypotheses are local obligations for Layer 5b; they are not added
  to the soundness statement. This first part is proved below.
- **(b) Interleaved operands:** recover the two 64-bit operands when the RAF
  flag is zero, then connect bitwise and comparison tables to their operations.
  Operand recovery, evaluation at the recovered address, and the bitwise and
  comparison table interpretations are proved and reviewed.
- **(c) Remaining tables and uses:** connect W operations, upper-word results,
  aligned addresses, shifts, rotations, extraction and assertion tables, and
  discharge the remaining instruction-input and lookup-output uses. Reuse pure
  table identities without assuming an already-executed trace. This part is now
  proved and reviewed. Shift-mask shape and agreement with the run's source
  values remain local obligations for Layer 5b, which composes these lookup
  lemmas with execution; they are not soundness or instance premises.

Advice rows need a different argument from arithmetic rows. Their `Advice` flag
sets identity RAF, but exempts the right lookup operand from equality with the
right instruction input. Choose the address supplied by
`instructionLookupRa_unique`, use `lookupOutput_of_selected_bytecode`, and apply
`rangeCheck_entry` to obtain its low 64 bits. This proves that the lookup output
encodes a word; no input-determined `encoded` hypothesis is available for
`lookupOutput_rangeCheck_of_identity`. At the lookup level, any 64-bit word is
possible; constraints elsewhere in the program may restrict it. Layers 5–7
must separately prove that runtime advice (`VirtualAdvice`) equals the honest
tracer's result. Tape answers (`VirtualAdviceLoad`, `VirtualAdviceLen`) need no
such proof: they are untrusted under the Layer 5a decision.

**Field-scope audit before this layer:** an identity-RAF row
(`InstructionRafFlag = 1`) equates the full lookup address with the right operand
only in the field. For Akita's prime `p = 2^128 - 2^32 + 22537`, both `s` and
`s + p` fit in 128 bits when `s < 4294944759`; they have the same field encoding
but different `RangeCheck` outputs. The base equations alone therefore do not
support an injectivity argument from the former `2^127 < ringChar F` premise.
This is an obstruction to the proposed argument, not a constructed witness
satisfying every constraint.

Jolt revision `43cc043332762034b5f65379441576e06e7a3890` already addresses this
alias in its Akita build. In
`crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs`,
`CANONICAL_INSTRUCTION_ADDRESS = cfg!(feature = "akita")`, and
`upper_half_all_ones` is the product of the upper 64 address bits.
`crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs` adds the
`gamma^3` coefficient for this predicate times `InstructionRafFlag`; the input
claim has no corresponding coefficient. In the deterministic, non-succinct
relation this contributes a zero constraint for each cycle. At a selected
identity address it rules out an all-ones upper half, hence gives
`address < 2^128 - 2^64 < p`. Both prover and verifier Cargo features enable
`jolt-claims/akita`. This rules out the proposed alias in that build; this audit
read the code and did not run an end-to-end forged proof.

Our [constraint checklist](../JoltConstraints/constraints.md) explicitly leaves
this Akita condition outside the current base model. On 2026-10-10, Ari approved
restricting this theorem to `2^128 < ringChar F` and modeling Akita separately.
Layer 4 must use that stronger bound to recover full lookup addresses. The
separate Akita relation must include the guard and its actual field: merely
adding the upper-half guard would still not cover every characteristic above
`2^127`. That modeling work is pending and does not include PCS security.

### Layer 5: advice tape and execution

#### Layer 5a: untrusted advice-tape answers

**Where tape instructions come from.** No RISC-V instruction expands to a tape instruction.
`VirtualAdviceLoad` and `VirtualAdviceLen` come only from Jolt's custom source instructions (opcode `0x5B`): `AdviceLB`, `AdviceLH`, `AdviceLW`, `AdviceLD` and `VirtualAdviceLen` ([`expansions.lean`](../JoltConstraints/expansions.lean), lines 279–285).
A guest gets them by calling the SDK's tape functions: the reads that `#[jolt::advice]` uses, and `AdviceTape::bytes_remaining()` (`jolt-sdk/src/lib.rs:545`), which nothing in the SDK calls.

**Decision of 2026-10-10.** The [runtime advice page](https://jolt.a16zcrypto.com/usage/runtime_advice.html) says: "Advice values are untrusted -- the prover could supply arbitrary data. The guest must verify correctness using `check_advice!`."
Ari decided to treat every tape answer as untrusted, including the answer to `bytes_remaining()`, which the page does not mention.
That last point is to be confirmed with a16z ([Questions for a16z](#questions-for-a16z), item 1).
A weak check in a guest is the guest's problem, not a Jolt soundness bug.

**Two specifications to retain.** Keep the existing fixed-tape execution, including its cursor and [`readAdviceTape`](../JoltBytecode/JoltISA/AdviceTape.lean), for Jolt's actual tracer and completeness.
The separate untrusted-answer execution for the planned soundness theorem is
`execWithTapeAnswer`. `UntrustedAnswerRun.answers` supplies a finite sequence
indexed by executed rows; answers on non-tape rows are ignored. These answers
are private existential data in `UntrustedAnswerLanguage`. The induction will
take them from the witness. The original `JoltPrivateInputs` and initial state
are retained, including tape bytes and the cursor, so fixed-tape inclusion can
preserve every state exactly. Only the relaxed load rule advances the cursor;
neither relaxed tape rule reads the tape bytes or enforces exhaustion.
A free answer must be allowed to be any 64-bit word, because the constraints only range-check the advice row's value; the honest `readAdviceTape` result has zero high bits for a narrow read.
Check that each narrow-load expansion uses only the low bytes of that row's value, so the guest still sees a value of the declared width.
Prove that every fixed-tape run gives an untrusted-answer run by taking its actual read values and length reports as the answers, preserving the executed rows, register and RAM values, outputs and stopping behaviour.
This proves inclusion of the fixed-tape language in the relaxed language; the reverse inclusion is not assumed.

**Shared trace requirements.** `UntrustedAnswerRun` and `UntrustedAnswerTrace`
currently duplicate the linkage, initialization, preprocessing, internal-advice
and stopping requirements of `ValidRun` and `HonestTrace`. A change to either
original structure must be reviewed in its relaxed counterpart, especially a
future fix to B6's stopping specification. Fixed-tape inclusion alone does not
detect every divergence: weakening a relaxed requirement could leave inclusion
provable. A later refactor may share these fields through a structure
parameterized by the execution rule; this review does not require that refactor.

**Premise decision, 2026-10-10.** Ari approved replacing the run-based RAM
no-wrap assumption with `RamRegionFits`, the instance-only bound
`lowest + 8 * maxRamSize ≤ 2^64`. **NOTE: to confirm with a16z.**
The former predicate and next-step helper are removed. This avoids quantifying
over either fixed-tape or relaxed runs: the no-wrap fact is derived only at
satisfying LD/SD cycles, by the integer argument in Layer 3 above.
The bound and its use in the proof are recorded in `model_review.md`.

`CodeUnchanged` needs no relaxed counterpart for this proof. Both trace
specifications execute the expanded bytecode rather than fetching instructions
from memory, and no proved soundness lemma uses `CodeUnchanged`. The premise
justifies relating the model to Jolt's tracer; it does not block the relaxed
bytecode-execution proof. Its existing definition and place in the main theorem
are retained. Whether it belongs in that theorem is a separate scope question.
After reviewing Layer 5a, Ari approved this premise replacement and continuing
with Layer 5b. No other premise change was authorized.
The relaxed specification and its provisional justification are recorded in
`model_review.md`. Jolt's documented distrust of advice values does not itself
settle the contract of `bytes_remaining()`.
If a16z requires accurate length reports, retain the shared proofs and return to the fixed-tape soundness target. That still requires a tape-consistency proof or an upstream fix; the inclusion lemma alone cannot establish the stronger conclusion.

**What the relaxed target does not require.** The obligation that the witness's reads and length answers fit one tape remains open for fixed-tape soundness, but is not needed for the relaxed target.
Candidate inconsistency: a guest calls `bytes_remaining()` twice with no read in between, and the witness answers 3 and then 100. We found no constraint that rules this out, but have not constructed a complete satisfying witness. No fixed tape gives those two different answers.
The audit evidence below records the checks made for constraints linking these answers.
The [modeled metadata](../JoltConstraints/metadata.lean) gives `VirtualAdviceLoad` and `VirtualAdviceLen` the `Advice` flag and a `RangeCheck` lookup; [`rightLookupEqRightInputOtherwise`](../JoltConstraints/Constraints/RightLookupEqRightInputOtherwise.lean) leaves the right lookup operand unconstrained by the instruction input in this case.

The initial source audit at Jolt revision `43cc043332762034b5f65379441576e06e7a3890` found the same flags in `crates/jolt-riscv/src/instructions/virt/advice_{len,load}.rs`, the same lookup over the captured destination value in `crates/jolt-lookup-tables/src/instructions/virt/advice_{len,load}.rs`, and the same Advice exemption in `crates/jolt-r1cs/src/constraints/rv64.rs`.
The expansion dispatch in `crates/jolt-program/src/expand/{grammar,materialize}.rs` leaves a nonzero-destination `VirtualAdviceLen` as one native row; it adds no assertion relating separate length queries.
Advice-load expansions in `expand/memory/shared.rs` add sign extension for narrow loads, with no tape-length consistency check. The x0 rewrite in `expand/materialize.rs`, using the side-effect classification in `crates/jolt-riscv/src/kind.rs`, redirects these loads to a temporary register.
No cross-query or load/length relation was found in this audit of the modeled constraints and Jolt's R1CS, claim relations and verifier code.
Under the untrusted-answer semantics, and pending a16z's confirmation, independent answers are intended behaviour rather than a bug. Whether this is Jolt's intended contract remains open.

#### Layer 5b: one execution step

Planned file: `JoltConstraints/Soundness/Layer5/Step.lean`.

What: for `t < n`, given `Agrees w t prefix state` and the step's advice compatibility facts, prove that the step succeeds under the untrusted-answer semantics and returns a post-state matching the witness's writes.
When `t + 1 < n`, combine this with Layer 6's next-row selection and `advance_pc` rule to extend agreement.
At `t + 1 = n`, prove the endpoint table comparisons using Layer 3's update equations, including the update into `RamValFinal` if `n = N`.
This is proved one instruction family at a time, with the bounds needed to interpret register and RAM values as 64-bit words.
Use `RegisterAgreement.read` for a canonical operand's successful read and
table encoding. After deriving an instruction's successful destination write
and the equality of its value with `RdWriteValue`, use
`RegisterAgreement.write` to obtain the next cycle's register agreement.
It derives destination canonicality from the selected bytecode row and handles
x0 with Layer 2's zero-table invariant. These local execution and value facts
remain obligations of each instruction family; the shared write lemma does
not establish them. It applies when `t + 1 < N`, since there is no register
table at cycle `N`.
[AddImmediate.lean](../JoltConstraints/Soundness/Layer5/AddImmediate.lean)
now discharges these local obligations for ADDI. Its `addi_step` derives
source/immediate encodings, the addition and write flags, and the RangeCheck
table from the selected row, then proves execution and next-cycle register
agreement. The result is the wrapped 64-bit sum; no arithmetic no-wrap premise
is needed. Its execution and write-value conclusions also apply at the last
cycle. Other instruction families and RAM/PC agreement remain to be connected.

**Termination-device restriction under discussion; not added.** Banning all
termination accesses would exclude normal SDK exits: the SDK writes byte 1,
whose SB expansion loads the enclosing word before storing it. A candidate
temporary restriction would forbid reads from the termination word after a
write, while allowing the normal exit sequence. Its exact formulation and
sufficiency for the proof remain to be checked. The RAM invariant would also
need to distinguish the termination table entry from readable device memory.
Any such temporary premise must carry a comment of this form:

```text
FIXME: Temporary workaround for the termination-device mismatch tracked in
https://github.com/a16z/jolt/issues/1950 and
https://github.com/a16z/jolt/issues/1951 (item 2).
Remove this restriction once the upstream mismatch is resolved, the Lean model
reflects that resolution, and the unrestricted proof is established.
This is a temporary theorem restriction, not a verifier check or intended
permanent requirement on guest programs.
```

The local store/load discrepancy does not by itself demonstrate an accepted
cheating proof. No complete satisfying witness for that consequence has been
constructed. This candidate restriction does not resolve the separate stopping
and panic obligations.

For a runtime-advice step, justify the local lemma's advice hypotheses using the relevant expansion constraints; a tape-reading step takes its answer from the witness.
For `AdviceLB`, `AdviceLH` and `AdviceLW`,
[AdviceExpansion.lean](../JoltConstraints/Soundness/Layer5/AdviceExpansion.lean)
now proves the source expansion shapes and full execution of their
`VirtualAdviceLoad`, `VirtualMULI` and `VirtualSRAI` rows in order. Both the
ordinary-destination and x0 temporary-register branches are covered. The
proofs derive the shift constants from the generated programs, establish
register-value linkage, and apply `narrowAdvice_value` at widths 8, 16 and 32.
`execProgramWithTapeAnswers` composes the existing per-row execution rule,
using local expansion row indices. The induction still has to establish that
the witness selects these rows in order, relate its answer to the first row,
and maintain register/RAM table agreement through their intermediate states.
For an LD or SD step, use `ld_address_encoded` or `sd_address_encoded`
with the approved `RamRegionFits` premise and the source-column agreement
from the induction. These address lemmas already derive the signed integer
equality, nonwrapping bound and machine-address encoding; they do not yet
prove the memory access succeeds or matches the RAM table.
Preserve the tape-answer facts and the runtime-advice equalities in `Agrees`; prove that appending a row leaves the earlier rows' `honestTracerAdviceAtStepN` values unchanged.
Why: this supplies the transition for the induction step and the proof required by the eventual `executes` field.
Uses: Layers 0 to 4, Layer 5a, instruction semantics, runtime-advice compatibility.

Before each family's execution lemma, prove a small metadata lemma from the
selected bytecode row and its instruction constructor. It should identify the
lookup table, RAF value, input-source flags and relevant output flags. Derive the
operand words separately from `Agrees`, Layers 2–3 and the input-selection lemma;
metadata alone cannot establish agreement with the run's state.

| Instruction family | Local Layer 4 obligations to discharge |
|---|---|
| Arithmetic, including W operations and MULHU | Derive the arithmetic flag, table and RAF one from the row; recover the two input words and use `rightLookupOperand_add/sub/mul` to derive the wide `encoded` address |
| Bitwise, XOR rotations, comparisons, conditional operations and extraction | Derive the table and RAF zero; use `lookupOperands_eq_inputs_of_raf_zero` and source agreement to obtain both lookup-operand encodings |
| Powers, shift masks, alignment, byte reversal and window masks | Derive the table and addition mode; recover the source/immediate words and derive the identity address before applying the word-table lemma |
| Immediate and register shifts | Derive the table and RAF zero; prove mask shape from `immShiftOk` for an immediate, or expansion linkage and the preceding mask-producing row for a register shift |
| Advice rows | Derive the RangeCheck table and Advice flag; recover a word with `lookupOutput_rangeCheck_word`, then handle tape answers or internal runtime-advice correctness under the appropriate execution rule |
| Assertions, register writes and branches | Derive the Assert, WriteLookupOutputToRD or Branch flag from the row; apply the corresponding output-consumption lemma after interpreting the lookup |

These are lemmas to prove within Layer 5b, not premises to add to the soundness
statement or the instance. Keep the metadata lemmas grouped by family and split
further when a family has different operand modes. Compose those proved facts
with the state-transition lemma.

### Layer 6: control flow

What: prove entry selection and the two next-slot rules in `Agrees` for all cycles before `n`.
Prove the padding suffix properties stated above, including preservation of the tables after cycle `n - 1` when `n > 0`.
For RAM, prove that `RamRa a t * RamInc t = 0` throughout the suffix, for every RAM index `a`; the unselected `RamInc t` need not itself be zero.
Handle `n = 0` and `n = N` explicitly.
Why: Layer 5b handles the state; this handles which bytecode row runs next.
It supplies the `starts` and `linked` fields and connects the defined boundary `n` to the witness's no-op suffix.
Uses: the PC and sequence constraints, Layer 5b.

**Entry address zero:** neither the [program image type nor entry preprocessing](../JoltConstraints/program.lean) excludes it; `get_first_pc` maps it to slot 0.
Jolt's preprocessing also maps address 0 to the no-op entry, and Jolt's tracer initializes `prev_pc` to 0, so an initial PC of 0 produces no executed rows.
This was checked in `crates/jolt-program/src/preprocess/bytecode.rs` (`get_first_pc`) and `tracer/src/lib.rs` (`trace`, `step_emulator`) at revision `43cc043332762034b5f65379441576e06e7a3890`.
We have not established whether `AllConstraints` admits such an instance.
The proof must either rule it out using the existing constraints or derive `n = 0` from entry selection and the no-op flag, then handle the initial device in Layers 7–8.
It must not assume a positive entry address or a positive number of executed steps.

### Layer 7: the relaxed trace

What: use the prefix constructed on the supplied untrusted advice and the tape answers from the witness.
Take the successful execution, linkage and runtime-advice equalities from `Agrees w n prefix state` for the relaxed trace's counterparts of the `HonestTrace` fields.
The required stopping obligations are `stops` (the final source instruction leaves `nextPC` at its own address), `runs_until_stop` (no earlier source instruction did so), and `nonempty` (a nonzero entry address gives a nonempty trace).
These are open. In particular, [B6](./review_completeness_and_soundness.md#b6-the-soundness-statement) records a known unsound stopping case from reading the code: a witness can end at a jump before the tracer's PC stall. A reproduction against Jolt's code is still needed.
Prefix agreement and a padding suffix do not establish these stopping properties.
For an empty prefix, `stops` and `runs_until_stop` are vacuous; `nonempty` still requires excluding a nonzero entry address.
Take the instance facts, including `initialized`, from the context, adapted to the new form of the private input after the Layer 5a model change; `accepted` follows from `expands` and `entryIsRust`.
Why: once all these obligations are resolved, the constructed prefix can be packaged as a relaxed trace.
Uses: the context, Layers 5 and 6, stopping proofs.

### Layer 8: outputs

What: use the endpoint RAM comparison in `Agrees w n prefix state`.
If `n < N`, carry that comparison from `RamVal a n` to `RamValFinal a` using Layer 3's suffix lemma and Layer 6's zero per-word increments on padding; if `n = N`, agreement already compares `RamValFinal` with the final state.
Translate the agreed RAM encoding on the public I/O region into the final device's output bytes and panic flag.
Then use `RamOutputEqPublicIo` to prove that the final device has the instance's output bytes, after trimming trailing zeros, and its panic flag.
For an empty trace, use the initial device.
The panic-store discrepancy in B6 is an open obstacle to this step.
Why: this gives `matches_outputs`; together with Layer 7's relaxed trace, it proves the planned theorem's existential conclusion.
Uses: endpoint agreement from Layers 5b–6, Layer 3's suffix lemma, `RamOutputEqPublicIo`, device semantics.

### Obligations that need particular care

- **Chunk selection alone does not establish address selection.** With 5-bit addresses and
  two 4-bit chunks, one-hot digits `(2, 0)` encode 32, outside the domain `0…31`.
  The full selector is then zero throughout that domain. Layer 1(b) now rules
  this out for bytecode. For RAM, it proves that an all-zero selector forces
  `RamAddress`, read and write values, and all per-word increments to zero.
  Layer 5b still has to justify execution of zero-address instructions; the
  RAM-table facts alone are not a soundness proof for those instructions.
  This example alone is not a satisfying witness for `AllConstraints`.
- **Field-valued histories are not yet machine states.** Layers 2–3 prove update
  equations. Layer 5b must establish and preserve their interpretation as machine
  words. Check arithmetic bounds per expression, especially wide multiplication.
- **Lookup reuse must not assume execution.** `lookupEntryCorrect_*` takes an
  `HonestTraceRow`, which already includes a proof of execution. Reuse pure identities such
  as `and_entry`; separately prove the connection to arbitrary witness operands.
- **Local execution does not establish honest advice or termination.** Running a
  `VirtualAdvice` row with a supplied value does not show that the honest tracer
  supplies that value. Likewise, the shape of padding and the stopping rule need
  proofs before interpreting the witness as a complete relaxed trace.

### Current status and known obstacles

- **Proved, first review chunk:** [Layer0/Field.lean](../JoltConstraints/Soundness/Layer0/Field.lean)
  proves bounded cast injectivity and Boolean decoding. It now also provides
  `two_pow_127_lt_char`, the shared bridge from `charAbove2pow128` to
  `charAbove2pow127`, used by Layer 2's zero-lookup and x0 proofs.
  [Layer1/OneHot.lean](../JoltConstraints/Soundness/Layer1/OneHot.lean) proves unique
  selection when the sum is one, all-zero selection when the sum is zero, and
  the selected-value read rule. These are generic algebraic lemmas; `Chunks.lean`
  now applies the selection lemmas to Jolt's chunk constraints (Layer 1(a)).
  `read_eq_selected` and its helper `selector_eq_ite` are now used by the
  selected-address read lemmas in `Bytecode.lean` and `Ram.lean`.
- **Proved, Layer 0 verifier bounds:** [Layer0/Bounds.lean](../JoltConstraints/Soundness/Layer0/Bounds.lean)
  bounds advice-polynomial variables by 64 and the modeled Dory setup by 72.
  From `ConstraintContext.oneHotFitsSetup`, it derives `chunkBits ≤ 72`, then
  `Fintype.card (Fin (2^chunkBits)) < ringChar F` using the existing `charAbove2pow127`
  assumption, directly matching the generic one-hot lemmas' cardinality premise.
  No honest-prover chunk configuration is assumed. The four lemmas compile at
  the default heartbeat limit; their only axioms are `propext`, `Classical.choice`
  and `Quot.sound`. The setup definition was checked against Jolt revision
  `43cc043332762034b5f65379441576e06e7a3890`; precommitted program tables remain
  outside this model, as documented in `verifier_sizes.lean`. Revisit 72 if those
  `extra_candidates` are modeled.
- **Proved, Layer 0 word encodings:** [Layer0/Words.lean](../JoltConstraints/Soundness/Layer0/Words.lean)
  derives `2^64 < ringChar F` and bounds every 64-bit word's natural value by the
  characteristic. It then proves that equal field encodings imply equal words,
  using bounded cast injectivity.
  All three lemmas compile at the default heartbeat limit and depend only on
  `propext`, `Classical.choice` and `Quot.sound`. No new premise is added to the
  soundness theorem or instance. This covers word encodings; bounds on wider
  arithmetic expressions still need proofs where those expressions are used.
  `Bytecode.lean` now uses the word-encoding bridge to exclude address four.
- **Proved, Layer 1(a) chunk selection:** [Layer1/Chunks.lean](../JoltConstraints/Soundness/Layer1/Chunks.lean)
  proves unique selection in every bytecode and instruction-lookup chunk at every
  cycle. The RAM weight is zero or one; at a cycle, either all RAM chunk entries
  are zero or every RAM chunk selects exactly one entry, according to that weight.
  The helpers use the context and equations obtained from `AllConstraints`,
  together with the existing `charAbove2pow127` assumption where needed. The five
  lemmas compile at the default heartbeat limit and depend only on `propext`,
  `Classical.choice` and `Quot.sound`. No new premise is added to the soundness
  theorem or instance. The combined selectors are handled by the proofs below.
- **Proved, full-selector alternatives:** [Layer1/Products.lean](../JoltConstraints/Soundness/Layer1/Products.lean)
  proves the Boolean-product facts, and [Layer1/Addresses.lean](../JoltConstraints/Soundness/Layer1/Addresses.lean)
  uses address-digit injectivity to show that the full bytecode and RAM selectors
  are each either all zero or select exactly one in-domain address. This holds
  for arbitrary satisfying witnesses, including the zero-bit RAM domain with no
  chunks; its empty product is one. No positive-chunk or in-range-selection
  premise is added. The ten public lemmas compile at the default heartbeat limit
  and depend only on `propext`, `Classical.choice` and `Quot.sound`.
- **Proved, Layer 1(b) selector classification:** [Layer1/Bytecode.lean](../JoltConstraints/Soundness/Layer1/Bytecode.lean)
  rules out all-zero bytecode selection: it would force the next unexpanded PC
  to four, contradicting either the next cycle's preprocessed address or the
  final-cycle zero shift. Every cycle therefore selects exactly one bytecode slot.
  The final-cycle boundary was checked against Jolt revision
  `43cc043332762034b5f65379441576e06e7a3890`: the `NextUnexpandedPC` claim in
  `crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs` is weighted
  by `EqPlusOneOuter`, which the verifier evaluates in
  `crates/jolt-verifier/src/stages/stage3/spartan_shift.rs` using
  `crates/jolt-poly/src/eq_plus_one.rs`. At the maximum input cycle every term
  has a zero bit-flip factor, so the entire successor kernel is zero; it does
  not wrap to cycle zero. `NextUnexpandedPc::extract` in
  `crates/jolt-witness/src/witnesses/pc.rs` also returns zero when no next row exists.
  [Layer1/Instruction.lean](../JoltConstraints/Soundness/Layer1/Instruction.lean)
  uses the checked divisibility of chunk widths to prove a bijection between
  lookup-chunk addresses and small-digit tuples, then proves each lookup selector
  selects exactly one address without bounding its entire domain by the characteristic.
  [Layer1/Ram.lean](../JoltConstraints/Soundness/Layer1/Ram.lean) proves full RAM
  selection is zero exactly when `RamAddress` is zero, and otherwise unique.
  It proves the zero read, write and per-word-increment consequences. Its loose
  remapped-address field bound uses `WitnessParams.logRamK_lt_usizeBits`, the
  modeled 64-bit host's domain-size bound, rather than an extra context premise.
  All eleven current public lemmas compile at the default heartbeat limit and depend
  only on `propext`, `Classical.choice` and `Quot.sound`. No premise was added to
  the soundness theorem or instance. This completes Layer 1(b)'s selector
  classification; instruction execution remains in Layer 5b. Generic selected
  bytecode and RAM read lemmas are also proved, since the classification uses
  them. Their column-specific consequences and the lookup read rule are proved
  in Layer 1(c) below.
  `ram_address_value_lt_char`, originally private, is now public because Layer 3
  reuses its bound to recover a natural-number address from the field equation.
- **Proved and reviewed, Layer 1(c):** [Layer1/BytecodeReads.lean](../JoltConstraints/Soundness/Layer1/BytecodeReads.lean)
  derives the ten bytecode-backed column reads: PC, unexpanded PC, immediate,
  circuit flags, instruction flags, both source-register selectors, the
  destination-register selector, lookup-table flags, and the lookup operand-format flag.
  [Layer1/RamReads.lean](../JoltConstraints/Soundness/Layer1/RamReads.lean)
  derives the raw address, read value and write value at a selected RAM index.
  Layer 3 uses `ram_zero_effects` for zero addresses; the unused generic
  `ram_read_of_address_zero` wrapper was removed, leaving three lemmas here.
  [Layer1/InstructionReads.lean](../JoltConstraints/Soundness/Layer1/InstructionReads.lean)
  reconstructs one full 128-bit lookup address from the `InstructionRa` choices,
  proves its read rule, and collapses the lookup-output and both operand sums.
  This uses exact chunk-width divisibility, without assuming `2^128 < ringChar F`.
  The selected-address hypotheses of the read lemmas are supplied by the proved
  selection lemmas; they are not new soundness premises.
  All twenty-one current public lemmas compile at the default heartbeat limit and depend
  only on `propext`, `Classical.choice` and `Quot.sound`. Layer 1's selector and
  read obligations are complete. Register and RAM histories are handled in Layers 2–3;
  identifying the active lookup table and interpreting its operation and operands
  remain in Layer 4. Ari reviewed these lemmas on 2026-10-10. Recheck the ten
  bytecode wrappers' callers as later layers land and remove any left unused.
- **Proved and reviewed, Layer 2(a):** [Layer2/Registers.lean](../JoltConstraints/Soundness/Layer2/Registers.lean)
  proves zero initialization and the single-cycle register increment from
  `RegistersValEqPrefixRdInc`. Using Layer 1 bytecode selection, it proves both
  source reads and the destination write value, then shows that the next table
  changes only the selected destination, to `RdWriteValue`. An absent operand
  reads zero; a cycle with no destination preserves every entry. This includes
  padding slots and keeps explicit x0 distinct from an absent operand.
  Updates require the next cycle to be inside the table; there is no register
  column at `traceLength`. All six public lemmas compile at the default heartbeat
  limit and depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  The public `sum_before_succ` helper now lives in
  [Helpers/PrefixSum.lean](../JoltConstraints/Soundness/Helpers/PrefixSum.lean),
  so Layer 3 can share it; it needs only an additive commutative monoid and has
  the same allowed axiom dependencies. Ari reviewed the six table lemmas on
  2026-10-10. Keep their match-form statements for now; add `some`/`none`
  corollaries when concrete callers need them.
  No soundness premise was added. `Rs1Ra`, `Rs2Ra`, and `RdWa` column wrappers
  from Layer 1(c) now have callers here.
  The equations were checked against Jolt revision
  `43cc043332762034b5f65379441576e06e7a3890`, in
  `crates/jolt-claims/src/protocols/jolt/relations/registers/{val_evaluation,read_write_checking}.rs`
  and the verifier's `stages/stage5/registers_val_evaluation.rs` and
  `stages/derivations.rs`: the history uses the strict comparison of the write
  cycle with the read cycle, with no initial-register term.
- **Proved and reviewed, Layer 2(b):**
  [Layer2/RegisterMap.lean](../JoltConstraints/Soundness/Layer2/RegisterMap.lean)
  proves encoding/decoding identities and injectivity for canonical source and
  destination operands. `bytecodeRow_rowOk` derives a real row's validity and
  operand canonicality from `context.expands`, using
  `ExpansionRows.expand_program_rowOk`. Its destination facts exclude a virtual
  register alias at index zero when proving that an x0 destination is the
  canonical no-op.
  [Layer2/State.lean](../JoltConstraints/Soundness/Layer2/State.lean) connects every
  initial register-table entry to the actual initial-state word, using
  `initial_state_sourceValue`, and proves that `advance_pc` preserves every
  source value. `context.initialized` supplies the initialization equation;
  no honest trace is assumed.
  [Layer2/ZeroLookup.lean](../JoltConstraints/Soundness/Layer2/ZeroLookup.lean)
  proves that identity RAF with a zero right operand and the RangeCheck table
  gives zero output. The existing `charAbove2pow128` bound makes the full-address
  cast injective. The flag and operand hypotheses are discharged for the
  canonical no-op in
  [Layer2/ZeroRegister.lean](../JoltConstraints/Soundness/Layer2/ZeroRegister.lean).
  Its induction proves `registersVal_x0` at every cycle and
  `x0_write_effect_zero` even at the final cycle, where no next register-table
  column exists. Padding and every other destination leave x0 unchanged.
  These fourteen new public lemmas, the six Layer 2(a) lemmas, and the shared
  prefix-sum helper compile at the default heartbeat limit. Each was audited
  with `#print axioms`: dependencies are subsets of `propext`, `Classical.choice`,
  and `Quot.sound`, with no `sorryAx`, compiler-trust axiom, or project axiom.
  The broader `expand_program_rows_valid` bundle still depends on
  `sys_enable_experimental_extensions`; none of these proofs uses that bundle.
  No premise was added to the soundness theorem or instance. This completes the
  planned Layer 2 obligations; agreement after instruction
  execution remains in Layer 5b.
  `source_encode_decode`, `sourceRegisterAddress_injective`,
  `registersVal_initial_advance_pc`, and `x0_write_effect_zero` currently have no
  callers. Keep them for the planned state and linkage proofs in Layers 5b and 6;
  recheck their callers when those layers land and remove any left unused.

  The three case-split proofs requested for timing were profiled separately
  from the build on 2026-10-10, using Lean 4.29.0-rc4 on this checkout. One run
  per module with `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=5`
  followed by the module's file path reported:

  | Declaration | Proof elaboration | Main theorem kernel check |
  | --- | ---: | ---: |
  | `slot_setWidth` (`Layer2/RegisterMap.lean`) | 0.361 s | 0.017 s |
  | `sourceValue_advance_pc` (`Layer2/State.lean`) | 0.883 s | 0.051 s |
  | `instruction_destination_canonical` (`Layer2/RegisterMap.lean`) | 0.754 s | 0.020 s |

  These are declaration timings with profiling enabled, excluding process
  startup and import loading, not whole-module build times. The profiler also
  reported a 0.031 s kernel check for the generated auxiliary proof of
  `sourceValue_advance_pc`. The default heartbeat limit was unchanged. Keep
  these case splits: the measured times do not warrant rewriting them solely
  for performance. Reprofile if the proofs or instruction set grow.
- **Proved, awaiting review, Layer 3:**
  [Layer3/History.lean](../JoltConstraints/Soundness/Layer3/History.lean) proves
  the initial table, the one-cycle increment, the last-cycle update into
  `RamValFinal`, and equality with the final column when all remaining per-word
  increments vanish. It reuses `sum_before_succ` and takes only the history
  constraints it needs. The last-cycle theorem also covers `traceLength = 1`.
  [Layer3/Updates.lean](../JoltConstraints/Soundness/Layer3/Updates.lean) uses
  selection to replace only the accessed word with `RamWriteValue`, both between
  table cycles and into the final column. A zero address leaves every word
  unchanged; `RamInc` itself need not be zero in this case.
  [Layer3/Access.lean](../JoltConstraints/Soundness/Layer3/Access.lean) derives zero
  address for non-memory cycles and for `IsNoop = 1` padding, and proves that a
  load has zero write effect on every word. This does not assume that padding
  forms a suffix or that a zero-address load executes successfully.
  [Layer3/Address.lean](../JoltConstraints/Soundness/Layer3/Address.lean) recovers
  `raw.toNat = ramLowestAddress + 8 * chosen` from selection and the field
  encoding of a 64-bit raw address, then proves that raw address remaps to
  `chosen`. The execution proof must establish the raw-address encoding from
  its operands; it is a local helper hypothesis, not a new soundness premise.
  [Layer3/State.lean](../JoltConstraints/Soundness/Layer3/State.lean) ties the
  initial table to `context.initialized`, proves agreement of the public and
  initial-state memory layouts, and proves that preparing PC preserves any
  observation of the memory map and Jolt device. In particular, initial RAM
  agreement survives preparing the first instruction's PC.
  All eighteen public Layer 3 lemmas build at the default heartbeat limit and
  have only subsets of the three standard axioms. No soundness or instance
  premise was added. The suffix-zero hypothesis remains for Layer 6 to discharge
  using its padding-suffix proof, `ramAddress_zero_of_padding`, and
  `ram_zero_effects`. Read agreement after execution, including device regions,
  remains in Layer 5b; output and panic agreement remain in Layer 8.
  The history equations were checked against Jolt revision
  `43cc043332762034b5f65379441576e06e7a3890`:
  `crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs` batches the
  current and final histories; the verifier's `stages/stage4/ram_val_check.rs`
  uses `LtPolynomial::evaluate(write_cycle, read_cycle) + gamma`. The strict
  comparison in `crates/jolt-poly/src/lt.rs` gives earlier writes for `RamVal`,
  while the final term includes every cycle. The remapping matches
  `MemoryLayout::remap_word_address` in `common/src/jolt_device.rs`; the
  non-memory and load guards match `crates/jolt-r1cs/src/constraints/rv64.rs`.
  This is a source check of the modeled equations, not a PCS proof.
- **Layer 3 review, address wraparound:** resolved by a new premise.
  [layout_check.lean](../bug-report/ram-address-wraparound/layout_check.lean)
  shows that layout construction and the maximum RAM size alone allow a RAM
  domain past `2^64`; it is not a satisfying witness. Its two lemmas use only
  subsets of the three standard axioms.
  Ari approved replacing the run-based address assumption with the
  instance-only `RamRegionFits` premise on 2026-10-10. NOTE: to confirm with
  a16z. `Layer3/Layout.lean` derives the witness domain bound from the verifier's
  maximum-size check and proves that all eight bytes of every word fit.
  `Layer5/MemoryAddress.lean` derives `encoded` as described in Layer 3,
  including the unselected zero case. The old predicate and next-step helper
  are deleted. The module note, `model_review.md` and B6 of
  `review_completeness_and_soundness.md` now describe the layout premise.
  The main theorem still has its existing `sorry`; compiling it is not a proof
  of soundness.
  The Noop decoder/expansion audit above resolves the metadata TODO for the
  modeled instruction set. Padding suffix and stopping remain open in Layers
  6–7. The remaining Layer 3 lemmas keep their planned callers in Layers 5b,
  6 and 8.
- **Proved and reviewed, Layer 4(a):**
  [Layer4/Table.lean](../JoltConstraints/Soundness/Layer4/Table.lean) collapses
  the table selection, including the no-table case, and derives identity RAF
  from an active arithmetic flag using the selected bytecode row.
  [Layer4/Identity.lean](../JoltConstraints/Soundness/Layer4/Identity.lean)
  recovers the full address using `charAbove2pow128` and evaluates the selected
  table there.
  [Layer4/RangeCheck.lean](../JoltConstraints/Soundness/Layer4/RangeCheck.lean)
  and [Layer4/Arithmetic.lean](../JoltConstraints/Soundness/Layer4/Arithmetic.lean)
  prove the wrapped 64-bit addition, subtraction and multiplication results.
  They retain addition's carry, subtraction's `2^64` bias (also when the right
  input is zero), and every multiplication bit until the table truncates them.
  The pure `rangeCheck_entry` identity moved from the completeness helper into
  [Layer4/RangeCheckEntry.lean](../JoltConstraints/Soundness/Layer4/RangeCheckEntry.lean),
  keeping its name and callers. Its new proof uses ordinary bit-vector lemmas
  and a kernel-checked constant mask instead of bit blasting.
  These twelve public lemmas use only subsets of the three standard axioms,
  build at the default heartbeat limit, and introduce no soundness or instance
  premise. Jolt's `add.rs`, `sub.rs`, `mul.rs`, `tables/range_check.rs` and the
  arithmetic rows of `jolt-r1cs/src/constraints/rv64.rs` were checked at
  `43cc043`; no mismatch was found in this chunk.
  Connecting instruction inputs and destination writes to execution belongs
  to Layer 5b.
  The requested timing check for `instructionRafFlag_one_of_arithmetic` measured
  0.386 s for proof elaboration and 0.0025 s for kernel checking, excluding
  imports, with Lean's trace profiler on the unchanged theorem text. The default
  heartbeat limit was unchanged. This does not justify rewriting the proof
  for performance. Advice rows follow the separate word-recovery route in
  Layer 4 above; they do not need an input-determined identity address.
- **Proved and reviewed, Layer 4(b), operand recovery:**
  [Layer4/Interleave.lean](../JoltConstraints/Soundness/Layer4/Interleave.lean)
  proves the bit-unpacking identities, both round trips, and agreement between
  the field operand polynomials and the decoded words. Five existing pure
  lemmas moved from the completeness helper, retaining their names and callers.
  Their two native `bv_decide` proofs introduced compiler-generated axioms, so
  those proofs were replaced by kernel-checked bit simplification, split into
  four private lemmas covering sixteen bit positions each.
  [Layer4/Interleaved.lean](../JoltConstraints/Soundness/Layer4/Interleaved.lean)
  uses the two RAF equations and word-cast injectivity to recover both operands,
  their unique interleaved address, and the selected table's entry there.
  These files contain eleven public lemmas: six new and five moved. The weaker
  `charAbove2pow127` bound suffices because each operand is a 64-bit word.
  RAF zero and operand agreement remain local obligations for later instruction
  proofs; no soundness or instance premise was added.
  `lake build JoltConstraints` passes, including the existing completeness
  callers. All eleven public lemmas' axiom lists contain only subsets of
  `propext`, `Classical.choice` and `Quot.sound`. The default heartbeat limit
  is unchanged. Replacing `norm_num` with targeted `simp only` reduced the
  four bit-unpacking helpers from the earlier 2.29–2.33 s each. The follow-up
  timing audit below measures their current proofs and both `WordEntry` mask
  computations. The four bounded sixteen-position case splits remain; a proof
  through the mask stages is a possible later refactor. The earlier full build
  reported 6.2 s for `Interleave.lean`, including imports and concurrent jobs.
  Docstrings now describe both interleaving bit lemmas and every bitwise and
  comparison entry lemma.
  Jolt's `interleave.rs` and stage-5 `instruction_read_raf.rs` were checked at
  `43cc043`; the odd-left/even-right convention agrees with the model.
- **Proved and reviewed, Layer 4(b), table operations:**
  [Layer4/Bitwise.lean](../JoltConstraints/Soundness/Layer4/Bitwise.lean) and
  [Layer4/Comparison.lean](../JoltConstraints/Soundness/Layer4/Comparison.lean)
  interpret AND, OR, XOR, ANDN, equality, inequality, unsigned comparisons and
  signed comparisons. Their eleven witness lemmas use `lookupOutput_of_interleaved`
  and eleven pure identities in the matching `Entry` files. The pure identities
  moved from completeness with their names and callers retained. All 45 public
  lemmas in Layer 4(a–b) were audited: only the three standard axioms occur.
  The modules build at the default heartbeat limit. Ari reviewed these table
  interpretations on 2026-10-10. The eleven table operations were checked against
  Jolt's `materialize_entry` implementations at `43cc043`; no mismatch was found.
- **Proved and reviewed, Layer 4(c):**
  [Layer4/Word.lean](../JoltConstraints/Soundness/Layer4/Word.lean) interprets
  word slices, sign extension, aligned addresses, powers, shift masks, byte
  reversal and window masks.
  [Layer4/WordArithmetic.lean](../JoltConstraints/Soundness/Layer4/WordArithmetic.lean)
  composes these results with the arithmetic constraints for ADDW/SUBW/MULW
  and the high product used by MULHU.
  [Layer4/Conditional.lean](../JoltConstraints/Soundness/Layer4/Conditional.lean)
  covers sign masks, conditional negation, division checks and store lanes.
  [Layer4/Shift.lean](../JoltConstraints/Soundness/Layer4/Shift.lean),
  [Layer4/Rotate.lean](../JoltConstraints/Soundness/Layer4/Rotate.lean) and
  [Layer4/Pext.lean](../JoltConstraints/Soundness/Layer4/Pext.lean) cover the four
  right shifts, twelve XOR-rotate tables, and both unsigned and signed extraction
  for arbitrary masks. Shift interpretations require the appropriate right-shift
  mask as a local hypothesis; Layer 5b must derive that shape from expansion and
  the earlier mask-producing row or immediate. The other operand-agreement
  hypotheses likewise belong to the execution induction.

  [Layer4/Assertions.lean](../JoltConstraints/Soundness/Layer4/Assertions.lean)
  interprets halfword alignment, word alignment and multiplication without
  overflow. [Layer4/Inputs.lean](../JoltConstraints/Soundness/Layer4/Inputs.lean)
  recovers the input-source selection from bytecode and proves that RAF zero
  preserves both instruction inputs.
  [Layer4/Outputs.lean](../JoltConstraints/Soundness/Layer4/Outputs.lean) connects
  lookup outputs to register writes and branch decisions, and proves that an
  active assertion establishes its table predicate.
  [Layer4/Advice.lean](../JoltConstraints/Soundness/Layer4/Advice.lean) recovers
  a 64-bit RangeCheck output without an input-determined address. It supplies
  the advice word, without claiming that internal runtime advice is correct.

  All 55 `LookupTableKind` constructors are accounted for: 53 have operation
  interpretations; [Layer4/Reachable.lean](../JoltConstraints/Soundness/Layer4/Reachable.lean)
  proves the other two (`VirtualROTR`, `VirtualROTRW`) cannot be selected by
  bytecode expanded from the current `SourceInstruction` type. It uses
  `bytecodeRow_rowOk`'s `immShift` fact, not the broader execution-validity bundle.
  This exclusion is specific to the modeled language: Jolt's
  `expand/inline.rs::rotri` and `rotri32` can emit these instructions, but inline
  source opcodes `0x0B` and `0x2B` are already outside `SourceInstruction`.

  The matching `Entry` files hold the pure identities shared with completeness.
  The shift and PEXT helpers moved there with compatibility imports at their
  old paths. The moved word, sign-mask and rotation proofs now avoid native
  evaluation; their constant checks and bit-vector steps are kernel checked.
  All modules are imported by `JoltConstraints.lean`, and `lake build
  JoltConstraints` passes, including the completeness callers. All 162 public
  Layer 4 theorems were checked with `#print axioms`: only subsets of `propext`,
  `Classical.choice` and `Quot.sound` occur. No heartbeat limit, soundness premise
  or instance premise was added.

  The same declaration timing audit found a maximum of 0.146 s in `PextEntry`
  (`pextSigned_eq_jolt_virtual_pext_signed_value`) and 0.175 s in `ShiftEntry`
  (`sign_foldl`); their other declarations were below those times. Both use
  loop invariants and induction. The full build reported 3.6 s and 3.3 s for
  those modules respectively. A follow-up audit on 2026-10-10 measured the
  remaining case-split proofs with one Lean worker, excluding imports. It used
  `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true
  -Dtrace.profiler.threshold=50` on each source file. Explicit `Elab.async`
  tracing also reports declarations below the 50 ms threshold. Times below are
  proof elaboration and the sum of the following kernel `Lean.addDecl` checks;
  they are measurements of this run, not performance bounds.

  | File and lemma | Proof elaboration | Kernel checks |
  |---|---:|---:|
  | `Interleave.lean: uninterleave_snd_bits_0_15` (private) | 1.165 s | 0.039 s |
  | `Interleave.lean: uninterleave_snd_bits_16_31` (private) | 1.164 s | 0.037 s |
  | `Interleave.lean: uninterleave_snd_bits_32_47` (private) | 1.158 s | 0.040 s |
  | `Interleave.lean: uninterleave_snd_bits_48_63` (private) | 1.161 s | 0.040 s |
  | `WordEntry.lean: shiftRightBitmask_value` | 0.053 s | 0.009 s |
  | `WordEntry.lean: shiftRightBitmaskW_value` | 0.026 s | 0.004 s |

  These timings support retaining the bounded case splits for now, with the
  default heartbeat limit. `Interleave` uses `simp only`; the two `WordEntry`
  lemmas use kernel-checked `decide` after the case split. Every public helper
  in `ShiftEntry` and `PextEntry` now has a docstring. Their names and visibility
  are preserved for existing callers. Ari reviewed all of Layer 4 by reading on
  2026-10-10; compilation and axiom checks were run separately as recorded above.

  The remaining table families' `materialize_entry`
  functions, including the PEXT and byte-reversal helpers, were checked against
  Jolt at `43cc043`; no translation mismatch was found in those definitions.
- **Resolved scope, Layer 4:** the Akita address alias is excluded by a
  feature-gated constraint already present in Jolt at `43cc043`, but that
  constraint is explicitly outside our base model. With Ari's approval on
  2026-10-10, the main theorem now requires `2^128 < ringChar F`; the proved
  Layer 0–1 lemmas retain their weaker bounds. Akita will be modeled separately
  as a non-succinct constraint relation, with PCS security outside scope.
  The detailed source audit is in Layer 4 above.
- **SC advice (runtime-advice agreement):** SC.W can report failure when the reservation holds;
  the honest tracer reports success. The reproducer was reported as
  [a16z/jolt#2037](https://github.com/a16z/jolt/issues/2037). SC.D has the same
  one-way check; only SC.W was run. With Ari's approval on 2026-10-10, the main
  theorem now temporarily assumes `NoStoreConditional`, excluding both instructions
  from the source program. The `FIXME` requires removing this premise after the
  constraints and model are fixed; the underlying issue remains unresolved.
- **Stopping and panic (Layers 7–8):** the two cases under "Known not sound for
  this L" in [B6](./review_completeness_and_soundness.md#b6-the-soundness-statement)
  are findings from reading the code; they still need reproductions.
- **Layer 5a implemented and reviewed by reading:**
  [TapeSemantics.lean](../JoltConstraints/Soundness/Layer5/TapeSemantics.lean)
  defines independent 64-bit tape answers and proves that a successful
  fixed-tape step has exactly the same post-state under the relaxed rule.
  [TapeTrace.lean](../JoltConstraints/Soundness/Layer5/TapeTrace.lean) defines
  relaxed runs, completed traces and their language. Its embeddings retain
  the entire original trace, including runtime advice, outputs and stopping
  requirements, and prove `inLanguage_implies_untrustedAnswerLanguage`.
  [NarrowAdvice.lean](../JoltConstraints/Soundness/Layer5/NarrowAdvice.lean)
  proves the multiply/shift post-processing returns the signed low-width word
  for every width in `1..64`. The generated `AdviceLB`, `AdviceLH` and `AdviceLW`
  expansions use those operations at widths 8, 16 and 32 in both destination
  branches, including the x0 temporary-register branch. The generic value
  identity is proved here; the expansion shapes and their full execution are
  now proved in the Layer 5b narrow-advice chunk below. Connecting the resulting
  states to the witness tables remains open.

  All three modules are imported by `JoltConstraints.lean`; `lake build
  JoltConstraints` passes. The five public theorems and two embedding definitions
  were checked with `#print axioms`. The step and trace inclusion results use
  exactly `propext`, `Classical.choice`, `Quot.sound` and the allowed Sail constant
  `sys_enable_experimental_extensions`, through the instruction semantics in
  their statements. `narrowAdvice_value` uses only the three standard axioms.
  No new `sorry`, compiler-trust axiom or heartbeat setting was introduced.
  The existing main theorem remains unfinished and fixed-tape; no premise or
  instance definition was changed in the Layer 5a chunk. The later approved
  layout-premise replacement is recorded in the Layer 5b entry below.

  The review clarified the remaining narrow-expansion execution obligation and
  the need to keep the duplicated trace requirements synchronized. The relaxed
  load's error message now says only `invalid width`: it cannot exhaust a tape.

  The provisional advice contract is recorded in `model_review.md`.
  A complete satisfying witness with inconsistent length answers has not been
  constructed; fixed-tape soundness and a16z's answer about `bytes_remaining()`
  remain open. Layer 5a was reviewed before starting 5b. `CodeUnchanged`
  needs no relaxed counterpart for bytecode execution.
- **Layer 5b, address chunk proved and ready for review:**
  [Layer3/Layout.lean](../JoltConstraints/Soundness/Layer3/Layout.lean) defines
  the approved `RamRegionFits` premise, with `NOTE: to confirm with a16z`,
  and proves two lemmas: the witness-domain bound and the bound on every byte
  of each word. The former run-based predicate and its next-step helper are
  deleted; the main theorem now takes `ramRegionFits`.
  [Layer5/MemoryAddress.lean](../JoltConstraints/Soundness/Layer5/MemoryAddress.lean)
  proves seven public lemmas. The address constraint gives the field encoding
  of the signed sum; the selected and unselected cases recover integer
  equality, including zero; the layout bound then gives the machine range and
  address encoding. The LD and SD lemmas derive the flags and signed immediate
  from the selected bytecode row. Their source-column equality is a local
  induction obligation, not a new soundness premise.

  `lake build JoltConstraints` passes. All nine new public lemmas were checked
  with `#print axioms` and use only `propext`, `Classical.choice` and `Quot.sound`.
  There are no new `sorry`s, compiler-trust axioms or heartbeat settings.
  The existing unfinished `JoltInstance.soundness` was checked separately: it
  still has `sorryAx`, plus the three standard axioms and
  `sys_enable_experimental_extensions`; it remains a fixed-tape target.
  This closes the address-wraparound subproblem under the approved premise.
  Layer 5b still must establish source-register agreement, successful execution
  and post-state agreement, including memory/device behavior at address zero.
- **Layer 5b, narrow-advice execution proved and ready for review:**
  [Program.lean](../JoltConstraints/Soundness/Layer5/Program.lean) composes
  `execWithTapeAnswer` over a generated program. Answers are indexed by local
  row number; only tape instructions use them. Errors and non-success results
  stop execution as in the original `execProgram`. Its step lemma passes the
  exact post-state to the next row.
  [AdviceExpansion.lean](../JoltConstraints/Soundness/Layer5/AdviceExpansion.lean)
  proves the actual `AdviceLB`, `AdviceLH` and `AdviceLW` expansion shapes and
  their execution under this rule. The final state advances the cursor by
  1, 2 or 4 and writes the sign-extended low 8, 16 or 32 bits of the first
  answer. Later row answers have no effect. For rd = x0 the generated sequence
  uses temporary register 40, so the cursor still advances and architectural
  x0 is unchanged. Other state is preserved by the full-state result
  `afterAdviceLoad`, which uses the existing `NativeDispatch.afterDst` model.

  The load establishes the value read by the arithmetic rows, so the proofs
  require no initial register-presence hypothesis. Small read-after-write and
  write-overwrite helpers reuse the existing register proofs; no new finite
  register enumeration or heartbeat setting is needed. All eight new public
  lemmas were checked with `#print axioms`: the three expansion-shape lemmas
  use `propext` and `Quot.sound`; the five execution/composition lemmas use the
  standard three axioms plus the allowed `sys_enable_experimental_extensions`.
  There are no new `sorry`s, compiler-trust axioms or soundness premises.
  Both modules are included in `JoltConstraints.lean`; `lake build
  JoltConstraints` passes. Module builds reported 2.5 s for `Program.lean`
  and 3.5 s for `AdviceExpansion.lean`; these include more than proof elaboration.
  Witness selection, answer recovery and table agreement at the intermediate
  rows still need to be connected to these execution results in the induction;
  this chunk does not establish all of Layer 5b.
- **Layer 5b, register agreement proved and ready for review:**
  [Registers.lean](../JoltConstraints/Soundness/Layer5/Registers.lean) defines
  `RegisterAgreement` and proves four public lemmas: initialization, preservation
  through `advance_pc`, successful canonical-operand reads with table encoding,
  and preservation through a selected instruction's destination write.
  The invariant includes every Sail register's presence, established from
  `initial_state` and preserved using existing write and PC lemmas. The write
  proof combines Layer 2's table update with read-after-write and frame facts,
  derives canonicality from expansion, and uses `registersVal_x0` for x0.
  It covers architectural and virtual destinations without new register
  enumeration. Its successful-write and `RdWriteValue` encoding hypotheses
  must still be proved for each instruction family. RAM, device state and
  control flow are outside this register-only chunk.

  The module is imported by `JoltConstraints.lean`; `lake build JoltConstraints`
  passes. Its module build reported 3.7 s. All four public lemmas were checked
  with `#print axioms` and use only `propext`, `Classical.choice` and `Quot.sound`.
  No new `sorry`, heartbeat setting or soundness premise was introduced.
- **Layer 5b, ADDI execution and register agreement proved and ready for review:**
  [RegisterWrite.lean](../JoltConstraints/Soundness/Layer5/RegisterWrite.lean)
  defines the concrete state `afterWriteDst` and proves that writing any
  canonical destination reaches it. A virtual destination cannot alias a
  protected architectural index: the proof uses register-address injectivity
  and width bounds, without enumerating the 32 architectural registers.
  [AddImmediate.lean](../JoltConstraints/Soundness/Layer5/AddImmediate.lean)
  proves `addi_step` from the context, constraints, selected ADDI row and
  current register agreement. Private lemmas derive operand canonicality,
  metadata, input encodings and the wrapped write value before composing
  execution with `RegisterAgreement.write`. Neither a successful-write
  hypothesis nor a write-value hypothesis is left to the caller.

  The theorem includes architectural and virtual operands and x0. It accepts
  the row's already-decoded 64-bit immediate, including arithmetic wraparound.
  Its exact execution state is `afterWriteDst`; register agreement is proved
  whenever the next column exists. The execution and write-value results do
  not require a next column. Full RAM agreement, bytecode linkage and the
  remaining instruction families are still open.

  Both modules are in the `JoltConstraints` build, which passes. Module builds
  reported 3.6 s for `RegisterWrite` and 4.1 s for `AddImmediate`.
  `#print axioms` checked both public lemmas: the write helper uses only the
  three standard axioms; `addi_step` also includes the allowed Sail constant
  `sys_enable_experimental_extensions`, without assuming its value.
  No new soundness premise, `sorry`, compiler-trust axiom, heartbeat setting
  or finite register enumeration was introduced.

## Questions for a16z

Collected here so they can be sent together. Each item states what we assume meanwhile.

1. **Is the answer to `bytes_remaining()` untrusted, like advice values?**
   Before proving, the prover prepares the tape, for example `[7, 3, 9]`.
   A read takes the next byte; `bytes_remaining()` says how many bytes are left (3 at the start).
   The constraints only check that each answer is a 64-bit number.
   If a guest calls `bytes_remaining()` twice with no read in between, we found no constraint that rules out answers 3 and then 100, although a real tape answers 3 both times. We have not constructed a complete satisfying witness for this example.
   The runtime advice page says advice values are untrusted but does not mention `bytes_remaining()`.
   If the answer may be arbitrary, guests must validate any property they rely on. If it is meant to be accurate, which constraint enforces that guarantee?
   Assumed meanwhile: untrusted (Layer 5a).
2. **Can we assume the RAM region `[lowest, lowest + 8·maxRamSize)` fits below `2^64`?**
   This bounds the verifier's maximum padded RAM domain, including every byte
   of its last word. We use it with the RAM-size check and the address
   constraints to derive nonwrapping addresses for satisfying LD/SD cycles,
   independently of the tape specification.
   Assumed meanwhile: `RamRegionFits`, approved by Ari on 2026-10-10.
   NOTE: to confirm with a16z.

## First milestone

Layer 1(b)'s selector proofs and Layer 1(c)'s read proofs have been reviewed.
Layer 2's register proofs and review corrections are complete. Layer 3's eighteen
RAM lemmas are proved and ready for review: histories, boundary updates,
non-memory and load effects, remapping, initialization, and PC preparation.
Layer 3's review exposed the address-wraparound case; Ari approved the instance-only
`RamRegionFits` premise, pending a16z's confirmation. The integer no-wrap
derivation and machine-address encoding are proved in Layer 5b.
Layer 4(a)'s twelve lemmas cover table selection, identity-address recovery,
and arithmetic RangeCheck. Layer 4(b) is proved and reviewed: operand recovery
and bitwise/comparison table operations. Layer 4(c) is also proved and reviewed,
including the remaining table operations, input/output connections and
advice word recovery. Layer 5a now adds the relaxed tape semantics and proves
fixed-tape inclusion and narrow-answer truncation. It is built and reviewed by
reading. Layer 5b now includes the address proofs, full execution of the
three narrow-advice expansions, and the shared register-agreement invariant
with initialization, read and write rules. ADDI now derives its local write
and witness encoding and preserves register agreement. The remaining
instruction families must do the same, and these results still need to be
connected to RAM agreement and the execution-prefix induction.
The separate Akita model remains future work.
