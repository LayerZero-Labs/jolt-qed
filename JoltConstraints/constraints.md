# Jolt constraints

Source: the base RV64 relations at [Rust commit `e012da54`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-r1cs/src/constraints/rv64.rs). GitHub links are documentation pointers; reviews of current behavior must scan the local Jolt checkout.

A checked box means the stated honest-witness theorem is proved in Lean without
`sorryAx`. The status labels are `DONE:` for a checked proof, `TODO:` for
unfinished proof or correspondence work, and `FIXME:` for a confirmed issue.
This tracks proof status under each theorem's stated premises; it does not by
itself establish that all Rust executions satisfy those premises. The Lean
source and `#print axioms` were checked for all 62 numbered targets: 52 are
`DONE:`, eight are `TODO:`, and two are `FIXME:`.

The `FIXME:` targets are (01), blocked by the confirmed
[wrapping-load completeness bug](../bug-report/ram-address-wrap.md), and (16),
whose [taken self-branch counterexample](../bug-report/self-branch.md) leaves
its unrestricted target as a statement rather than a theorem. The eight `TODO:`
targets are (26), (34)–(39), and (42); none is classified as a confirmed
Jolt bug. Among them, (26), (37)–(39) still need Rust–Lean correspondence
checks, while the others need proof and trace-invariant work.

Constraint (12) has a proved conditional completeness theorem requiring
equality-assertion operands to match;
Rust's intentionally unsatisfiable spoil execution makes the unrestricted claim
false. Constraint (13) has a proved theorem for valid Lean trace rows; the
historical Rust counterexample was fixed in Jolt, as recorded in the
[CSRRS report](../bug-report/issue.md). Deriving Lean's program-row validity
certificate from every Rust expansion remains separate work. Constraint (15)
has a proved honest-witness theorem for padded traces; its proof has no
`sorryAx` dependency. Some other targets need additional program/trace
validity conditions.
The completeness theorem for constraint (22) explicitly requires at least one padding cycle, as Rust's
trace-length calculation guarantees. The completeness theorem for (58) requires
at least one RAM chunk. The register completeness targets require zero initial
registers and still need admissible-register and history assumptions.

Equations (43)–(47) were rechecked against Rust commit `e012da54c3bb26a6436b5ca74e86c19bb39695ad`. Their honest-witness targets now require the exact Rust bytecode domain, including the leading no-op and power-of-two padding.

The remaining equations (23)–(26), (37)–(38), (40)–(41), (48)–(53), and (59)
were also checked against Rust commit `e012da54c3bb26a6436b5ca74e86c19bb39695ad`.
This checklist covers the base RV64 relations; optional `akita` relations,
including its extra instruction-address canonicality condition, are outside it.
The final RAM and public-I/O completeness targets still need memory-history,
layout, and termination assumptions. Constraint (53) takes the public entry slot
explicitly and requires the trace to start there. Constraint (50) selects the
destination recorded in the final bytecode row, including x0. The
[`JoltTraceRow` load-capture condition](trace.lean) separately requires a load's
captured RAM value to equal its captured destination value; it rejects a raw
`LD x0` of a nonzero word without rewriting that destination.

The current model audit and changes to previously accepted definitions are recorded in
[model_review.md](model_review.md). Matching constraint equations does not
certify every current completeness statement.

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

- [ ] (01) FIXME: [RAM address for loads and stores](Constraints/RamAddrEqRs1PlusImmIfLoadStore.lean)
- [x] (02) DONE: [Zero RAM address for other instructions](Constraints/RamAddrEqZeroIfNotLoadStore.lean)
- [x] (03) DONE: [Loads preserve RAM](Constraints/RamReadEqRamWriteIfLoad.lean)
- [x] (04) DONE: [Loads copy RAM to the destination](Constraints/RamReadEqRdWriteIfLoad.lean)
- [x] (05) DONE: [Stores copy the second source to RAM](Constraints/Rs2EqRamWriteIfStore.lean)
- [x] (06) DONE: [Zero left lookup operand for add/subtract/multiply](Constraints/LeftLookupZeroIfAddSubMul.lean)
- [x] (07) DONE: [Left lookup operand for other modes](Constraints/LeftLookupEqLeftInputOtherwise.lean)
- [x] (08) DONE: [Addition lookup operand](Constraints/RightLookupAdd.lean)
- [x] (09) DONE: [Subtraction lookup operand](Constraints/RightLookupSub.lean)
- [x] (10) DONE: [Multiplication lookup operand](Constraints/RightLookupEqProductIfMul.lean)
- [x] (11) DONE: [Right lookup operand for other modes](Constraints/RightLookupEqRightInputOtherwise.lean)
- [x] (12) DONE: [Assertion lookup output](Constraints/AssertLookupOne.lean)
- [x] (13) DONE: [Write lookup output to the destination](Constraints/RdWriteEqLookupIfWriteLookupToRd.lean)
- [x] (14) DONE: [Jump return address](Constraints/RdWriteEqPCPlusConstIfJump.lean)
- [x] (15) DONE: [Next address after a jump](Constraints/NextUnexpandedPCEqLookupIfShouldJump.lean)
- [ ] (16) FIXME: [Next address after a taken branch](Constraints/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean)
- [x] (17) DONE: [Next address for other rows](Constraints/NextUnexpandedPCUpdateOtherwise.lean)
- [x] (18) DONE: [Next expanded PC within a virtual sequence](Constraints/NextPCEqPCPlusOneIfInline.lean)
- [x] (19) DONE: [Start virtual sequences at their beginning](Constraints/MustStartSequenceFromBeginning.lean)

[Rust: the 19 equality-conditional rows](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-r1cs/src/constraints/rv64.rs#L121).

∀ t ∈ T; every column in this block is evaluated at t:

```text
(01) (Load + Store) · (RamAddress − Rs1Value − Imm) = 0

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

(15) ShouldJump · (NextUnexpandedPC − LookupOutput) = 0

(16) ShouldBranch · (NextUnexpandedPC − UnexpandedPC − Imm) = 0

(17) (1 − ShouldBranch − Jump)
       · (NextUnexpandedPC − UnexpandedPC − 4
          + 4·DoNotUpdateUnexpandedPC + 2·IsCompressed) = 0

(18) (VirtualInstruction − IsLastInSequence) · (NextPC − PC − 1) = 0

(19) (NextIsVirtual − NextIsFirstInSequence) · (1 − DoNotUpdateUnexpandedPC) = 0
```

## SpartanProductVirtualization — stage 2

- [x] (20) DONE: [Product of instruction inputs](Constraints/ProductEqLeftInputMulRightInput.lean)
- [x] (21) DONE: [ShouldBranch product](Constraints/ShouldBranchEqLookupOutputMulBranch.lean)
- [x] (22) DONE: [ShouldJump product](Constraints/ShouldJumpEqJumpMulNotNextIsNoop.lean)

[Rust: the three product rows](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-r1cs/src/constraints/rv64.rs#L367); [sumcheck](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/spartan/product_remainder.rs).

∀ t ∈ T:

```text
(20) Product(t) = LeftInstructionInput(t) · RightInstructionInput(t)

(21) ShouldBranch(t) = LookupOutput(t) · Branch(t)

(22) ShouldJump(t) = Jump(t) · (1 − NextIsNoop(t))
```

## RamReadWriteChecking — stage 2

- [x] (23) DONE: [RAM read-value selection](Constraints/RamReadValueEqRamRead.lean)
- [x] (24) DONE: [RAM write-value selection](Constraints/RamWriteValueEqRamReadWrite.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs#L89).

∀ t ∈ T:

```text
(23) RamReadValue(t) = Σ_{a ∈ M} RamRa(a,t) · RamVal(a,t)

(24) RamWriteValue(t) = Σ_{a ∈ M} RamRa(a,t) · (RamVal(a,t) + RamInc(t))
```

## RamRafEvaluation — stage 2

- [x] (25) DONE: [RAM address reconstruction](Constraints/RamAddressEqRamRaf.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs#L133).

`lowest_address` is the memory layout's lowest byte address; remapped word `a` has byte address `lowest_address + 8a`.

```text
(25) ∀ t ∈ T:
       RamAddress(t) = Σ_{a ∈ M} (lowest_address + 8a) · RamRa(a,t)
```

## RamOutputCheck — stage 2

- [ ] (26) TODO: [Public RAM output](Constraints/RamOutputEqPublicIo.lean)

[Rust: constraint](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs#L115); [public arrays](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/preprocess/public_io.rs#L20).

`IoMask(a) = [io_mask_start ≤ a < io_mask_end]`. `ValIo` contains the public input/output words, the panic word, and termination word 1 when not panicking; other entries are zero, exactly as in `PublicIoMemory::new`.

```text
(26) ∀ a ∈ M:
       IoMask(a) · (RamValFinal(a) − ValIo(a)) = 0
```

## SpartanShift — stage 3

- [x] (27) DONE: [NextUnexpandedPC shift](Constraints/NextUnexpandedPCEqShift.lean)
- [x] (28) DONE: [NextPC shift](Constraints/NextPCEqShift.lean)
- [x] (29) DONE: [NextIsVirtual shift](Constraints/NextIsVirtualEqShift.lean)
- [x] (30) DONE: [NextIsFirstInSequence shift](Constraints/NextIsFirstInSequenceEqShift.lean)
- [x] (31) DONE: [NextIsNoop shift](Constraints/NextIsNoopEqShift.lean)

[Rust: constraint](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs#L103); [non-wrapping successor](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-poly/src/eq_plus_one.rs#L1).

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

- [x] (32) DONE: [Left instruction-input selection](Constraints/LeftInstructionInputEqSelection.lean)
- [x] (33) DONE: [Right instruction-input selection](Constraints/RightInstructionInputEqSelection.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L102).

∀ t ∈ T:

```text
(32) LeftInstructionInput(t) =
       LeftOperandIsRs1Value(t) · Rs1Value(t)
       + LeftOperandIsPC(t) · UnexpandedPC(t)

(33) RightInstructionInput(t) =
       RightOperandIsRs2Value(t) · Rs2Value(t)
       + RightOperandIsImm(t) · Imm(t)
```

## RegistersReadWriteChecking — stage 4

- [ ] (34) TODO: [Destination register write-value selection](Constraints/RdWriteValueEqRegistersReadWrite.lean)
- [ ] (35) TODO: [First source register value selection](Constraints/Rs1ValueEqRegistersRead.lean)
- [ ] (36) TODO: [Second source register value selection](Constraints/Rs2ValueEqRegistersRead.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs#L97).

∀ t ∈ T:

```text
(34) RdWriteValue(t) = Σ_{r ∈ R} RdWa(r,t) · (RegistersVal(r,t) + RdInc(t))

(35) Rs1Value(t) = Σ_{r ∈ R} Rs1Ra(r,t) · RegistersVal(r,t)

(36) Rs2Value(t) = Σ_{r ∈ R} Rs2Ra(r,t) · RegistersVal(r,t)
```

## RamValCheck — stage 4

- [ ] (37) TODO: [RAM value from preceding increments](Constraints/RamValEqInitialPlusPrefixRamInc.lean)
- [ ] (38) TODO: [Final RAM value from all increments](Constraints/RamValFinalEqInitialPlusRamInc.lean)

[Rust: constraint](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135); [initial public RAM](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/preprocess/ram.rs#L134).

`Init(a)` is the initial word array: the program image and public inputs, together with the trusted/untrusted advice words at their memory-layout addresses, zero elsewhere. Advice words are inputs to this array, not additional public constants.

```text
(37) ∀ a ∈ M, ∀ t ∈ T:
       RamVal(a,t) = Init(a) + Σ_{s ∈ T, s < t} RamRa(a,s) · RamInc(s)

(38) ∀ a ∈ M:
       RamValFinal(a) = Init(a) + Σ_{s ∈ T} RamRa(a,s) · RamInc(s)
```

## InstructionReadRaf — stage 5

- [ ] (39) TODO: [Lookup output from the selected table](Constraints/LookupOutputEqInstructionReadRaf.lean)
- [x] (40) DONE: [Left lookup operand reconstruction](Constraints/LeftLookupOperandEqInstructionRaf.lean)
- [x] (41) DONE: [Right lookup operand reconstruction](Constraints/RightLookupOperandEqInstructionRaf.lean)

[Rust: constraint](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/instruction/read_raf.rs#L90); [operand coefficients](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L180).

Let `Q` be the variants of [`LookupTableKind<64>`](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-lookup-tables/src/tables/mod.rs#L137). The fixed array `Table_q(x)` is Rust's `q.evaluate_mle(bits(x))` at the 128-bit Boolean encoding of `x`.

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

## RegistersValEvaluation — stage 5

- [ ] (42) TODO: [Register value from preceding increments](Constraints/RegistersValEqPrefixRdInc.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs#L69).

```text
(42) ∀ r ∈ R, ∀ t ∈ T:
       RegistersVal(r,t) = Σ_{s ∈ T, s < t} RdWa(r,s) · RdInc(s)
```

The empty sum at `t = 0` is zero.

## BytecodeReadRaf — stages 6a–6b

- [x] (43) DONE: [Expanded PC from bytecode](Constraints/PCEqBytecodeRead.lean)
- [x] (44) DONE: [Unexpanded PC from bytecode](Constraints/UnexpandedPCEqBytecodeRead.lean)
- [x] (45) DONE: [Immediate from bytecode](Constraints/ImmEqBytecodeRead.lean)
- [x] (46) DONE: [Circuit flags from bytecode](Constraints/OpFlagsEqBytecodeRead.lean)
- [x] (47) DONE: [Instruction flags from bytecode](Constraints/InstructionFlagsEqBytecodeRead.lean)
- [x] (48) DONE: [First source selector from bytecode](Constraints/Rs1RaEqBytecodeRead.lean)
- [x] (49) DONE: [Second source selector from bytecode](Constraints/Rs2RaEqBytecodeRead.lean)
- [x] (50) DONE: [Destination selector from bytecode](Constraints/RdWaEqBytecodeRead.lean)
- [x] (51) DONE: [Lookup-table flags from bytecode](Constraints/LookupTableFlagEqBytecodeRead.lean)
- [x] (52) DONE: [Instruction RAF flag from bytecode](Constraints/InstructionRafFlagEqBytecodeRead.lean)
- [x] (53) DONE: [Entry bytecode row](Constraints/BytecodeRaAtEntryEqOne.lean)

[Rust: row values](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L533); [PC and entry](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L358).

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

Here `f` ranges over all 14 `CircuitFlags`, `g` over all 6 `InstructionFlags`, `r ∈ R`, and `q ∈ Q`. Missing register/table operands give zero indicators.

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

- [x] (54) DONE: [Instruction chunk selector booleanity](Constraints/InstructionRaChunkBooleanity.lean)
- [x] (55) DONE: [Bytecode chunk selector booleanity](Constraints/BytecodeRaChunkBooleanity.lean)
- [x] (56) DONE: [RAM chunk selector booleanity](Constraints/RamRaChunkBooleanity.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs#L25).

∀ t ∈ T, ∀ u ∈ U, and every chunk d in the respective family:

```text
(54) InstructionRaChunk_d(u,t) · (InstructionRaChunk_d(u,t) − 1) = 0

(55) BytecodeRaChunk_d(u,t) · (BytecodeRaChunk_d(u,t) − 1) = 0

(56) RamRaChunk_d(u,t) · (RamRaChunk_d(u,t) − 1) = 0
```

## RamHammingBooleanity — stage 6b

- [x] (57) DONE: [RAM hamming-weight booleanity](Constraints/RamHammingWeightBooleanity.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/ram/hamming_booleanity.rs#L85).

```text
(57) ∀ t ∈ T:
       RamHammingWeight(t) · (RamHammingWeight(t) − 1) = 0
```

## RamRaVirtualization — stage 6b

- [x] (58) DONE: [RAM address selector from chunks](Constraints/RamRaEqChunkProduct.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/ram/ra_virtualization.rs); [chunk product](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/ram.rs#L163).

```text
(58) ∀ a ∈ M, ∀ t ∈ T:
       RamRa(a,t) = ∏_{d=0}^{D_M−1} RamRaChunk_d(digit_d(a),t)
```

## InstructionRaVirtualization — stage 6b

- [x] (59) DONE: [Virtual instruction selectors from small chunks](Constraints/InstructionRaEqChunkProduct.lean)

[Rust](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/instruction/ra_virtualization.rs); [chunk grouping](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs#L402).

```text
(59) ∀ t ∈ T, ∀ j ∈ {0, …, J−1}, ∀ v ∈ {0, …, 2^(nb)−1}:
       InstructionRa_j(v,t) =
         ∏_{h=0}^{n−1} InstructionRaChunk_{jn+h}(digit_h(v),t)
```

Here `digit_h(v)` splits the `nb`-bit virtual chunk into its `n` small chunks.

## Hamming weights — HammingWeightClaimReduction, stage 7

- [x] (60) DONE: [Instruction chunk hamming weights](Constraints/InstructionRaChunkHammingWeight.lean)
- [x] (61) DONE: [Bytecode chunk hamming weights](Constraints/BytecodeRaChunkHammingWeight.lean)
- [x] (62) DONE: [RAM chunk hamming weights](Constraints/RamRaChunkHammingWeight.lean)

[Rust: prescribed weights](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs#L82); [sumcheck](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-claims/src/protocols/jolt/relations/claim_reductions/hamming_weight.rs#L102).

∀ t ∈ T, and every chunk d in the respective family:

```text
(60) Σ_{u ∈ U} InstructionRaChunk_d(u,t) = 1

(61) Σ_{u ∈ U} BytecodeRaChunk_d(u,t) = 1

(62) Σ_{u ∈ U} RamRaChunk_d(u,t) = RamHammingWeight(t)
```
