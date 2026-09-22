# Jolt constraints

Source: the RV64 constraints in the current [Rust checkout](/Users/ari.biswas/Work-with-A16z/jolt), commit `eae0574a20c2b6481828bcc743a1c8ba683072b2`.

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

[Rust: the 19 equality-conditional rows](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-r1cs/src/constraints/rv64.rs:121).

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

[Rust: the three product rows](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-r1cs/src/constraints/rv64.rs:367); [sumcheck](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/spartan/product_remainder.rs).

∀ t ∈ T:

```text
(20) Product(t) = LeftInstructionInput(t) · RightInstructionInput(t)

(21) ShouldBranch(t) = LookupOutput(t) · Branch(t)

(22) ShouldJump(t) = Jump(t) · (1 − NextIsNoop(t))
```

## RamReadWriteChecking — stage 2

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs:89).

∀ t ∈ T:

```text
(23) RamReadValue(t) = Σ_{a ∈ M} RamRa(a,t) · RamVal(a,t)

(24) RamWriteValue(t) = Σ_{a ∈ M} RamRa(a,t) · (RamVal(a,t) + RamInc(t))
```

## RamRafEvaluation — stage 2

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-verifier/src/stages/stage2/ram_raf_evaluation.rs:133).

`lowest_address` is the memory layout's lowest byte address; remapped word `a` has byte address `lowest_address + 8a`.

```text
(25) ∀ t ∈ T:
       RamAddress(t) = Σ_{a ∈ M} (lowest_address + 8a) · RamRa(a,t)
```

## RamOutputCheck — stage 2

[Rust: constraint](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs:115); [public arrays](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/preprocess/public_io.rs:20).

`IoMask(a) = [io_mask_start ≤ a < io_mask_end]`. `ValIo` contains the public input/output words, the panic word, and termination word 1 when not panicking; other entries are zero, exactly as in `PublicIoMemory::new`.

```text
(26) ∀ a ∈ M:
       IoMask(a) · (RamValFinal(a) − ValIo(a)) = 0
```

## SpartanShift — stage 3

[Rust: constraint](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/spartan/shift.rs:103); [non-wrapping successor](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-poly/src/eq_plus_one.rs:1).

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

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs:102).

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

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:97).

∀ t ∈ T:

```text
(34) RdWriteValue(t) = Σ_{r ∈ R} RdWa(r,t) · (RegistersVal(r,t) + RdInc(t))

(35) Rs1Value(t) = Σ_{r ∈ R} Rs1Ra(r,t) · RegistersVal(r,t)

(36) Rs2Value(t) = Σ_{r ∈ R} Rs2Ra(r,t) · RegistersVal(r,t)
```

## RamValCheck — stage 4

[Rust: constraint](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs:135); [initial public RAM](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/preprocess/ram.rs:134).

`Init(a)` is the initial word array: the program image and public inputs, together with the trusted/untrusted advice words at their memory-layout addresses, zero elsewhere. Advice words are inputs to this array, not additional public constants.

```text
(37) ∀ a ∈ M, ∀ t ∈ T:
       RamVal(a,t) = Init(a) + Σ_{s ∈ T, s < t} RamRa(a,s) · RamInc(s)

(38) ∀ a ∈ M:
       RamValFinal(a) = Init(a) + Σ_{s ∈ T} RamRa(a,s) · RamInc(s)
```

## InstructionReadRaf — stage 5

[Rust: constraint](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/instruction/read_raf.rs:90); [operand coefficients](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs:180).

Let `Q` be the variants of [`LookupTableKind<64>`](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/tables/mod.rs:137). The fixed array `Table_q(x)` is Rust's `q.evaluate_mle(bits(x))` at the 128-bit Boolean encoding of `x`.

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

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs:69).

```text
(42) ∀ r ∈ R, ∀ t ∈ T:
       RegistersVal(r,t) = Σ_{s ∈ T, s < t} RdWa(r,s) · RdInc(s)
```

The empty sum at `t = 0` is zero.

## BytecodeReadRaf — stages 6a–6b

[Rust: row values](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs:533); [PC and entry](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs:358).

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

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/booleanity.rs:25).

∀ t ∈ T, ∀ u ∈ U, and every chunk d in the respective family:

```text
(54) InstructionRaChunk_d(u,t) · (InstructionRaChunk_d(u,t) − 1) = 0

(55) BytecodeRaChunk_d(u,t) · (BytecodeRaChunk_d(u,t) − 1) = 0

(56) RamRaChunk_d(u,t) · (RamRaChunk_d(u,t) − 1) = 0
```

## RamHammingBooleanity — stage 6b

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/ram/hamming_booleanity.rs:85).

```text
(57) ∀ t ∈ T:
       RamHammingWeight(t) · (RamHammingWeight(t) − 1) = 0
```

## RamRaVirtualization — stage 6b

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/ram/ra_virtualization.rs); [chunk product](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/ram.rs:163).

```text
(58) ∀ a ∈ M, ∀ t ∈ T:
       RamRa(a,t) = ∏_{d=0}^{D_M−1} RamRaChunk_d(digit_d(a),t)
```

## InstructionRaVirtualization — stage 6b

[Rust](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/instruction/ra_virtualization.rs); [chunk grouping](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs:402).

```text
(59) ∀ t ∈ T, ∀ j ∈ {0, …, J−1}, ∀ v ∈ {0, …, 2^(nb)−1}:
       InstructionRa_j(v,t) =
         ∏_{h=0}^{n−1} InstructionRaChunk_{jn+h}(digit_h(v),t)
```

Here `digit_h(v)` splits the `nb`-bit virtual chunk into its `n` small chunks.

## Hamming weights — HammingWeightClaimReduction, stage 7

[Rust: prescribed weights](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs:82); [sumcheck](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-claims/src/protocols/jolt/relations/claim_reductions/hamming_weight.rs:102).

∀ t ∈ T, and every chunk d in the respective family:

```text
(60) Σ_{u ∈ U} InstructionRaChunk_d(u,t) = 1

(61) Σ_{u ∈ U} BytecodeRaChunk_d(u,t) = 1

(62) Σ_{u ∈ U} RamRaChunk_d(u,t) = RamHammingWeight(t)
```
