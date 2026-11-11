# Jolt's inline precompiles in jolt-qed

This note specifies how jolt-qed brings Jolt's inline precompiles into its theorems.
It fixes the scope, the design, the statements to prove, the order of work and the boundary of the results.
Later work implements it; when that work finds a decision here to be wrong, this note changes first.

Today no jolt-qed theorem says anything about a guest that calls an inline.
`SourceInstruction` has no constructor for the inline opcodes, and an image that contains one cannot be written down.
Issue #37 keeps inlines out of scope "for now".
Guests that prove an Ethereum block or check a signature call inlines thousands of times, and those guests fall outside `JoltInstance.soundness`, `sail_soundness` and `sail_reproduces`.

## Sources

- Jolt, a16z/jolt `main` at `70e00da09` (2026-11-11), for the inline mechanism, the builders and the fixtures.
  The inline crates (`jolt-inlines/`) are unchanged from `70e00da09` to `a6b6dc717`, which section 12 cites for the SDK code.
- jolt-qed at `09aaeab`, the head of #42 (stacked on #39), for every jolt-qed file and line cited below.
- EthLib, ethereum/EthLib at `5310b3e` (2026-11-11), CC0-1.0, for the hash and field specifications (section 5.6).
- A survey of Lean sources for the four families and of machine-checked zkVM precompiles, made on 2026-11-11.
  Its claims about other projects are as of that date.

## 1. Scope

### 1.1 What is in scope

The plan proves twelve inlines in four families:

| Family | Inlines |
|---|---|
| SHA-256 | `SHA256`, `SHA256_INIT` |
| Keccak-256 | `KECCAK256`, `KECCAK256_ABSORB_PERMUTE` |
| BLAKE2b | `BLAKE2` |
| secp256k1 | `SECP256K1_MULQ`, `SECP256K1_SQUAREQ`, `SECP256K1_DIVQ`, `SECP256K1_MULR`, `SECP256K1_SQUARER`, `SECP256K1_DIVR`, `SECP256K1_GLVR_ADV` |

Every item below is in scope or out of scope.
The plan has no optional tier.

| Item | Scope | Where |
|---|---|---|
| Each inline's rows, generated from Jolt's Rust and checked against Jolt's fixture | in | 5.1 |
| Frame and footprint of every call, for every input and every advice | in | 5.4 |
| Soundness of the rows: every advice that passes the asserts gives the specified result; for `GLVR_ADV` the result is six words stored in the output buffer | in | 5.4 |
| Completeness of the rows: Jolt's own advice functions, transcribed to Lean, pass every assert; for `GLVR_ADV` this includes the bound `k1, k2 < 2^128` and the recombination identity the SDK checks | in | 5.4 |
| `JoltInstance.soundness` and `JoltInstance.completeness` for images that call the twelve | in | 6, R1 and R4 |
| `sail_soundness` and `sail_reproduces` for guests that call the twelve | in | 6, R5 |
| The generic machinery: inline keys, the row generator, the program logic, the `inline_advice` private input, the platform step | in | 5 |
| The other fifteen registered inlines: BLAKE3 and its keyed variant, BIGINT256_MUL, the P-256 and Grumpkin inlines, P256_FAKE_GLV_ADV, the two NTT inlines | out | Each later needs its key, specification and lemmas; the driver already generates and checks their rows |
| Field-inline (`0x7B`) | out | It changes the constraint system; revisit after the generated constraints of T3 and #41 land |
| User inlines on `0x2B` | out | None exist |
| Guest code that calls the inlines: the SDK's field wrappers and their `c < q` checks, `decompose_scalar_impl`, `ecdsa_verify`, the digest functions, and the curve fact `λ·Q = φ(Q)` | out | Section 12: a later track |
| The Rust extractor itself, the Sail compiler, Lean's kernel | out | Trusted, as today |
| Jolt's verifier below the constraint relation: sumcheck and commitments | out | As for today's theorems |

The machinery stays generic.
The source language takes the set of supported inlines as a parameter, the driver generates and checks the rows of all 27 registered inlines, and the shared proof libraries are parametric in the modulus, the limb count and the number of advice words.
Adding an inline later means adding its key, its specification and its per-inline lemmas.

### 1.2 What the results will not say

The results say that Jolt runs each inline correctly.
They do not say that the guest code around the inlines computes what its name says.

After this plan, an accepted proof for an image that calls `ecdsa_verify` means that some private inputs give a Sail run of the image in which every inline call keeps its frame and meets its specification under its preconditions, no spoil assert fires, and the outputs match.
It does not mean that the image verifies ECDSA signatures, or that an image that calls `Sha256::digest` computes SHA-256.
If `ecdsa_verify` had a bug that accepted a forged signature, Jolt would correctly prove that the buggy image accepted it, and every theorem in this plan would still hold.

Any public statement of the results (the README, a paper, a blog post) states this boundary next to the theorem.
Section 12 describes the gap, what can go wrong in it, and how a later track would close it.

### 1.3 Terminology

jolt-qed uses "inline" for three things: any virtual sequence (constraint `NextPCEqPCPlusOneIfInline` covers division and atomics too), the scratch register pools `inlineTmp` and `largeInlineTmp`, and the precompile opcodes.
This note uses "inline" only for the registered precompiles on `0x0B` and `0x2B`.

## 2. How Jolt runs an inline

### 2.1 Three instruction classes

| Class | Opcode | Count | Mechanism | Constraint impact |
|---|---|---|---|---|
| Registered inline precompiles | `0x0B` (`0x2B` reserved, unused) | 27 in 9 crates | R-type `.insn r 0x0B, funct3, funct7, rd, rs1, rs2`; decoded as `SourceInstructionKind::Inline` with key `(opcode, funct3, funct7)`; registered at link time (`register_inlines!`, `inventory`); expanded by `InlineExpansionBuilder` into a straight-line sequence of ordinary rows | None: no new R1CS rows, claims or inline-only tables; the rows use general tables (`VirtualXORROT*`, `VirtualXORROTW*`, `VirtualXORROTL1`, `VirtualRev8W`, `Andn`, `VirtualROTR*`) |
| Field-inline | `0x7B` (feature `field-inline`) | 10 operations | One final row per instruction; a 16-slot field register file with its own Twist instance, product lanes, claims in stages 2, 4, 5 and 6 | New circuit flags, R1CS rows and sumcheck claims |
| Jolt custom instructions | `0x5B` | 7 | Advice loads, `VirtualRev8W`, `VirtualAssertEQ`, `VirtualHostIO` | Ordinary rows; already in jolt-qed's source language |

A registered inline is not a separate circuit.
Jolt's expander replaces it with ordinary rows, and the ordinary constraints check those rows.
jolt-qed already models every row kind these sequences use and the constraints that make a sequence atomic.

### 2.2 How an inline expands

1. The decoder maps opcodes `0x0B` and `0x2B` to `Inline` and stores `rd` in the `rs3` slot.
   It accepts any `funct3` and `funct7` without consulting the registry (`decode.rs:85`).
   An unregistered key fails later, when the tracer or preprocessing looks it up (`tracer/src/instruction/inline.rs:113-121`).
2. If `rd = x0`, the expander allocates an instruction temporary from `vr40..47` and substitutes it for `rd` (`expand/mod.rs:134-169`).
   It does not initialise the temporary.
   The inline provider reads that register as `rs3` (`expand/inline.rs:40-42`), and the builders that write an output buffer use `rs3` as its pointer.
3. The registered builder emits rows.
   Inline temporaries come from the pool `vr48..127`.
4. `materialize_inline` expands source-only helpers (`LW`, `SLLI`, ...), checks that load and store offsets fit in 12 bits, and appends one `ADDI vr, x0, 0` reset row for each pool register the builder allocated.
   Helpers allocate their own instruction temporaries from `vr40..47` (an `LW` helper takes two, `expand/memory/shared.rs:173-186`); releasing them does not restore their values.
   Registered inlines may have up to `u16::MAX` final rows; built-in sequences at most 64 (`materialize.rs:20-21`).
5. Metadata stamping marks the first row, counts `virtual_sequence_remaining` down to 0, and sets the compressed flag on the last row only.

Whole-program preprocessing passes one allocator through every source instruction (`expand/mod.rs:291-306`).
The fixture generator uses a fresh allocator per instruction (`jolt-inlines/fixtures/src/lib.rs:139-146`).
Reserving the `rd = x0` temporary shifts later helper allocations; the known case is NTT, whose `LW` helpers take `vr41` and `vr42` instead of `vr40` and `vr41`.

### 2.3 What carries soundness

| Property | Where Jolt enforces it | Consequence for jolt-qed |
|---|---|---|
| Atomicity: a trace enters a sequence only at its first row and leaves only after its last | R1CS rows 16, 17 (`NextPCEqPCPlusOneIfInline`, which covers every virtual sequence) and 18, plus bytecode preprocessing | Already modelled and proved (constraint 18, `Layer6/BytecodePC.lean`, `Layer7/LastJump.lean`) |
| Pool registers `vr48..127` are zero when an inline starts | Zero initial registers; each inline resets the pool registers it allocated; no other source expansion writes the pool | Only BLAKE3_KEYED64, which is out of scope, relies on it (`blake3/src/sequence_builder.rs:81-93`); see section 5.4 |
| An inline writes no architectural register (`x1..x31`) and no persistent virtual register (`vr32..39`) | Nothing: `InvalidInlineWriteTarget` is never constructed | Today's builders comply; Lean proves a frame lemma per inline; inlines may write instruction temporaries `vr40..47` through helpers, and the rule must allow those (request J1) |
| Advice values | `VirtualAdvice` rows: any 64-bit word (RangeCheck table) | Every further property comes from later rows or from guest code |

## 3. The twelve inlines

| Family | Inline (final rows) | Advice | What the rows guarantee |
|---|---|---|---|
| SHA-256 | `SHA256` (1,900): one compression with a given state; `SHA256_INIT` (1,864): one compression from the standard IV | None | The new state is a function of the old state and the 64-byte block, for every input. The rows read 8 words of state and a big-endian block and write the state in place through `rs1` |
| Keccak-256 | `KECCAK256` (3,087): Keccak-f[1600] in place; `KECCAK256_ABSORB_PERMUTE` (3,121): XOR a 136-byte rate block into the state, then Keccak-f | None | The new 200-byte state is a function of the old state (and the block), for every input |
| BLAKE2b | `BLAKE2` (1,067): one compression F | None | The new `h` is a function of `h`, the 128-byte block, the counter `t` and `is_final`; the mathematical meaning needs `is_final ∈ {0, 1}` |
| secp256k1 field | `MULQ`, `SQUAREQ`, `DIVQ` (186, 167, 194); `MULR`, `SQUARER`, `DIVR` (232, 213, 240) | MUL and SQUARE: 4 words (`w`); DIV: 8 words (`c`, `w`) | See below |
| secp256k1 GLV | `GLVR_ADV` (13) | 6 words | Nothing: the rows store six prover-chosen words |

For the field operations, `q` stands for the base-field prime `p` or the group order `n`, and `p' = 2^256 − q`.

- MUL and SQUARE: the prover chooses the quotient limbs `w` (four unsigned words).
  The rows compute `a·b + w·p'`, assert that its high four limbs equal `w`, and store the low four limbs as `c`.
  Hence `a·b = w·q + c` over the integers, with final bound checks on `w`, and therefore `c ≡ a·b (mod q)` and `c < 2^256`.
  The rows do not give `c < q`.
  A second representative `c + q` passes when `a·b ≥ q` (which makes `w − 1 ≥ 0`), `c + q < 2^256`, and the final checks accept `w − 1`.
  For the base field `2^256 − p = 2^32 + 977`, and the second representative needs `c < 2^32 + 977`; for the scalar field `2^256 − n` is about `1.3·2^128`.
- DIV: the prover also chooses `c`, and the rows enforce `c·b = w·q + a`.
  If `b ≡ 0 (mod q)` and `a ≡ 0`, every `c` passes; Jolt's advice function panics there, and the SDK spoils the proof on a zero divisor (`secp256k1/src/sdk.rs:280-284`), outside the inline.
  All DIV result stores come after all checks.
  An earlier version stored before checking, and under `rd = rs1` that made the check vacuous (v12 audit finding #115878, fixed in `db9679295`).
- `GLVR_ADV`: the rows store six words and check none of them.
  The guest checks the sign words and `k1 + λ·k2 = k` afterwards (`secp256k1/src/sdk.rs:751`).

The SDK calls the five hash inlines with `rd = x0`, and they update a buffer in place through `rs1`; they never read `rs3`.
The seven secp256k1 inlines use `rs3` as the output pointer, and the SDK always passes a real `rd`.

## 4. What jolt-qed has today

- `SourceInstruction` is `.riscv` or `.jolt` (the seven `0x5B` instructions).
  `JoltInstance.soundness` covers both.
  The whole-run theorems exclude `.jolt` rows through the scope premise `BlockConforms.riscv`.
- `joltDecode` returns `none` for `0x0B`, `0x2B`, `0x5B` and `0x7B`.
  `ImageDecoded` constrains only `.riscv` rows; #43 derives it from a transcription of Jolt's `decode_elf`.
- The inline rows use only existing `Instr` constructors (91 at `09aaeab`), including `ANDN`, `VirtualAdvice`, `VirtualAssertEQ`, `VirtualAssertLTE`, `VirtualROTRI` and `VirtualXORROT*`.
  The work can reuse `Layer5/XorRotation.lean`, the `largeInlineTmp` register pool, constraint 18, and the DIV/REM proof pattern: generated rows, a phase split proved by `rfl`, run lemmas, `*_math` files, and a two-direction theorem.
- Four parts of the model need revisiting:
  - `Layer4/Reachable.lean` proves the plain rotate tables `VirtualROTR` and `VirtualROTRW` unreachable "because inlines are outside the type"; SHA-256 and Keccak's ρ step use them.
  - `Layer7/TapeRebuild.lean` assumes that no inline reads the advice tape, which is true for all 27.
  - `CodeInv.storeBase` returns `none` for non-RISC-V rows.
  - `SourceInstruction.honestTracerAdvice` (`honest_trace.lean:158`) covers only DIV and REM.
- `expand_instruction` rejects every `.sequence` longer than `MAX_FINAL_ROWS_PER_SOURCE = 64` (`program.lean:177-198`), and `program_facts.lean:70-79` uses that bound.
  Every in-scope inline except `GLVR_ADV` exceeds it.
- The soundness language (`language.lean:13-26`) requires an `HonestTrace`, which runs every instruction with the tracer's runtime advice (`honest_trace.lean:214-215`, `Layer5/TapeTrace.lean:73-74`).
  A witness may use other advice only where the end state is the same (DIV and REM by zero), and the proof tolerates a different value in temporary `vr40` after REM by zero (`Layer6/ExecutionPrefix.lean:15-44`).
  Tape reconstruction collects only `VirtualAdviceLoad` answers (`Layer7/TapeRebuild.lean:70-88`).
  This fits the hash inlines, which take no advice.
  It does not fit the secp256k1 inlines, whose stored outputs depend on the advice (section 5.3).

## 5. Design

### 5.1 Rows as Rust-emitted data, never transcribed

```
Jolt @ pin ──► driver (Rust, scripts/expansion-parity)
                 ├─ production entry point: whole-image expansion with one shared allocator
                 ├─ checks: fixture hash = registered_inline_expand_parity_hashes.jsonl
                 ├─ checks: rows are uniform in (rs1, rs2, rs3) over x0..x31, per allocation case
                 ├─ checks: every pool register is written before it is read (in-scope inlines)
                 └─ JSON ──► gen ──► JoltBytecode/Inlines/Generated/<Name>.lean
                                          │  rendered back and compared with Rust's rows
                                          │  rfl
                 JoltBytecode/Inlines/<Name>/Builder.lean (structured, rounds)
                                          │  proofs
                 JoltBytecode/Inlines/<Name>/Spec.lean (copied or adapted specification)
```

- The driver links the inline crates at the pin and runs the production expansion entry point that bytecode preprocessing uses: `TracerInlineExpansionProvider` under `RV64IMAC_JOLT_ALL_INLINES`, the shared allocator, `materialize_inline`, and stamping.
  It prints fully materialised final rows, with addresses, sequence metadata, compressed flags, the effective circuit flags and table of each row, and the PC map that preprocessing builds.
  It does this for all 27 registered inlines.
- Allocation differs between cases.
  The `rd = x0` rewrite reserves an instruction temporary and shifts later helper allocations (section 2.2).
  The driver emits one row family per allocation case, not one sentinel family with operands substituted afterwards.
  It also checks that the shared allocator is back in its initial state after every successfully expanded source instruction, which makes the per-instruction rows independent of the instructions before them.
- The driver recomputes each inline's golden hash for the four fixture scenarios (normal, compressed, `rd = x0`, aliased) and fails if any differs from the fixture that Jolt's CI checks.
  A change to an inline's rows then shows up as a fixture change in Jolt and a regeneration diff in jolt-qed.
  The fixture uses a fresh allocator; the hash check shows only that the driver and the fixture agree on that path, and the allocator-restoration check connects it to the shared-allocator path.
- The driver checks operand uniformity exhaustively: for every triple of architectural registers `x0..x31`, within each allocation case, the rows equal the parametric rows with the operands substituted.
  This rules out a builder that branches on register identity, which today's sampling generator cannot detect.
  If a builder does branch, the driver reports it, and the generated Lean takes the branch condition as a parameter.
- The driver checks, for each in-scope inline, that every pool register the rows read was written earlier in the same sequence.
- The generator writes `<name>RowsAuto (rs1 rs2 rs3 : Reg) : JoltISA.Program` per allocation case.
  A test executable renders the generated Lean definitions back to concrete rows, and the driver compares them with Rust's concrete rows, field by field.
  The extractor (driver plus generator) remains trusted; the round trip narrows what it can get wrong.
- A hand-written structured builder (`rounds`, `sigma`, `mulAcc` helpers that mirror the Rust builder) is proved equal to the generated definition by `rfl`, chunked per round if elaboration needs it.
  The proofs use the structured builder.
  It is not trusted, because `rfl` ties it to the generated rows.
- The fixture stores hashes of rows, not flags or tables.
  The metadata comparison of T1 covers flags and tables for every row kind, which also catches a semantic change such as `4e55c9a5f` (range-checked RAM loads) that left the fixture unchanged.

### 5.2 Source language, expansion and decoding

- Add `SourceInstruction.inline (key : InlineKey) (rs1 rs2 rs3 : Reg)`.
  `InlineKey` enumerates the supported keys and is generated with the rows: the five hash keys in I1a, the seven secp256k1 keys in I1b.
  Every `match` on `SourceInstruction` gains a case.
  Supporting another inline later adds a key and its generated rows; nothing in the language changes.
- `SourceInstruction.expand (.inline k rs1 rs2 rs3)` reproduces Rust's `rd = x0` rewrite with the allocator state that preprocessing has at that point, and returns the generated rows for the matching allocation case.
- `expand_instruction` gets a capacity that depends on the class: 64 final rows for built-in sequences, as today, and `u16::MAX` for registered inlines, as in Rust.
  The proofs in `program_facts.lean` that use the 64-row bound are generalised.
- Decoding has two steps, as in Rust.
  The raw decoder maps `0x0B` and `0x2B` with any `funct3` and `funct7` to an inline encoding, and `0x5B` through a transcription of `decode_custom`.
  A separate registration check maps a supported key to `.inline` and rejects the rest.
  T2 compares the raw decoders.
  I3's decoding premise uses the combined pipeline (raw decoding plus registration), compared with Rust's combined pipeline (decoding plus the registry lookup in the tracer and in preprocessing).
- The registration check rejects `rd = x0` encodings of every key whose rows read `rs3`, which are the seven secp256k1 inlines.
  Rust substitutes an uninitialised instruction temporary for `rd`.
  The hash inlines never read `rs3`, and for them the temporary is unused.
  A secp256k1 inline encoded with `rd = x0` takes its output pointer from whatever an earlier sequence left in the temporary.
  The current soundness proof lets that temporary differ between the witness and the honest run after REM by zero (`Layer6/ExecutionPrefix.lean:15-44`).
  A witness can leave a valid RAM pointer in `vr40` where the honest run has zero, and a following `rd = x0` inline then stores to different places in the two runs.
  The SDK never emits such an encoding, and the exclusion follows the precedent of `SC.W` and `SC.D`, excluded with Ari's approval on 2026-10-10.
  Request J6 asks Jolt to reject these encodings too (decision D7).

### 5.3 Inline advice is a private input, like the advice tape

#### Two kinds of prover choice today

Today's theorem handles prover choice in two ways (`methods/soundness.md`).

1. Visible choice goes into the private inputs.
   An `AdviceL*` instruction reads the advice tape, and the guest sees the value.
   No constraint ties the witness's answers to one tape, and the theorem's existential picks the tape: Layer 7 rebuilds one tape from the witness's answers, and the honest run reads that tape.
2. Internal choice must be invisible.
   A DIV or REM expansion takes the quotient and remainder as advice, and the honest run uses the tracer's values.
   The witness may choose other advice, but the asserts force the same architectural result (the `*Program_sound` theorems).
   The only leftover difference is the quotient after a division by zero, which lands in a temporary in `vr40..47` that is dead at the next source boundary.

The current Lean:

```lean
-- language.lean
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
    trace.matches_outputs joltInstance ∧
    (trace.prover_config joltInstance).isSome ∧
    trace.SpoilAssertsPass

-- program.lean
structure JoltPrivateInputs where
  untrusted_advice : Array (BitVec 8)
  advice_tape : Array (BitVec 8)

-- honest_trace.lean
def honestTracerAdviceAtStepN (program : Rv64ProgramImage SourceInstruction)
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode)) (n : Nat) :
    Option (BitVec 64) := do
  let row ← rows[n]?
  let bytecodeValue ← bytecode[row.rowIndex].instruction.adviceValue?
  let first ← rows[startOfExpansionContainingStepN rows n]?
  let instruction ← program.instructionAt bytecode[first.rowIndex].address
  let values := instruction.honestTracerAdvice first.preState
  pure (values[adviceStepsBeforeStepN rows n]?.getD bytecodeValue)
```

Jolt's bytecode carries no advice value (`VirtualAdvice(())`), and the placeholder `bytecodeValue` is whatever the Lean expansion put in the row.
Without a formula case in `honestTracerAdvice`, an honest trace takes that placeholder.

#### Why the secp256k1 inlines fit neither kind

The five hash inlines take no advice, and neither mechanism is needed.
The secp256k1 inlines fit neither:

- The field operations' quotient words `w` stay in pool registers, which the reset rows zero, and they are invisible like DIV's quotient.
  The result `c` is stored to memory, and the asserts do not determine it (section 3).
- `GLVR_ADV` stores six words that no row checks.

Take `SECP256K1_MULQ` with `a = 2` and `b = (q + 1)/2`, the inverse of 2 modulo `q`.
Then `a·b = q + 1`, and two advice words pass the rows:

| | Jolt's advice | Another passing advice |
|---|---|---|
| Quotient `w` | `1` | `0` |
| `a·b + w·p'` | `2^256 + 1` | `q + 1` |
| High four limbs | `1 = w`: pass | `0 = w`: pass |
| Stored `c` | `1` | `q + 1` |
| `c < q` | yes | no |

Suppose the model added `SECP256K1_MULQ` to `honestTracerAdvice` with Jolt's formula, as it does for division.
A guest that reads `a` and `b` from its public input, calls the inline, and writes `c` to its public output without checking `c < q` would be a counterexample to the theorem.
The witness with `w = 0` satisfies every constraint and outputs `q + 1`, and every honest run records `w = 1` and outputs `1`.
The SDK's field wrapper checks `c < q` and spoils the proof otherwise, but the theorem covers every image, including one that calls the inline directly.
For `GLVR_ADV`, any guest that outputs the split is a counterexample.
Even when the final output agrees, as for an SDK ECDSA check that accepts several valid splits, the proof cannot keep the witness and the honest run in step, because their memories differ.

#### The design

Inline advice words become a private input, the way the advice tape already is.

```lean
structure JoltPrivateInputs where
  untrusted_advice : Array (BitVec 8)
  advice_tape : Array (BitVec 8)
  -- NEW. The words the VirtualAdvice rows of inline sequences write, in the order
  -- the trace runs them. Jolt's prover fills it with each inline's `build_advice`.
  inline_advice : Array (BitVec 64)

-- NEW. Whether step `n` runs a VirtualAdvice row of an inline's sequence.
def stepNOfTraceIsInlineAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat) : Bool :=
  stepNOfTraceIsAdvice rows n &&
    match rows[startOfExpansionContainingStepN rows n]?.bind
        (fun first => program.instructionAt bytecode[first.rowIndex].address) with
    | some (.inline ..) => true
    | _ => false

-- NEW. How many inline advice steps the trace runs before step `n`, over all calls.
def inlineAdviceStepsBeforeStepN (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat) : Nat :=
  ((List.range n).filter (stepNOfTraceIsInlineAdvice program rows)).length

def honestTracerAdviceAtStepN (program : Rv64ProgramImage SourceInstruction)
    (privateInputs : JoltPrivateInputs)                            -- NEW argument
    {bytecode : Array JoltInstructionRow} (rows : Array (TraceRow bytecode)) (n : Nat) :
    Option (BitVec 64) := do
  let row ← rows[n]?
  let bytecodeValue ← bytecode[row.rowIndex].instruction.adviceValue?
  let first ← rows[startOfExpansionContainingStepN rows n]?
  let instruction ← program.instructionAt bytecode[first.rowIndex].address
  match instruction with
  | .inline .. =>                                                  -- NEW case
    pure (privateInputs.inline_advice[inlineAdviceStepsBeforeStepN program rows n]?.getD 0)
  | _ =>                                                           -- unchanged
    let values := instruction.honestTracerAdvice first.preState
    pure (values[adviceStepsBeforeStepN rows n]?.getD bytecodeValue)
```

`HonestTrace.advice_from_honest_tracer` passes `privateInputs` to `honestTracerAdviceAtStepN`.
The text of `InLanguage` and `JoltInstance.soundness` does not change.
Every other step keeps today's rule, and programs without inline advice rows are unaffected.

The proof adds three facts.
Their exact homes in Layers 5 to 7 are decided in I1b.

```lean
-- The witness's inline advice words, in trace order.
def collectInlineAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) : Array (BitVec 64) :=
  ((List.range rows.size).filterMap fun n =>
    if stepNOfTraceIsInlineAdvice program rows n then rows[n]?.bind (·.someTracerAdvice?)
    else none).toArray

-- The constraints do not read `inline_advice`.
theorem allConstraints_inline_advice (words : Array (BitVec 64)) :
    AllConstraints joltInstance { privateInputs with inline_advice := words } witness ↔
      AllConstraints joltInstance privateInputs witness

-- With the collected words in the field, every inline advice step is honest.
theorem collectInlineAdvice_honest (rows : Array (TraceRow bytecode)) (n : Fin rows.size)
    (inline : stepNOfTraceIsInlineAdvice program rows n) :
    rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN program
        { privateInputs with inline_advice := collectInlineAdvice program rows } rows n
```

After Layer 6 reconstructs the trace, the proof sets the field to the witness's inline advice words in trace order, and every inline advice step is then honest.
Layer 7's `rebuiltInputs` replaces only `advice_tape` and copies the field unchanged.
`sail_reproduces` and `JoltInstance.completeness` need the other direction: Jolt's prover fills the field with its `build_advice` words, and these pass every assert (section 5.4).

The step relation of an inline call is `InlineSpec k`, a relation between states, not a function.
For the hash inlines it is the graph of a function.
For the field operations it is the integer relation of section 3 with a bounded quotient witness.
For `GLVR_ADV` it allows any six words at the output buffer.

The change touches the contracts of Layers 5a, 6 and 7, which already treat the tape this way; I1b lists and adapts each.
DIV and REM keep their present treatment.
A later cleanup can move them to the private input and retire part of the 3,400-line honest-advice reconstruction in `Layer6/Division*.lean`.

This design changes `JoltPrivateInputs` and `honestTracerAdviceAtStepN`, which define the language.
`AGENTS.md` requires Ari's approval for that, and I1b waits for it (decision D2).

### 5.4 Per-inline theorems

Each inline `k` has a precondition `Pre k s` that collects the caller's obligations: alignment, buffers inside RAM, overlap rules, and value ranges (`is_final ∈ {0, 1}` for `BLAKE2`, inputs below the modulus for secp256k1, a nonzero divisor for DIV).
Row execution covers only the rows; the block layer advances the source PC (`Semantics.lean:589-597`, `WholeRun/Basic.lean:81-84`).

Statement shapes, generic in `k`:

```lean
-- What a call may do when its preconditions hold.
def InlineSpec (k : InlineKey) (rs1 rs2 rs3 : Reg) : SailJoltState → SailJoltState → Prop

-- Frame and footprint: every input, every advice choice.
theorem rows_frame (k)
    (run : RunsToEnd (rowsAuto k rs1 rs2 rs3) advice s s') :
    Frame k rs1 rs2 rs3 s s'

-- Soundness: every advice choice that gets through all the asserts.
theorem rows_sound (k) (pre : Pre k s)
    (run : RunsToEnd (rowsAuto k rs1 rs2 rs3) advice s s') :
    InlineSpec k rs1 rs2 rs3 s s'

-- Jolt's `build_advice` for key k, transcribed; the empty list for the hashes.
def joltAdvice (k : InlineKey) (s : SailJoltState) : List (BitVec 64)

-- Completeness: Jolt's own advice passes.
theorem rows_jolt_advice_complete (k) (pre : Pre k s) :
    ∃ s', RunsToEnd (rowsAuto k rs1 rs2 rs3) (joltAdvice k s) s s' ∧
      InlineSpec k rs1 rs2 rs3 s s'

-- The GLV facts behind the GLVR_ADV case.
theorem glvDecompose_small (k : ZMod n) :
    (glvDecompose k).k1 < 2 ^ 128 ∧ (glvDecompose k).k2 < 2 ^ 128
theorem glvDecompose_recombines (k : ZMod n) :
    (glvDecompose k).signedK1 + (glvDecompose k).signedK2 * glvLambda = k
```

- **Frame and footprint**, for every input: the rows leave `x1..x31`, `vr32..39`, the advice tape, the device configuration and the other state that composition reads unchanged.
  Memory changes only inside the output buffer, computed from the rewritten operand with wrapping addresses.
  The allocated pool registers are zero again, and untouched pool registers keep their values.
  The instruction temporaries `vr40..47` may change.
  This lemma does not need `Pre k`, and the whole-run layer can use it for every call.
- **Soundness** (`rows_sound`): for every advice sequence, if the rows run to the end from `s` with `Pre k s`, the end state satisfies `InlineSpec k`.
  For the field operations `InlineSpec` is operation-specific: `a·b = w·q + c` for MUL and SQUARE, and `c·b = w·q + a` for DIV, each with the bounded quotient witness `w` the rows check.
- **Completeness with Jolt's advice** (`rows_jolt_advice_complete`): for every `s` with `Pre k s`, the rows run to the end with `joltAdvice k s`, every assert passes, and the end state satisfies `InlineSpec k` with the canonical output.
  The transcriptions are `mulq_quotient_advice` (`w = ⌊a·b / m⌋`), `mulq_division_advice` (result and quotient interleaved; it panics when `b = 0`, which `Pre k` excludes), both in `jolt-inlines/sdk/src/host.rs`, and `glv::decompose_scalar`.
  For `GLVR_ADV` the lemma proves that both sign words are 0 or 1, that `k1, k2 < 2^128` (Jolt's `to_sign_abs` truncates to 128 bits), and that `k ≡ ±k1 ± λ·k2 (mod n)`, the identity the SDK checks.
  I0 tests each transcription against Rust; I2 proves the lemmas.
  `JoltInstance.completeness` (`Completeness/completeness.lean`) then extends to inline rows in I1a and I1b.
- **Determinism** for the hash inlines follows from the functional specification.
  For the field operations a corollary states which representatives can pass (`c`, and `c + q` only under the conditions of section 3) and that a `c < q` check makes the result unique.
  For DIV the corollary assumes `b ≢ 0 (mod q)`.
- **Conditional and unconditional parts.**
  The frame and footprint hold for every call.
  The mathematical specification holds only under `Pre k`.
  R4 and R5 state both parts, and the per-call precondition appears as an explicit premise or as an invariant the guest establishes.
- **Pool registers.**
  If the write-before-read check of section 5.1 passes for the twelve, their lemmas hold from any pool state.
  If it fails for an inline, that inline's lemmas take a premise `PoolZero s` (pool registers are zero at the start of a call), and I1 proves it as an invariant from five facts: registers start at zero (`program.lean:109-110`, with initial agreement from `Layer5/Registers.lean:72-80`); no non-inline source expansion writes the pool; each inline resets every pool register it allocates; each inline leaves the pool registers it does not allocate unchanged; and atomicity puts every reset before the next source boundary.

The specifications are the trusted part.
Each is copied or adapted from an existing Lean source (section 5.6) or is a one-line statement in Mathlib terms (`c ≡ a * b [ZMOD q]`).
Each comes with known-answer tests in a separate test module outside the headline import closure.
Each `rows_sound` is instantiated on a concrete known-answer input, to show that its hypotheses are satisfiable.

### 5.5 Proof engineering for long sequences

- Proofs work on the structured builder, one lemma per round or helper (a SHA-256 round, Keccak θ, ρπ, χ and ι, the BLAKE2b G function, a multiply-accumulate step), composed by a small straight-line program logic over `JoltISA` states: a weakest-precondition calculator for rows that write registers and memory, with simp lemmas for register-file updates.
  jolt-qed's `ProofSupport` and the DIV phase lemmas are the starting point; `riscv-zkvm`'s `Rv64.Logic` and LNSym's SHA-512 proof show the shape.
- Hash specifications follow a two-layer pattern: a reference specification that reads like the standard, a fast specification shaped like the inline's rounds, and a proof that the two agree.
- Bit-vector reasoning uses `BitVec` lemmas and `omega`.
  `bv_decide` may be used during exploration to find counterexamples, never in a committed proof in the headline import closure.
- The checking standard is strict: only `propext`, `Classical.choice` and `Quot.sound`; no `bv_decide`, `decide +kernel`, `native_decide`, or heartbeat and recursion-depth overrides in the headline import closure.
- A proof that gets stuck is a candidate bug (Scroll's `is_final` under-constraint was found this way).
  Record it before weakening a statement.

### 5.6 Specifications

EthLib covers all four families, each with a `BitVec` model written in the standard's notation, a proof that its fast code equals the model, and known-answer tests run through its Python bindings.

| Family | Primary specification | What it proves | Cross-check |
|---|---|---|---|
| SHA-256 compression and IV | EthLib `Sha256.Spec.compression (input : Vector (BitVec 32) 16) (initial : State) : State` and `Spec.initial` (`Proofs/Hash/Sha256.lean`) | `compress_toState`: the `UInt32` code equals the model; `IV_from_primes`, `K_from_primes` derive the constants from the primes | NIST CAVP vectors in EthLib; `riscv-zkvm` `ZiskAccel.sha256Compress` (MIT); VCVio `Algorithms/Sha2.lean` (Apache-2.0) |
| Keccak-f[1600], absorb-then-permute | EthLib `Keccak.keccakF` over 25 `UInt64` lanes and `absorbBlock`, specified by the bit-level model `Proofs/Models/KeccakBits.lean` | `toLanes_permutation`: the lane code equals the bit model; `keccak256_eq`; one lemma per step; `keccakF_bijective` | Keccak team KATs in EthLib; `ZiskAccel.keccakF`; VCVio `Algorithms/Keccak.lean` |
| BLAKE2b compression F | EthLib `Blake2b.compress 12 h m t0 t1 f` and `Spec.compress` with a 128-bit counter (`Proofs/Hash/Blake2b.lean`) | `compress_toBitVec` for every round count; `IV_sqrt`, `SIGMA_perm` | Ironwood `Zcash/Common/Hash/Blake2b.lean` `compressWords` (Apache-2.0 or MIT); EIP-152 vectors in EthLib |
| secp256k1 fields | EthLib `Fp`, `Fn` with `toZMod : Fp ≃+* ZMod p` and Pratt primality certificates; or CompPoly `Secp256k1.BaseField` and `ScalarField` (`ZMod`, Apache-2.0) | Primality of `p` and `n`; ring isomorphisms to `ZMod` | Wycheproof vectors in EthLib |
| secp256k1 GLV split (completeness of `GLVR_ADV`) | The constants of `glv.rs` (`λ`, the basis `(a1, b1)`, `(a2, b2)`, the rounding constants) over `Fn`; no Lean source has the secp256k1 GLV split | Primality of `n`; the curve itself is not needed | EthLib's BLS12-381 GLV split (`Proofs/Kzg/SetupLagrange/Glv.lean`) as a template; Jolt's GLV tests |

- The per-inline specifications need only the first four rows.
  `GLVR_ADV`'s rows check nothing, and its specification is "six words at the output buffer"; the GLV mathematics enters its completeness lemma.
- jolt-qed copies the specification definitions (the `Spec` sections, the Keccak bit model, the field definitions) rather than importing EthLib.
  CC0 allows this.
  Copying avoids EthLib's dependency on VCVio and keeps EthLib's `decide +kernel` constant proofs out of the headline import closure (the SHA-256 and BLAKE2b proof files use it twice each).
  Each copied file records the EthLib commit, and a CI job diffs the copies against EthLib.
- jolt-qed also copies, or re-proves without `decide +kernel`, the equations between EthLib's word-level code and its models where the proofs need them.
- Clean's Keccak `absorbBlock` is not used: `hash-specs` reports that it XORs the block into the wrong lanes.
  `hash-specs` itself has no licence file.
  No GPL or LGPL source (`fips-180-4-lean`, `LeanSha256`) is used; jolt-qed is Apache-2.0.

## 6. Results

| # | Result | Statement | Needs |
|---|---|---|---|
| R1 | Row-level soundness and completeness for guests that call the twelve | `JoltInstance.soundness` and `JoltInstance.completeness` with `SourceInstruction` including `.inline`; each inline runs `rowsAuto k`, and the private inputs include the inline advice words, which have no effect on a program without inline advice rows | I0, I1a, I1b |
| R2 | Per-inline correctness | Frame and footprint for every input; `rows_sound` and `rows_jolt_advice_complete` under `Pre k`; determinism or the representative corollary, for the twelve | I2 per inline |
| R3 | Bug regression | The pre-`db9679295` secp256k1 DIV rows admit a run under `rd = rs1` whose output is not `a / b mod q`; the current rows satisfy `rows_sound` | I2 for DIV |
| R4 | Inline-level soundness under the modelled acceptance relation | R1 plus R2: if the witness satisfies `AllConstraints`, every inline call satisfies its frame and footprint, and every call whose state satisfies `Pre k` satisfies `InlineSpec k` | R1, R2 |
| R5 | Whole run for guests that call the twelve | `sail_soundness` and `sail_reproduces` against `platformRun`: Sail's `try_step` plus, on supported inline encodings, a step that always satisfies the frame and satisfies `InlineSpec k` when `Pre k` holds; the per-call preconditions are a premise or an invariant the guest supplies | I3 |

"Accepted" in R4 and R5 means the modelled relation `AllConstraints`, as for the existing theorems.
Connecting it to Jolt's verifier needs the sumcheck and commitment layers, which are outside this plan.
Claims that the model matches production Jolt also depend on T5's typing fixes.
None of the five results says that a guest computes a hash or verifies a signature (section 1.2).

The 2026-11-11 survey found per-row machine-checked soundness for OpenVM 2.0's Keccak-f and SHA-256/512 (Lean, no completeness), a partial Lean proof of Scroll's Keccak-256 circuit (which found an `is_final` under-constraint), and a determinism check of RISC Zero's Keccak accelerator (Picus).
Clean proves soundness and completeness for standalone SHA-256 and BLAKE3 gadgets that are not part of a zkVM.
The survey found nothing for BLAKE2b or secp256k1 field precompiles in a production zkVM, no production precompile with a completeness result, and no project that states a precompile theorem at the level the guest sees.

## 7. Phases

Effort figures are rough.
They extrapolate from jolt-qed's history: the DIV/REM equivalence proofs took 560 to 1,250 lines per instruction plus about 3,400 soundness lines, and the System family (2,390 lines) took about four hours of worker time on 2026-11-08.
Long hash sequences have no precedent in the repository, and their estimates are the least certain.

### Track T: translation trust

Every Jolt artifact in the headline statement reaches Lean by hand or through a generated file that cannot be regenerated today: the 22 R1CS rows, the 55 lookup tables, the flags and table assignments in `metadata.lean`, the 57 generated expansions in `ExpansionsAutomated.lean` (`JoltConstraints/model_review.md:189` records that the generator at the pin cannot reproduce the file), the system expansions, the decoder and the tracer semantics.
Only the Sail model is regenerated and diffed in CI.
The dangerous translation errors are the ones proofs cannot catch: a Lean constraint, flag or table that is correct, or stronger, where Jolt's is wrong, or weaker.
Track T shares its driver with the inlines.

| Step | Work | Output | Size |
|---|---|---|---|
| T1 (first) | Rust driver in `scripts/expansion-parity/`, built like `scripts/difftest/jolt-trace` with `JOLT_DIR` at the pin. It emits stamped rows through the production entry point for Jolt's 360 golden-fixture inputs, aliased operands, `rd = x0`, `rs1 = x0`, a few hundred random operands and immediates (compressed and not), and every native kind once, together with each kind's circuit flags, instruction flags, lookup table and RAF flag. A Lean test executable compares them with `SourceInstruction.expand`, `stamp_sequence` and `metadata.lean` and lists every mismatch | Mismatch report at the current pin; a CI job, non-blocking until clean | 2–4 days plus fixes |
| T2 | Raw decoder sweep: all 2^16 compressed parcels and 32-bit words per opcode class, `joltDecode` and `joltUncompress` against `decode.rs` (not the tracer's decoder) | Agreement report; CI job | 1–2 days |
| T3 | Constraint data: emit the 22 R1CS rows, per-kind flag vectors, table assignments and the four `UnbatchedClaimExpr` relations as generated Lean; prove each handwritten equation and `metadata.lean` entry equal to the generated form (the sp1-lean pattern); CI regenerates and diffs | `Generated/Constraints.lean`, `Faithful/*.lean` | 1–2 weeks |
| T3b | Coverage ledger: one row per field of `AllConstraints` and per modelled artifact, with the kind of check behind it (generated and proved equal, sampled test, source audit, outside the model) and the Jolt revision checked | `docs/coverage-ledger.md`, kept current by T1–T7 | 1–2 days, then upkeep |
| T4 | Lookup tables: emit `materialize_entry` vectors at edge and random indices and check them against a computable twin proved equal to the generic-field tables; this samples entries and does not prove agreement at every index | Table test module | 3–5 days |
| T5 | Witness-typing review: for each witness column, write down what Jolt's verifier knows (committed field element, range-checked value, public value) and compare it with the Lean type; then fix the untrusted-advice gap (Lean advice words are 64-bit; Jolt's verifier accepts any committed field element) and any other mismatch | Review note, then a model change | 2–3 days of review; the fix is separate |
| T6 | Symbolic recipe emission for built-in expansions, including branches on register identity; bring the System expansions and the native mapping under the same data; define `*ProgramAuto` from the data or prove the existing definitions equal | Regenerable `ExpansionsAutomated.lean`; the sampling generator retired | 1–2 weeks |
| T7 | Provenance manifest (Lean file to Jolt paths to revision checked); CI checks one pin and no local paths or fork citations; adopt openvm-fv's gates (hygiene scan, axiom allowlist in the build, comparator replay of frozen headline statements) | `provenance.toml`, CI jobs | 2–3 days |

### Track I: inlines

| Phase | Work | Output | Size |
|---|---|---|---|
| I0 foundations | (a) Extend the T1 driver to inline rows for all 27: production entry point, allocation cases, allocator restoration, fixture-hash and operand-uniformity checks, the write-before-read check for the twelve, the round-trip comparison; generated `Inlines/Generated/*.lean`. (b) Known-answer differential before any proof: run each of the twelve in Jolt's tracer on known-answer and random inputs, with honest advice from `build_advice`, and compare with the chosen Lean specification evaluated by `#eval` (test module only). (c) Answer the open questions of section 10. (d) Lean transcriptions of Jolt's advice functions for the seven secp256k1 inlines, tested against Rust on random and edge-case inputs, including edge-case scalars for the GLV split. (e) The generic frame lemma for rows that write only pool registers, instruction temporaries and stores in a footprint, with the per-inline write set computed from the generated rows. (f) Check every SDK call site of the twelve against `Pre k` | Generated rows for 27 inlines; known-answer report; tested advice transcriptions; frame lemma | 1–2 weeks |
| I1a language, hash inlines | `SourceInstruction.inline` over a generated key set (the five hash keys first), expansion with the `rd = x0` rewrite and the registration check of section 5.2, class-dependent capacity and the generalised `program_facts.lean` proofs; revisit `Layer4/Reachable.lean`; re-establish `JoltInstance.soundness` under today's `InLanguage` and extend `JoltInstance.completeness` to the hash rows. Acceptance: preprocessing the 3,121-row `KECCAK256_ABSORB_PERMUTE` expansion succeeds in the model | R1 for the hash inlines | 1–2 weeks |
| I1b language, advice inlines | After D2: the `inline_advice` field and the changed honest rule (section 5.3); the adapted Layer 5a, 6 and 7 contracts; the seven secp256k1 keys; re-establish `JoltInstance.soundness` and extend `JoltInstance.completeness` | R1 for secp256k1 | 1–2 weeks |
| I2 per-inline proofs | In this order: `GLVR_ADV`, secp256k1 MUL and SQUARE (both fields), secp256k1 DIV (both fields) with R3, `BLAKE2`, `SHA256` and `SHA256_INIT`, `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`. Shared libraries, parametric for later inlines: limb and carry lemmas; `p'` cross-term lemmas parametric in the modulus and limb count (secp256k1 needs 1–3 limbs, P-256 later 3–4); the advice-store lemma parametric in the word count; 32-bit "dirty upper half" invariants (SHA-256, BLAKE3 later); a 64-bit rotate-and-XOR library (BLAKE2b, Keccak). Each inline's completeness lemma with Jolt's advice, including the GLV bound | R2, R3, R4 | `GLVR_ADV` rows: hours; GLV bound: about a week; secp256k1 field operations: about two weeks with shared lemmas; each hash: 2–4 weeks |
| I3 whole run | Platform step `platformStep`: Sail's `try_step` on RISC-V encodings; on supported inline encodings, a step that satisfies the frame and footprint and, under `Pre k`, `InlineSpec k`. Generalise `BlockSimulates`, `sailRun` and `sailRun_of_chain`; drop `BlockConforms.riscv` for supported encodings; extend the decoding premise with the combined pipeline; give inline stores a footprint in `CodeInv.storeBase` and the I/O-window fields (`NoCodeStore`, flag-word premises); state the per-call preconditions as a premise or an invariant | R5 | 2–3 weeks |

Order and parallelism:

- T1 and I0 come first and share the driver.
  T2, T3b and T7 can run beside them.
- I1a needs I0 only.
  I1b needs I1a and decision D2.
  The row-level proofs of I2 (`rows_sound` and the frame on generated rows) can start as soon as I0(a) lands, in parallel across inlines; only their link to the soundness theorem waits for I1a or I1b.
- T3 to T6 can run in parallel with I1 and I2.
  T5's fixes land before I3, because I3 restates the whole-run premises.
- I3 needs the frame, footprint and soundness lemmas of I2 for every inline it supports.
- Each phase follows `AGENTS.md`: statements are staged with `sorry` first and reviewed before they are proved.

## 8. Decisions

- **D1. The inline step in the whole-run theorem.**
  The reference machine runs each supported inline by its Lean specification.
  A similar step for the seven `0x5B` instructions was deferred on 2026-11-11 because it only relocates trust into a Lean definition.
  For inlines the specification is the standard's function (SHA-256, Keccak-f, BLAKE2b F, arithmetic modulo the secp256k1 primes), independent of Jolt's rows, and the proof that the rows implement it is the content of the result.
  The `0x5B` question stays deferred.
- **D2. Inline advice words are private inputs** (section 5.3).
  The alternatives were to transcribe Jolt's advice functions into the honest rule, which keeps today's statement but leaves it false for guests that output an inline's stored words, or to leave the secp256k1 inlines out.
  The chosen design keeps the theorem's shape, keeps the meaning of every existing theorem, and states what Jolt's verifier enforces.
  It widens the honest run beyond what Jolt's prover code computes.
  It changes definitions behind `InLanguage`, and Ari's approval is required before I1b.
- **D3. Specifications** come from EthLib, copied with provenance (section 5.6).
- **D4. Driver location:** `scripts/expansion-parity/`, next to difftest.
  A stable JSON export from Jolt (J5) can come later.
- **D5. Jolt revision.**
  Inline rows are pinned to Jolt `main` when I0 starts.
  Inline rows have not changed since 2026-09-02 except NTT (added 2026-10-28).
  Open upstream PRs change Keccak (a16z/jolt#2369, #2388, #2391) and secp256k1 (#2386) sequences; the CI regeneration diff signals when a re-proof is due, and Keccak comes last in I2.
- **D6. Field-inline stays out.**
  Revisit after T3 and #41 land.
- **D7. `rd = x0` encodings of inlines that read `rs3`** are excluded by the registration check (section 5.2).
  jolt-qed also asks Jolt to reject them at expansion (J6), after I0, by rejecting rather than initialising the temporary, because an inline that writes its output to address 0 is meaningless either way.

## 9. Requests to Jolt

Each is a small PR or issue.

- J1. Enforce the inline write-target rule where builders choose destinations: reject a builder row that writes `x1..x31` or `vr32..39`, while allowing helper temporaries in `vr40..47` and architectural registers as inputs.
  `register_operand` serves reads too and should not reject architectural registers.
- J2. Hash flags and lookup tables in `registered_inline_expand_parity_hashes.jsonl` (or a sibling fixture), so that a semantic change to a row kind changes the fixture.
- J3. A test harness that injects dishonest advice into inline sequences.
  The secp256k1 DIV aliasing test passes only honest quotients.
- J4. Fix stale docs: the book's inline opcode table (`book/src/how/optimizations/inlines.md:64-75`), the BLAKE3 KEYED64 "PARENT flag" comment, and the BIGINT builder comment that claims reliance on zeroed pool registers (the builder assigns both accumulators before use).
- J5. Later: a stable JSON export of rows, recipes, flags and R1CS; `jolt-lean-gen` support for `Inline` if Jolt wants it there.
- J6. Reject `rd = x0` for inlines that use `rs3` as a pointer (D7).

jolt-qed housekeeping that goes with I0: fix `docs/whole-run-theorem.md:124`, which says that `0x5B` holds the hash and big-integer instructions; correct the description of difftest in the README and in `docs/whole-run-theorem.md:175`, which presents it as evidence for the Lean models' faithfulness although Lean takes no part in it; add a glossary entry for the three meanings of "inline"; update issue #37 with this plan.

## 10. Open questions for I0

1. Which inline registration set the verifier's bytecode preprocessing uses, and how a guest that calls an unlinked inline fails.
2. Whether any of the twelve uses helpers that allocate instruction temporaries, which would make the `rd = x0` allocation case matter for the hashes (known only for NTT so far).
3. What a misaligned or out-of-range `LD` or `SD` row inside an inline does after floor-addressed memory (`629b7d959`) and range-checked loads (`4e55c9a5f`): unsatisfiable, a trap, or something else.
   The answer fixes the alignment preconditions.
4. The carry bounds in the secp256k1 sequences (the `c2` accumulator and the final `assert_lte`), so far taken from builder comments.
5. Whether any builder branches on register identity (the exhaustive uniformity check answers this).
6. Whether every in-scope builder writes each pool register before reading it (the write-before-read check answers this).
7. Whether `trace_file` in `register_inlines!` affects proving.

## 11. Risks

| Risk | Mitigation |
|---|---|
| A specification is wrong, making R2 a theorem about the wrong function | Copied, reviewed specifications; two-layer specifications; known-answer tests on the specification and differential runs against Jolt's tracer in I0 |
| Elaborating or `rfl`-checking 3,000-row definitions is slow | Chunk generated files per round; prove `builder = generated` per chunk; measure in I0 on Keccak before committing to the shape |
| Jolt changes inline rows during the proofs (Keccak and secp256k1 PRs are open) | CI regeneration diff; proofs against the structured builder, which limits a local row change to a few lemmas; Keccak last |
| The widened honest run weakens the meaning of existing theorems | The `inline_advice` field reaches only `VirtualAdvice` rows inside `.inline` expansions and has no effect on programs without such rows; DIV and REM are unchanged until a deliberate cleanup |
| Statement drift or vacuity | Comparator replay of frozen statements (T7); each `rows_sound` instantiated on a known-answer input |
| The extractor (driver plus generator) is wrong | It runs Jolt's production entry point and checks Jolt's fixture hashes; the generated Lean is rendered back and compared with Rust's rows; a person reviews T1's first mismatch report |
| A precondition is unsatisfiable, or real guests do not establish it | Known-answer instances; I0(f) checks every SDK call site against `Pre k` |
| Jolt's GLV split exceeds `2^128` for some scalar, and the completeness lemma is false | I0 tests edge-case scalars first; a failing scalar is a Jolt completeness bug to report, and the lemma then states the scalars for which the split fits |
| The generic machinery fits only the twelve | The driver, uniformity and round-trip checks run on all 27 from the start; the field-operation and advice-store lemmas are parametric; NTT's allocation case is in the driver's checks |
| Readers take the results to cover the SDK | Section 1.2's boundary statement goes next to every public statement of the results |

## 12. After the inlines: the SDK guest code

This section describes the gap that section 1.2 states, and a later track that would close it.
Code references are to a16z/jolt `main` at `a6b6dc717`.

### 12.1 Where the line falls

```
 ecdsa_verify, Sha256/Keccak256/Blake2b::digest            guest Rust     out of scope
 c < q checks, point add/double, 4-scalar ladder,          guest Rust     out of scope
 decompose_scalar_impl, padding and buffering
 ──────────── inline instruction: MULQ, DIVQ, GLVR_ADV, SHA256, … ────────────
 R2 inline specification: which outputs the rows allow     this plan
 Sail RV64 + inline platform step (sail_soundness, R5)     this plan
 Jolt constraints (JoltInstance.soundness, R1, R4)         this plan
```

The guest is a RISC-V image, and the SDK is part of it.
The inline specifications are relational: MULQ allows one or two values of `c`, and `GLVR_ADV` allows any six words.
The SDK turns these weak guarantees into functions by checking each output and calling `spoil_proof()` when a check fails.

| Code | Where | What it relies on |
|---|---|---|
| Field wrappers: canonicity checks after each inline, limb-wise equality, add, sub and neg through arkworks `new_unchecked` | `secp256k1/src/sdk.rs` L17–30, L82, L136, L184, L226, L268 | Inputs to add and sub are canonical; every inline-backed operation checks `c < q` |
| Generic affine point code: infinity as `(0, 0)`, `double`, `add`, `double_and_add` | `sdk/src/ec.rs` L96, L165, L182, L204 | `(0, 0)` is not on the curve; every division has a nonzero divisor |
| `decompose_scalar_impl`: sign decoding and the recombination check after `GLVR_ADV` | `secp256k1/src/sdk.rs` L751–790 | The input scalar is canonical; λ matches β |
| `endomorphism` and the constants G, 2^128·G, 2^128·G + G, β, λ | `secp256k1/src/sdk.rs` L670–750 | `φ(Q) = λ·Q`; the constants are the claimed multiples of G |
| `secp256k1_4x128_inner_scalar_mul` and `ecdsa_verify` | `secp256k1/src/sdk.rs` L819, L866–920 | All of the above; `p < 2n` |
| Digest wrappers for SHA-256, Keccak-256 and BLAKE2b: buffering, padding, length and counter encoding, byte order | `sha2/src/sdk.rs`, `keccak256/src/sdk.rs`, `blake2/src/sdk.rs` | The memory layout matches each inline's specification |
| rustc and LLVM | the guest build | The compiled code means what the Rust source means |

### 12.2 Why it is out of scope

1. It is a different theorem.
   jolt-qed's headline theorems hold for every image.
   SDK correctness is a property of particular programs, and it needs reference specifications that jolt-qed does not formalize: FIPS 180-4, Keccak, RFC 7693, SEC 1 ECDSA and the secp256k1 group.
2. It is about a different object.
   jolt-qed reasons about machine code, and the SDK is Rust source.
   Nearly every SDK function is `#[inline(always)]`, and a compiled image has no single `ecdsa_verify` body: the compiler copies the code into each caller.
   A proof needs either a Rust semantics plus trust in the compiler, or a separate proof for each compiled image.
3. It builds on this plan.
   The SDK proof takes the R2 inline specifications as its assumptions.

### 12.3 What could go wrong

Most of the SDK's checks matter only against a malicious prover.
Jolt's tests run the honest host advice, which always passes the checks, and a missing or wrong check therefore never fails a test.
The hashes are the exception: their inlines take no advice, and test vectors cover much more of their code.

| Area | Failure | Would tests notice |
|---|---|---|
| Field wrappers | A missing `c < q` check after MULQ, SQUAREQ or DIVQ lets the prover store `c + q` (section 5.3). Limb-wise equality then says that equal elements differ, and arkworks' unchecked add, which assumes canonical inputs, can return a wrong value | No: honest advice is always canonical |
| Division | `div_assume_nonzero` with divisor 0: if the dividend is nonzero no result passes and the honest host panics; if it is 0 every result passes and the prover chooses. Each call site needs its own argument: `double` checks `y ≠ 0`, `add` divides only when the x-coordinates differ, `double_and_add` has an explicit `divisor.is_zero()` branch, and `ecdsa_verify` rejects `s = 0` | No: only adversarial points reach these cases |
| Unchecked constructors | `from_u64_arr_unchecked` on untrusted limbs; its doc comment (`ec.rs` L20) says this can abort host trace generation or give an incorrect trace | Partly |
| Montgomery add | The scalar-field wrapper adds plain limbs with arkworks' Montgomery-form add; a comment argues that this is correct because add and sub are the same in both forms. The argument is true, and nothing checks it | Yes, if it were wrong |
| GLV decomposition | `GLVR_ADV` is pure advice, and soundness rests on three checks: each sign word decodes to a bool; `|k1|, |k2| < 2^128` holds because each has two limbs; `k1 + k2·λ = k` in the scalar field. Dropping the recombination check lets the prover substitute any scalar, which forges signatures. Several decompositions pass the check and the prover chooses one; all give the same point only because `φ(Q) = λ·Q` | No for a dropped check; yes for a wrong β, λ pairing, which breaks every input |
| Point arithmetic | The public key is the attacker's input. For some keys the ladder's lookup entries coincide or are negatives of each other (`Q = −G` makes `G + Q = ∞`), and the branches for `P = Q`, `P = −Q`, a point at infinity and `2P + Q = ∞` must all be right. `double` returns infinity when `y = 0`, which is correct because secp256k1 has no point of order 2. Infinity as `(0, 0)` is safe because `0 ≠ 0³ + 7` | Rarely: random inputs do not reach these branches |
| `ecdsa_verify` | Its doc comment says that it validates every input and that callers need no validation: canonical z, r, s and Q, Q on the curve, Q not at infinity, r, s and z nonzero. It reduces `R.x` mod n with one conditional subtraction, correct because `p < 2n`, and rejects `R = ∞` because then `R.x = 0 ≠ r`. A formal specification must also state three choices that are not bugs: z must already be below n (a hash at or above n is rejected, not reduced; probability about 2^-128), z = 0 is rejected, and there is no low-s check | Validation gaps: no |
| SHA-256 | Padding byte `0x80`, a 64-bit big-endian bit length, the extra block when 56 or more bytes are buffered, the `initial` flag that selects `SHA256_INIT` for the first block, and byte order: the SDK passes message bytes unchanged, the inline expects a big-endian block (`sha2/src/sequence_builder.rs` L26), and the SDK byte-swaps the output words | Mostly yes: test vectors |
| Keccak-256 | Rate 136, padding `0x01 … 0x80` (Keccak, not SHA-3's `0x06`), both markers in one byte `0x81` when one byte of the block remains, and aligned input passed straight to the inline while unaligned input is copied first | Mostly yes |
| BLAKE2b | The parameter word `h[0] ^= 0x01010000 ^ outlen`, a byte counter that is 64-bit only, the final flag, and the rule that keeps at least one byte for the final block (`blake2/src/sdk.rs` L245), the usual BLAKE2 mistake when the length is a multiple of 128 | Mostly yes |
| Memory safety | All three digest wrappers use unsafe pointer copies and transmutes, and memory safety is part of their correctness | Partly |
| Inline asm | Each inline call is an `asm!` block with `options(nostack)`. A block wrongly marked `nomem` or `readonly` would let the compiler move memory accesses across the inline. This plan's frame result says which memory each inline touches, and the SDK proof would check that each block declares at least that | No |
| Compiler | A rustc or LLVM miscompilation leaves every jolt-qed theorem intact and breaks the link from the Rust source to the image | Rarely |

### 12.4 How to model it

Model the guest as a nondeterministic program that can fail.
Each inline call returns the value the prover supplies, subject to its R2 specification, and `spoil_proof()` is failure.
This matches `InLanguage`, which says that some private inputs give a run that passes `SpoilAssertsPass`.
Each routine gets two theorems:

- soundness: for every advice choice, if the run does not spoil, the output equals the reference specification;
- completeness: with Jolt's advice functions (`joltAdvice` from section 5.4), the run does not spoil on valid inputs.

A sketch (nothing exists):

```lean
/-- The prover's choice for each inline call, in call order. -/
abbrev Advice := List (Array (BitVec 64))
abbrev Guest := StateT Advice (Except Spoiled)

def Fq.mul (a b : Fq256) : Guest Fq256 := do
  let c ← pop                                -- prover's choice
  unless MulQ.allowed a b c do spoil          -- rows: the R2 specification
  when (q ≤ c.toNat) spoil                    -- SDK check, sdk.rs:184
  pure c

theorem ecdsaVerify_sound (adv : Advice) :
    (ecdsaVerify z r s Q).run' adv = .ok true →
      Secp256k1.ECDSA.Verify z.val r.val s.val Q.toCurve

theorem ecdsaVerify_complete (h : ValidInputs z r s Q) :
    Secp256k1.ECDSA.Verify z.val r.val s.val Q.toCurve →
      (ecdsaVerify z r s Q).run' (joltAdvice z r s Q) = .ok true
```

### 12.5 How to verify it

| Route | How | Strength | Cost |
|---|---|---|---|
| (a) Source level | Translate the SDK crates to Lean with Aeneas (used for Microsoft's SymCrypt ML-KEM); inline asm becomes opaque calls whose behaviour is assumed from R2 | One proof for every image built from the source | The unsafe buffer code is outside Aeneas's safe-Rust fragment and needs a safe refactor or a hand-written model; arkworks' generic bigint code may be hard to extract; rustc and LLVM stay trusted |
| (b) Binary level | Symbolic execution of the compiled image in Lean against the same Sail and inline semantics, the way s2n-bignum (HOL Light) and LNSym (Lean, Arm) verify cryptographic code | No compiler trust; composes with `sail_soundness` directly | One proof per compiled image, redone after any recompile; `#[inline(always)]` spreads each routine across its callers |
| (c) Mathematics first | Prove the facts the code relies on, independent of the code, on Mathlib's `WeierstrassCurve` affine group law: `φ(Q) = λ·Q` for this β, λ pair; the constants are the claimed multiples of G (by kernel `Nat` arithmetic, within the strict checking standard); `(0, 0)` is not on the curve and there is no 2-torsion; each affine formula branch equals the group law; the GLV recombination gives `k1·Q + k2·φ(Q) = k·Q`; the 4-scalar ladder computes `Σ ki·Pi`; `p < 2n` | Reusable by (a) and (b); the best-defined piece | Can start before any code-level work |

Proposed order: route (c) first, then route (a) with trust in rustc and LLVM stated as an explicit assumption, and route (b) only for a routine that someone needs with no compiler trust.
secp256k1 comes before the hashes, because it has prover choice, adversarial inputs and forgery as the failure.
The track starts after this plan, and it has not been sized.

End to end, the two tracks compose as follows:

```
AllConstraints
  ── R4, R5 (this plan) ──►            some advice gives a Sail + inline run of the image,
                                        no spoil, output o
  ── compiler assumption or route (b) ──► some advice gives a Rust-model run, no spoil, output o
  ── SDK soundness (later track) ──►    o = ECDSA.Verify(z, r, s, Q)
```

### 12.6 What this plan provides for the later track

R2 states each inline's allowed outputs relationally (the set of outputs the rows accept for given inputs), at the memory level the SDK uses: which bytes each call reads and writes, and in which byte order.
The later track takes R2 unchanged.
Stating R2 as "returns `a·b mod q`" instead would be false (section 5.3), and it would hide exactly the obligations that the SDK's checks discharge.
