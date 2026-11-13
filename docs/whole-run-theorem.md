# What the whole-run theorems prove

This page states what jolt-qed's two whole-run theorems prove, what they assume, and what they do not say.
Read it before citing either theorem.
[`riscv-alignment.md`](riscv-alignment.md) gives the reasoning behind each decision, and `JoltConstraints/WholeRun/Top.lean` holds the theorems and their proofs.

In one sentence: if Jolt's tracer runs a program, then the Sail RISC-V model, started from the matching state, runs the same program up to its first EBREAK, one `try_step` per source instruction, and ends in a matching state with the same outputs and panic flag.
The claim holds under the premises listed below, and the most important limits are in [What the theorems do not say](#what-the-theorems-do-not-say).

## The two theorems

```lean
theorem HonestTrace.sail_reproduces {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      WholeRun.sailRun n (sailInit trace.initialState) = .ok () s ∧
      Related halt s ∧
      trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
        trimTrailingZeros final.jolt_device.outputs ∧
      (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ final.jolt_device.panic = true) ∧
      (SailHalted joltInstance.program s ∨ halt = final)

theorem JoltInstance.sail_soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) :
    ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
      trace.matches_outputs joltInstance ∧
      (trace.prover_config joltInstance).isSome ∧
      trace.SpoilAssertsPass ∧
      ∃ (pre : List Block) (halt final : SailJoltState),
        HaltPrefix trace pre halt final ∧
        ((∀ b ∈ pre, BlockConforms joltInstance.program b) →
          ∃ (n : Nat) (s : SailState),
            sailRun n (sailInit trace.initialState) = .ok () s ∧
            Related halt s ∧
            trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
              trimTrailingZeros joltInstance.outputs ∧
            (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ joltInstance.panic = true) ∧
            (SailHalted joltInstance.program s ∨ halt = final))
```

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for both.

`sail_reproduces` is about a trace you already have.
An `HonestTrace` is a run of Jolt's tracer, as modelled in Lean, on the program and some private inputs.
A `HaltPrefix` of it is the list of blocks before its first EBREAK, where a block is one source instruction with the Jolt states before and after its rows.
If Jolt's prover accepts the trace (`hcfg`) and every block of that prefix conforms (`BlockConforms`), Sail's emulator loop `sailRun`, started from `sailInit` of the trace's initial state, takes `n` successful steps to a state `s`.
`sail_soundness` needs no `hcfg` premise, because `JoltInstance.soundness` returns an accepted trace.

`sail_soundness` is about an instance the constraints accept.
Jolt's soundness theorem, `JoltInstance.soundness`, turns a witness that satisfies `AllConstraints` into an honest trace with the instance's claimed outputs and panic flag.
`sail_soundness` applies `sail_reproduces` to that trace.

## What the conclusion says

The Sail state `s` satisfies four properties:

- `Related halt s`: Sail's state matches Jolt's state `halt`, as the next subsection describes.
- Sail's output region, with trailing zero bytes dropped, equals Jolt's outputs with trailing zero bytes dropped.
- Sail's panic word is nonzero exactly when Jolt's panic flag is set.
- Either Sail's PC is the address of an EBREAK row of the program (`SailHalted`), or the trace ended at `halt` without reaching an EBREAK.

### The relation `Related`

`Related jt s` (`JoltConstraints/WholeRun/Relation.lean`) says how a Sail state `s` matches a Jolt state `jt`:

- Sail's registers are Jolt's, as `sailRegs` lays them out. The general-purpose registers come from Jolt's state. Jolt keeps the six machine-mode CSRs in virtual registers `v34`–`v39` and the LR/SC reservation in `v32` and `v33`; Sail's CSRs and reservation are those values, with `mstatus.MPP` read as machine mode.
- Sail's `PC` is Jolt's `nextPC`, the register in which a Jolt state records the address of the next instruction.
- Sail's `misa` is its reset value, and its memory regions are the platform's. Sail's `minstret` and its increment flag are unconstrained.
- Sail's RAM equals Jolt's RAM at and above `RAM_START_ADDRESS`.
- Between `memLow`, the lowest address in Jolt's memory layout, and `RAM_START_ADDRESS`, each byte of Sail's memory is the byte Jolt's device reads there, except in the panic and termination words.
  Those bytes must be present, and Sail's panic word must be nonzero exactly when Jolt's panic flag is set. `Related` constrains them no further.
- The advice tape is not part of the relation.

`Related` also records facts that keep Sail's `try_step` a plain fetch-decode-execute step: the step invariant, Sail's HTIF device being off, and the presence of every memory byte the run can touch.

## What the theorems assume

Each premise is in one of four classes:

- a **platform** premise is true of Jolt's real platform, but Jolt does not check it;
- a **documented deviation** excludes a case where Jolt and the RISC-V specification really differ;
- a **scope** premise excludes a part of Jolt that the proof does not cover yet;
- a **soundness** premise belongs to `JoltInstance.soundness` and appears only in `sail_soundness`.

`sail_reproduces` also takes `hcfg`, which says that Jolt's prover accepts the trace.
Jolt checks this itself, and `sail_soundness` obtains it from `JoltInstance.soundness`.

### Platform premises

| Premise | Meaning | What would remove it |
| --- | --- | --- |
| `DecodedFrom` | Agreement of the program with Jolt's `decode_elf` on `elf`, the sections of the guest ELF | Nothing in Jolt (trusted, as described below) |
| `RowsAligned` | Every row address is even. Jolt's ELF loader does not check this. | A check in Jolt's preprocessing. |
| `HeapNoWrap` | `heap_end ≤ 2^64 - 8`. | A check in `MemoryLayout.new`. |

`DecodedFrom` (`JoltConstraints/WholeRun/Elf.lean`) transcribes `decode_elf` from `crates/jolt-program/src/image/elf.rs` up to the call of `decode_instruction`.
The proof derives from it that the committed bytecode is what Jolt's decoder makes of the program image (`ImageDecoded`).
No constraint can check `DecodedFrom`, because it describes how the bytecode was produced before proving starts.
Its input `elf` is the list of sections that the `object` crate parses from the ELF file (address, size, data, and whether the section is text) and the entry point.
The program's `memory_init`, `program_end` and `entry_address` are what `decode_elf` computes from them.
Its rows are, one to one and in order, the instructions `decode_text_section` finds in the merged text ranges, each with the instruction's address and width, and each RISC-V row is `joltDecode` of the instruction's word.
A row of one of Jolt's own instructions is constrained only in address and width, because Lean does not transcribe Jolt's decoder for those opcodes.
`DecodedFrom` also leaves out the checks by which `decode_instruction` rejects a program.
Every program Jolt builds from the ELF therefore satisfies `DecodedFrom`, and the relation still fixes the layout and every RISC-V row.
`decode_elf` never reads the data of a section below `RAM_START_ADDRESS`, and the data `elf` records for such a section may be arbitrary.
Three things stay trusted: that `elf` is what the `object` crate parses from the guest ELF, including that it gives every loaded text section of a successfully decoded ELF exactly as many bytes of data as its size; that Jolt's preprocessing and the verifier key were built from this program; and that the Lean transcriptions of `decode_elf`, `joltDecode` and `joltUncompress` match Jolt.

### Documented deviations

All five are fields of `BlockConforms`, which must hold for every block of the halt prefix.

| Premise | Meaning | What would remove it |
| --- | --- | --- |
| `no_code_store` | No store writes into an instruction row of the program. The check covers the whole aligned doubleword of each store, because Jolt's narrow stores rewrite their doubleword. Jolt keeps fetching the committed bytecode after such a store, while Sail fetches from memory; without Zifencei the specification allows both. | A constraint in Jolt that every store's doubleword lies outside the code, with the same check in the tracer. |
| `no_flag_word_load` | No load reads a byte of the panic or termination word. | Treating both words as plain memory in Jolt's tracer and verifier, with "panic" meaning "the panic word is nonzero". |
| `panic_store_nonzero` | A store into the panic doubleword leaves Sail's panic word nonzero. Jolt sets its panic flag on any such store, even of zero. | The same change as for `no_flag_word_load`. |
| `amo_no_flag_word` | An atomic memory operation on the I/O window touches no byte of the panic or termination word, across its whole doubleword. | The same change as for `no_flag_word_load`. |
| `no_zero_doubleword_load` | Every load's effective address is at least 8. Jolt's tracer records a byte, halfword or word load at the address of its doubleword, which is 0 below address 8, and returns zero, while Sail raises an access fault. Jolt's prover reads recorded address 0 as no access and does not reject the load. An LD records its own effective address, and an LD at address 0 escapes the check too. The premise excludes every LD below 8, to state one bound for every width. The prover rejects every other load below the lowest address of the memory layout, and the proof derives that bound (`Block.FirstRowAt.noLowLoad`). | A fault in Jolt's tracer for loads below the lowest address of the memory layout, as Sail has (jolt-qed#37). |

### Scope premise

| Premise | Meaning | What would remove it |
| --- | --- | --- |
| `riscv` (a field of `BlockConforms`) | Every block of the halt prefix runs a RISC-V instruction. Jolt's own instructions on opcode `0x5B`, such as its hash and big-integer instructions, have no block theorem yet. | A Lean specification of each of Jolt's instructions, and a step that runs those by their specification and every other instruction by `try_step` ([`riscv-alignment.md`](riscv-alignment.md) section 7). |

### Soundness premises (`sail_soundness` only)

`sail_soundness` keeps every premise of `JoltInstance.soundness` (`JoltConstraints/Soundness/Assumptions.lean`):

- `JoltField F`: the field's characteristic is above `2^128 - 2^64`. Both of Jolt's fields satisfy this: BN254 (the default Dory build) and `p = 2^128 - 1780711455` (the `akita` build, Jolt's production field since a16z/jolt#2403); `JoltField.akita` and `JoltField.bn254` (`Soundness/FieldModuli.lean`) prove it, including each modulus's primality, by Pratt certificates checked in Lean. Below characteristic `2^128` the constraints include Akita's canonical-address check (63), which Jolt's `akita` build enforces; it is what makes `2^128 - 2^64` enough.
- `SoundnessAssumptions.ramRegionFits`: the whole maximum padded RAM region lies below `2^64`. The comment in `Assumptions.lean` records it as still to be confirmed with a16z.
- `TemporaryRestrictions`: six restrictions that exclude programs exposing reported or suspected Jolt bugs.
  Jolt's verifier makes none of these checks.
- `UntrustedAdviceBlockFits`: a seventh temporary restriction, passed as the separate premise `adviceBlockFits` because soundness for advice given as bytes (`JoltInstance.soundness_onBytes`) does not need it.
  It excludes a configured maximum untrusted-advice size that is not a multiple of 8, where Jolt's verifier lets the prover commit block bytes no tracer run can hold.
  Jolt's verifier does not check it.

| Restriction | What it excludes |
| --- | --- |
| `tracerAddressChecks` | A load or store that fails Jolt's tracer address checks (a16z/jolt#2044 and related cases). |
| `hostCallsSucceed` | A host call (`VirtualHostIO`) that fails in the modelled execution. |
| `noMaxLengthTrace` | A trace that fills the largest power-of-two length the verifier admits, which Jolt's prover cannot produce. |
| `terminationThenStall` | A program whose next jump after a store to the termination word is not the stall (a JAL with offset 0), or that loads the termination word again. |
| `panicStoresOne` | A store to the panic word of any value other than 1, and a load of the panic word after such a store. |
| `claimsNoPanic` | An instance that claims a panic. With this restriction, the panic clause of `sail_soundness` says that Sail's panic word is zero. |

Four restrictions (`tracerAddressChecks`, `hostCallsSucceed`, `terminationThenStall` and `panicStoresOne`) constrain the next row the program attempts after every prefix of a relaxed execution, for every private input.
A relaxed execution is one in which every advice read gets an arbitrary answer; the attempted row need not succeed.
`noMaxLengthTrace` constrains every completed relaxed trace, and `claimsNoPanic` and `adviceBlockFits` constrain only the instance.
The deviation premises in `BlockConforms` are stated differently, as the next section explains.

## Conformance is a premise on a trace the verifier does not see

In `sail_soundness`, the private inputs and the trace are existentially quantified: `JoltInstance.soundness` proves that some trace exists, and does not name it.
`BlockConforms` is a premise on the blocks of that trace.
To obtain the Sail run, a reader has to prove that the halt prefix of the returned trace conforms.
A reader who sees only the instance cannot inspect those blocks.
The usual way is to show that the program conforms on every run it can take, for every private input.
That is sufficient but not required: a proof may also use what the theorem says about the returned trace.
For most deviations, conformance holds by construction of the program: compiled code does not store into its own instructions, and guests do not read the panic word.
It is still an argument about the program, which neither the theorem nor Jolt's verifier checks.

Every deviation premise that Jolt's constraints come to enforce leaves `BlockConforms`, and with it this argument.

## What the theorems do not say

- **They do not say anything about Jolt's verifier.** `AllConstraints` checks every constraint equation directly on the whole witness. Jolt's verifier instead runs sumchecks, reductions and a polynomial commitment scheme, which jolt-qed has not verified (see the [README](../README.md)). "Accepted" in `sail_soundness` means "has a witness that satisfies the modelled constraints".
- **They are one-directional.** Every honest Jolt run up to its first EBREAK is reproduced by Sail. The converse is not claimed: a Sail run need not correspond to a Jolt run, and the theorems say nothing about programs whose runs Jolt's tracer aborts.
- **They stop at the first EBREAK.** Jolt treats EBREAK as the end of the program, and the RISC-V reading of that is entering debug mode. The Sail model does not implement the debug extension, and the theorems stop in front of the first EBREAK or C.EBREAK without executing it ([`riscv-alignment.md`](riscv-alignment.md) section 4). They say nothing about later instructions.
- **They do not cover Jolt's own instructions**, the inline opcodes `0x0B` and `0x2B`, or the advice tape (see the scope premise above).
- **They describe a particular Jolt revision.** The system expansions, the decoder and the ELF loader (`decode_elf`) transcribe a16z/jolt `c336a6da7`, the head of a16z/jolt#2384. That change is not on Jolt `main` until a16z/jolt#2383 and #2384 merge ([`riscv-alignment.md`](riscv-alignment.md), Sources).
- **They compare outputs only up to trailing zero bytes**, as `JoltInstance.soundness` does.
- **They describe one hart configuration.** The Sail model is configured as an RV64IMAC hart with only M-mode and no interrupts, with Jolt's memory map ([`riscv-alignment.md`](riscv-alignment.md) sections 1 and 2). They say nothing about other configurations.

## What the theorems trust

- **The Sail model is the specification.** `LeanRV64D/` is generated from the model commit, compiler and patches pinned in `sail-import/PROVENANCE.toml`. The patches adapt the model's handwritten Lean support to the Lean version in use and configure the model as Jolt's hart; `PROVENANCE.toml` lists each change, including the fixes to the pinned model. `scripts/check-sail-model.sh` regenerates the model in CI and requires it to match the checked-in tree byte for byte.
- **Five generated declarations raise a Lean limit.** Three CSR if-chains and the two decoder mappings in the closure of the theorems carry declaration-local `maxRecDepth` options between 550 and 1450, and one of them a `maxHeartbeats` of 250000 ([`riscv-alignment.md`](riscv-alignment.md) section 8). No proof in `JoltBytecode/` or `JoltConstraints/` sets a limit.
- **The Lean models of Jolt are faithful.** Applying the theorems to Jolt itself requires trusting that the Lean definitions of its tracer, expansions, decoder, ELF loader and constraints match the cited Jolt revisions, and that the sections given to `DecodedFrom` are what the `object` crate parses from the guest ELF. The theorems do not prove that correspondence. The differential test in [`scripts/difftest/`](../scripts/difftest/) (jolt-qed#40) runs real binaries on the Sail emulator and on Jolt's tracer and compares the results; that is evidence for the correspondence, not a proof of it.
- **The Sail compiler preserves the model's meaning.** The CI check shows that the generated files are reproducible, not that the compiler translates the Sail model correctly.
- **Lean's kernel checks the proofs using three standard axioms.** Nothing in the closure of the theorems uses `sorry`, `native_decide`, `bv_decide` or `decide +kernel`.
