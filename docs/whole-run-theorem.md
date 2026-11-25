# What the whole-run theorems prove

This page states what jolt-qed's two whole-run theorems prove, what they assume, and what they do not say.
Read it before citing either theorem.
[`riscv-alignment.md`](riscv-alignment.md) gives the reasoning behind each decision, and `JoltConstraints/theorems/WholeRun/Top.lean` holds the theorems and their proofs.

In one sentence: if Jolt's tracer runs a program, then the Sail RISC-V model, started from the matching state, runs the same program up to its first explicit halt, one `try_step` per source instruction, and ends in a matching state with the same outputs and a halt kind that fixes the panic flag.
The claim holds under the premises listed below, and the most important limits are in [What the theorems do not say](#what-the-theorems-do-not-say).

## The two theorems

```lean
theorem HonestTrace.sail_reproduces {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      WholeRun.sailRun n (sailInit trace.initialState) = .ok () s ∧
      Related halt s ∧
      trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
        trimTrailingZeros (final.jolt_device.outputsOf final.sail.mem) ∧
      ∃ kind, final.halted = some kind ∧
        final.jolt_device.panic = (kind == JoltHaltKind.panic) ∧
        (SailHalted joltInstance.program s kind ∨ halt = final)

theorem JoltInstance.sail_soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    {params : WitnessParams} (givenInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance givenInputs witness)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
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
            trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
              trimTrailingZeros joltInstance.outputs ∧
            ∃ kind, final.halted = some kind ∧
              joltInstance.panic = (kind == JoltHaltKind.panic) ∧
              (SailHalted joltInstance.program s kind ∨ halt = final))
```

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for both.

`sail_reproduces` is about a trace you already have.
An `HonestTrace` is a run of Jolt's tracer, as modelled in Lean, on the program and some private inputs.
A `HaltPrefix` of it is the list of blocks before its first explicit halt, where a block is one source instruction with the Jolt states before and after its rows.
Jolt has two explicit halts (`haltSource` in `JoltConstraints/theorems/WholeRun/Halt.lean`): the `jolt.success` instruction ends a successful run, and EBREAK ends a run with a panic.
If Jolt's prover accepts the trace (`hcfg`) and every block of that prefix conforms (`BlockConforms`), Sail's emulator loop `sailRun`, started from `sailInit` of the trace's initial state, takes `n` successful steps to a state `s`.
`sail_soundness` needs no `hcfg` premise, because `JoltInstance.soundness` returns an accepted trace.

`sail_soundness` is about an instance the constraints accept.
Jolt's soundness theorem, `JoltInstance.soundness`, turns a witness that satisfies `AllConstraints` into an honest trace with the instance's claimed outputs and panic flag.
`sail_soundness` applies `sail_reproduces` to that trace.

## What the conclusion says

The Sail state `s` satisfies three properties:

- `Related halt s`: Sail's state matches Jolt's state `halt`, as the next subsection describes.
- The output bytes `outputsOf` reads from Sail's memory, with trailing zero bytes dropped, equal the output bytes it reads from the final Jolt state's memory, with trailing zero bytes dropped. Jolt keeps its outputs in the same shared byte memory as RAM, and `outputsOf` reads the output region of the memory layout, with zero for a missing byte.
- The final Jolt state records a halt kind `kind`, and Jolt's panic flag is set exactly when `kind` is the panic kind. Either Sail's PC is the address of the program's halt row of that kind (`SailHalted`, which takes the kind), or `halt` is the final state (`halt = final`). The panic clause comes from the halt kind; no memory word encodes it.

### The relation `Related`

`Related jt s` (`JoltConstraints/theorems/WholeRun/Relation.lean`) says how a Sail state `s` matches a Jolt state `jt`:

- Sail's registers are Jolt's, as `sailRegs` lays them out. The general-purpose registers come from Jolt's state. Jolt keeps the six machine-mode CSRs in virtual registers `v34`–`v39` and the LR/SC reservation in `v32` and `v33`; Sail's CSRs and reservation are those values, with `mstatus.MPP` read as machine mode.
- Sail's `PC` is Jolt's `nextPC`, the register in which a Jolt state records the address of the next instruction.
- Sail's `misa` is its reset value, and its memory regions are the platform's. Sail's `minstret` and its increment flag are unconstrained.
- Sail's memory equals Jolt's shared byte memory at every address (`Related.ram`), reading a missing byte as zero on either side. The same rule covers RAM and the I/O region below `RAM_START_ADDRESS`, and no address is excepted.
- Sail's memory holds a byte at every address from `memLow`, the lowest address in Jolt's memory layout, up to `memHigh` (`Related.present`).
- Jolt's memory layout is one that `MemoryLayout.new` builds (`Related.layout`).
- The advice tape is not part of the relation.

`Related` also records facts that keep Sail's `try_step` a plain fetch-decode-execute step: the step invariant and Sail's HTIF device being off.

## What the theorems assume

Each premise is in one of three classes:

- a **platform** premise is true of Jolt's real platform, but Jolt does not check it;
- a **scope** premise excludes a part of Jolt that the proof does not cover yet;
- a **soundness** premise belongs to `JoltInstance.soundness` and appears only in `sail_soundness`.

No premise is a documented deviation, that is, a premise that excludes a case where Jolt and the RISC-V specification really differ (see [Former deviation premises](#former-deviation-premises)).

`sail_reproduces` also takes `hcfg`, which says that Jolt's prover accepts the trace.
Jolt checks this itself, and `sail_soundness` obtains it from `JoltInstance.soundness`.

### Platform premises

| Premise | Meaning | What would remove it |
| --- | --- | --- |
| `DecodedFrom` | Agreement of the program with Jolt's `decode_elf` on `elf`, the sections of the guest ELF | Nothing in Jolt (trusted, as described below) |
| `HeapNoWrap` | `heap_end ≤ 2^64 - 8`. | A check in `MemoryLayout.new`. |

`DecodedFrom` (`JoltConstraints/theorems/WholeRun/Elf.lean`) transcribes `decode_elf` from `crates/jolt-program/src/image/elf.rs` at `ff6fc6568` up to the call of `decode_instruction`.
The proof derives from it that the committed bytecode is what Jolt's decoder makes of the program image (`ImageDecoded`) and that every row address is even (`RowsAligned`, which earlier revisions took as a separate platform premise).
No constraint can check `DecodedFrom`, because it describes how the bytecode was produced before proving starts.
Its input `elf` is the list of sections that the `object` crate parses from the ELF file (address, size, data, whether the section is text, whether it is writable, and the `$x` and `$d` mapping symbols that point into it) and the entry point.
The program's `memory_init`, `program_end` and `entry_address` are what `decode_elf` computes from them.
Its rows are, one to one and in order, the instructions `decode_text_section` finds in the merged text ranges, without the data ranges that `$d` mapping symbols mark, each with the instruction's address and width, and each RISC-V row is `joltDecode` of the instruction's word.
`DecodedFrom` includes every check by which `decode_elf` rejects an ELF, other than the checks of `decode_instruction`: a section whose end overflows, a truncated instruction parcel, an instruction at an odd address, an instruction extent that `code_region` rejects, and a writable section that overlaps the code region.
A row of one of Jolt's own instructions is constrained only in address and width, because Lean does not transcribe Jolt's decoder for those opcodes.
`DecodedFrom` also leaves out the checks by which `decode_instruction` rejects a program.
Every program Jolt builds from the ELF therefore satisfies `DecodedFrom`, and the relation still fixes the layout and every RISC-V row.
`decode_elf` never reads the data of a section below `RAM_START_ADDRESS`, and the data `elf` records for such a section may be arbitrary.
Three things stay trusted: that `elf` is what the `object` crate parses from the guest ELF, including that it gives every loaded text section of a successfully decoded ELF exactly as many bytes of data as its size; that Jolt's preprocessing and the verifier key were built from this program; and that the Lean transcriptions of `decode_elf`, `joltDecode` and `joltUncompress` match Jolt.

### Former deviation premises

`BlockConforms` has one field, `riscv` (the scope premise below), and it must hold for every block of the halt prefix.
Earlier revisions also had a documented deviation `no_code_store`: no store writes into an instruction row of the program.
Jolt keeps fetching the committed bytecode, while Sail fetches from memory, and without Zifencei the specification allows both.
The two differ only after a store changes a code byte.
Jolt's tracer at `ff6fc6568` rejects every store that changes a byte of its protected code region (`protected_store_ok` in `JoltBytecode/JoltISA/DeviceMemory.lean`), and that region covers every row byte that the image loads.
The proof now derives from this check that every block of an honest trace keeps the code bytes (`JoltCodeIntact.of_block` in `JoltConstraints/theorems/WholeRun/CodeInv.lean`). The premise is therefore gone.

Jolt at `ff6fc6568` has no panic or termination word: a run ends at an explicit halt row, and the I/O region below `RAM_START_ADDRESS` is ordinary shared byte memory.
The premises that excluded loads, stores and atomic operations on those words are gone with them.
The premise on loads from the doubleword at address 0 is gone too: the tracer now rejects every access below `RAM_START_ADDRESS` outside the mapped I/O regions (`effective_address_ok` and `JoltDevice.readable`), and `read_lower` in `JoltConstraints/theorems/WholeRun/SharedMemorySim.lean` derives the lower bound `memLow` from the checked read itself.
The earlier derivation from the prover's recorded address, `Block.FirstRowAt.noLowLoad`, no longer exists.

### Scope premise

| Premise | Meaning | What would remove it |
| --- | --- | --- |
| `riscv` (a field of `BlockConforms`) | Every block of the halt prefix runs a RISC-V instruction. Jolt's own instructions on opcode `0x5B`, such as its hash and big-integer instructions, have no block theorem yet. | A Lean specification of each of Jolt's instructions, and a step that runs those by their specification and every other instruction by `try_step` ([`riscv-alignment.md`](riscv-alignment.md) section 7). |

### Soundness premises (`sail_soundness` only)

`sail_soundness` keeps every premise of `JoltInstance.soundness` (`JoltConstraints/theorems/Soundness/Assumptions.lean`):

- `JoltField F`: the field's characteristic is above `2^128 - 2^64`. Both of Jolt's fields satisfy this: BN254 (the default Dory build) and `p = 2^128 - 1780711455` (the `akita` build, Jolt's production field since a16z/jolt#2403); `JoltField.akita` and `JoltField.bn254` (`Soundness/FieldModuli.lean`) prove it, including each modulus's primality, by Pratt certificates checked in Lean. Below characteristic `2^128` the constraints include Akita's canonical-address check (63), which Jolt's `akita` build enforces; it is what makes `2^128 - 2^64` enough.
- `SoundnessAssumptions.ramRegionFits`: the whole maximum padded RAM region lies below `2^64`. The comment in `Assumptions.lean` records it as still to be confirmed with a16z.

## Conformance is a premise on a trace the verifier does not see

In `sail_soundness`, the private inputs and the trace are existentially quantified: `JoltInstance.soundness` proves that some trace exists, and does not name it.
`BlockConforms` is a premise on the blocks of that trace.
To obtain the Sail run, a reader has to prove that the halt prefix of the returned trace conforms.
A reader who sees only the instance cannot inspect those blocks.
The usual way is to show that the program conforms on every run it can take, for every private input.
That is sufficient but not required: a proof may also use what the theorem says about the returned trace.
Since no deviation premise remains, `BlockConforms` asks only that every block of the halt prefix runs a RISC-V instruction.
Every scope premise that the proof comes to cover leaves `BlockConforms`, and with it this argument.

## What the theorems do not say

- **They do not say anything about Jolt's verifier.** `AllConstraints` checks every constraint equation directly on the whole witness. Jolt's verifier instead runs sumchecks, reductions and a polynomial commitment scheme, which jolt-qed has not verified (see the [README](../README.md)). "Accepted" in `sail_soundness` means "has a witness that satisfies the modelled constraints".
- **They are one-directional.** Every honest Jolt run up to its first explicit halt is reproduced by Sail. The converse is not claimed: a Sail run need not correspond to a Jolt run, and the theorems say nothing about programs whose runs Jolt's tracer aborts.
- **They stop at the first explicit halt.** Jolt ends a run at a `jolt.success` row (success) or at EBREAK (panic). The RISC-V reading of EBREAK as a halt is entering debug mode, which the Sail model does not implement, and `jolt.success` is one of Jolt's own instructions, which Sail does not have. The theorems stop in front of the first halt row without executing it ([`riscv-alignment.md`](riscv-alignment.md) section 4). They say nothing about later instructions.
- **They do not cover Jolt's own instructions**, the inline opcodes `0x0B` and `0x2B`, or the advice tape (see the scope premise above).
- **They describe particular Jolt revisions.** The halt rows, the shared memory and the constraints follow a16z/jolt `ff6fc6568`. The ELF loader (`decode_elf`, in `JoltConstraints/theorems/WholeRun/Elf.lean`) follows `ff6fc6568` too. The system expansions other than EBREAK and the compressed decoder (`joltUncompress`) still transcribe `c336a6da7`, the head of a16z/jolt#2384; #2383 and #2384 have since merged into Jolt `main`, and `crates/jolt-riscv/src/uncompress.rs` is the same at both commits.
- **They compare outputs only up to trailing zero bytes**, as `JoltInstance.soundness` does.
- **They describe one hart configuration.** The Sail model is configured as an RV64IMAC hart with only M-mode and no interrupts, with Jolt's memory map ([`riscv-alignment.md`](riscv-alignment.md) sections 1 and 2). They say nothing about other configurations.

## What the theorems trust

- **The Sail model is the specification.** `LeanRV64D/` is generated from the model commit, compiler and patches pinned in `sail-import/PROVENANCE.toml`. The patches adapt the model's handwritten Lean support to the Lean version in use and configure the model as Jolt's hart; `PROVENANCE.toml` lists each change, including the fixes to the pinned model. `scripts/check-sail-model.sh` regenerates the model in CI and requires it to match the checked-in tree byte for byte.
- **Five generated declarations raise a Lean limit.** Three CSR if-chains and the two decoder mappings in the closure of the theorems carry declaration-local `maxRecDepth` options between 550 and 1450, and one of them a `maxHeartbeats` of 250000 ([`riscv-alignment.md`](riscv-alignment.md) section 8). No proof in `JoltBytecode/` or `JoltConstraints/` sets a limit.
- **The Lean models of Jolt are faithful.** Applying the theorems to Jolt itself requires trusting that the Lean definitions of its tracer, expansions, decoder, ELF loader and constraints match the cited Jolt revisions, and that the sections given to `DecodedFrom` are what the `object` crate parses from the guest ELF. The theorems do not prove that correspondence. The differential test in [`scripts/difftest/`](../scripts/difftest/) (jolt-qed#40) runs real binaries on the Sail emulator and on Jolt's tracer and compares the results; that is evidence for the correspondence, not a proof of it.
- **The Sail compiler preserves the model's meaning.** The CI check shows that the generated files are reproducible, not that the compiler translates the Sail model correctly.
- **Lean's kernel checks the proofs using three standard axioms.** Nothing in the closure of the theorems uses `sorry`, `native_decide`, `bv_decide` or `decide +kernel`.
