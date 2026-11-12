# Does the soundness statement say what Jolt does?

Date: 2026-10-29.
Jolt commit checked: `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`, read with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 5def437f:<path>`.
Lean commit checked: `7096dcaeb62e4a49d259b511dce76c3bc77bae5f` (`main`).
Scope: the statement of `JoltInstance.soundness` (`JoltConstraints/Soundness/soundness.lean`), not its proof and not its assumptions.
Completeness is not covered here.

## The question

The theorem says: if a witness satisfies `AllConstraints`, the instance is in `JoltInstance.InLanguage`.
For the statement to mean what Jolt promises, two things must hold.
The hypothesis `AllConstraints` must be what Jolt's verifier checks.
The conclusion `InLanguage` must be what a Jolt proof claims: Jolt's tracer, run on the program and some private inputs, stops with the claimed outputs and panic flag.
Every Markdown document in the repository was treated as stale; only code was used as evidence.

## How it was checked

Claude read the top-level statement and compared it with the entry points of Jolt's verifier, prover, tracer and SDK.
Three read-only subagents compared, line by line:
- the 62 equations, the per-instruction flag tables and the 55 lookup tables with Jolt's base verifier;
- `JoltISA.execInstr` and the initial state with Jolt's tracer;
- the expansions and preprocessing with Jolt's expander and preprocessing.

Claude then rechecked against the code findings 1 and 2, the ANDN decoder gap, and the eight division advice formulas.
Items marked "(subagent)" rest on a subagent's reading only.

## Answer in brief

The statement matches Jolt almost everywhere.
The exception is serious: the hypothesis assumes every untrusted-advice word is a 64-bit value, Jolt's verifier does not check this, and the gap appears to allow a false claim (finding 1).
Four smaller differences change what the conclusion means without affecting the proof (findings 2 to 5).

## Findings

### 1. Untrusted-advice words: Lean requires 64-bit values, Jolt's verifier accepts any field element

Lean's private inputs hold untrusted advice as bytes: `JoltPrivateInputs.untrusted_advice : Array (BitVec 8)` (`JoltConstraints/program.lean`).
`TraceWitness.initialRamWordFromState` (`JoltConstraints/witness_helpers/ram_state.lean`) packs them into 64-bit words, and `ConstraintContext.initialized` (`JoltConstraints/constraint_context.lean`) makes those words the initial RAM used by constraints (37) and (38).

Jolt's verifier does not see words.
In stage 4 it splits the initial RAM into a public part and advice contributions: `public_initial_ram_evaluation` covers the program image and inputs, and `ram_val_check_init_structure` adds one contribution per present advice commitment (`crates/jolt-verifier/src/stages/stage4/verify.rs`; `RamValCheckInitContribution::untrusted`, `crates/jolt-claims/src/protocols/jolt/geometry/ram.rs`).
The untrusted contribution is an opening of a polynomial the prover commits to.
The advice claim reduction (`crates/jolt-claims/src/protocols/jolt/relations/claim_reductions/advice/`) only moves that opening to the commitment's opening point.
No relation under `crates/jolt-claims/src/protocols/jolt/relations/` constrains the polynomial's entries, and the advice region lies below the public I/O mask, so its final value is not checked either.
So a cheating prover may commit any field elements as untrusted-advice words.

The following example satisfies the per-cycle equations; it has not been built or run.
1. The prover commits the untrusted-advice word `2^64`, a field element that is not a 64-bit value.
2. The guest runs `ld x5, 0(a0)` with `a0` pointing at that word.
   LD has no lookup (`crates/jolt-riscv/src/instructions/i/ld.rs`: circuit flags `[Load]`), and constraint (04) copies the read value into the destination, so `x5` holds `2^64`.
3. The guest runs `mulhu x7, x5, x6` with `x6 = 2`.
   MULHU sets `MultiplyOperands` (`crates/jolt-riscv/src/instructions/m/mulhu.rs`), so constraints (10) and (20) make the lookup index the field product `2^65`, which is a valid 128-bit index.
   Its table is `UpperWord` (`crates/jolt-lookup-tables/src/instructions/riscv/mulhu.rs`), whose entry is `index >> 64` (`crates/jolt-lookup-tables/src/tables/upper_word.rs`), so `x7 = 2`.
4. The guest stores `x7` to the output and exits normally.

For every 64-bit `a`, `mulhu(a, 2)` is 0 or 1, so no choice of advice bytes makes Jolt's tracer output 2.
If this reproduces against Jolt's prover and verifier, it is a soundness bug in Jolt.
Status: found by reading the code; no satisfying witness has been constructed and nothing has been run.

Effect on the Lean statement: the hypothesis is stronger than what Jolt's verifier checks, so the theorem says nothing about such proofs.
Modeling advice words as field elements changes a core definition and needs Ari's decision.
Trusted advice has the same representation gap; there the verifier's caller supplies the commitment, which the trust model covers.

Update, 2026-11-12: closed in the model.
`AllConstraints` now takes the untrusted-advice words as field elements, and `JoltInstance.soundness` is proved for that relation (`reports/2026-11-12-witness-column-typing.md`).
At Jolt `a6b6dc717`, LD sets `RightOperandIsRdWriteValue` (`crates/jolt-riscv/src/instructions/i/ld.rs`), so its loaded value is range-checked and step 2 of the example fails.

### 2. END cycle marker: Lean skips a memory read that Jolt's tracer performs

Jolt's tracer reads the label for both events of the cycle-marker host call: `Cpu::handle_jolt_cycle_marker` (`tracer/src/emulator/cpu.rs`) calls `self.read_string(ptr, len)?` for `JOLT_CYCLE_MARKER_START` and for `JOLT_CYCLE_MARKER_END`, and `read_string` loads each byte through `mmu.load`.
Lean's `execHostIOWith` (`JoltBytecode/JoltISA/HostIO.lean`) reads the bytes for event 1 and reads nothing for event 2.
If the label pointer is an address the tracer's memory unit rejects, Jolt's tracer aborts while Lean retires the row (subagent's example: `x11 = 0xFFFFFF00` in live mode).
So `InLanguage` contains runs Jolt's tracer cannot produce.
`HostCallsSucceed` does not exclude them, because it is stated over Lean's execution.
Real guests pass valid labels.
The fix is in Lean: read the label for event 2 as for event 1.
The docstring of `execHostIOWith`, which says the memory reads are retained, is false for END.

### 3. The run's initial RAM comes from different ELF sections than Jolt's tracer uses

Lean's `initialRam` (`JoltConstraints/program.lean`) writes `memory_init`, which `decode_elf` (`crates/jolt-program/src/image/elf.rs`) builds from every section at or above `RAM_START_ADDRESS` with file data.
Jolt's tracer copies only sections of type PROGBITS, INIT_ARRAY, FINI_ARRAY and PREINIT_ARRAY with a nonzero file offset (`Emulator::setup_program`, `tracer/src/emulator/mod.rs`).
Jolt's verifier uses `memory_init` (`RAMPreprocessing::preprocess`, `crates/jolt-program/src/preprocess/ram.rs`).
For an ELF with another kind of section holding data above `RAM_START_ADDRESS`, such as an allocated note, the verifier's initial RAM has those bytes and Jolt's tracer has zeros.
A guest that reads them could then get a proof of an output Jolt's tracer does not produce.
This is a16z/jolt#1951 item 5.
Jolt's guest linker script (`src/linker.ld.template`) places no such section; sections the toolchain adds on its own were not checked.

### 4. ELFs that define `tohost` get a different RAM size in Jolt's tracer

If the ELF defines the symbol `tohost`, `Emulator::setup_program` sizes RAM to `TEST_MEMORY_CAPACITY` instead of the layout's total memory size (subagent).
Lean always uses the layout size.
Only ELFs that define that symbol are affected.

### 5. `InLanguage` does not mention the termination word

Jolt's verifier requires the final termination word to be 1 for a "no panic" claim and 0 for a "panicked" claim (`PublicIoMemory::new`, `crates/jolt-program/src/preprocess/public_io.rs`, checked by constraint (26)).
`Trace.matches_outputs` (`JoltConstraints/honest_trace.lean`) compares only the outputs and the panic flag.
So the theorem is true but says less than Jolt's verifier enforces.

## Differences with no effect on the theorem

Lean's source type can describe images Jolt's decoder never produces; these only add instances to the theorem.
- ANDN as a source instruction: `decode_op` (`crates/jolt-program/src/image/decode.rs`) has no case for it.
- Odd branch and jump offsets: Jolt's B and J formats clear bit 0.
- A quotient field on the division instructions, which lands in the `VirtualAdvice` row's value; the row metadata reads only its immediate (`JoltConstraints/metadata.lean`), and execution replaces the value.
- Instruction lists not tied to the text bytes, in any order, overlapping, or marked compressed when no compressed form exists (subagent).

Jolt accepts the inline instructions (opcodes `0x0B`, `0x2B`), which `SourceInstruction` leaves out by design.
Jolt's PC-map allocation (`BytecodePCMapper::try_new`) crashes for code at very high addresses, which `pc_map_ok` accepts; no proof exists there (subagent).

These semantic differences cannot be reached from any expansion Jolt produces (subagent):
- word shifts by 32 or more;
- LD immediates wider than 32 bits, which Jolt's tracer truncates;
- advice-load widths other than 1, 2, 4 or 8;
- odd branch targets, which Sail's `jump_to` rejects and Jolt's tracer accepts;
- signed-overflow panics in Jolt builds with overflow checks;
- virtual registers below 32.

## What matches

The hypothesis:
- Verifier input checks: layout equality, `lowest > 8`, input and output sizes before outputs are trimmed, trace length (a power of two, at least 256, at most the maximum), RAM size bounds and chunk-width checks (`validate_inputs`, `validate_trace_length`, `validate_ram_remap_base` in `crates/jolt-verifier/src/verifier.rs`; `JoltFormulaDimensions::try_from`).
- `MemoryLayout.new` matches `MemoryLayout::try_new` (`common/src/jolt_device.rs`) field by field.
- The initial RAM: program image words, then trusted advice, untrusted advice and inputs at their layout addresses (`PublicInitialRam::new`).
- All 62 equations, coefficient by coefficient, with no Lean equation that Jolt's base verifier lacks; the relations Jolt has beyond them only move claims between points (subagent).
- The circuit flags, instruction flags, lookup table and RAF flag of all 88 `JoltISA.Instr` constructors (subagent).
- All 55 lookup tables, including the operand interleaving convention (subagent).
- The public I/O words of constraint (26): inputs, outputs, the panic word, and the termination word, 1 exactly when not panicked (subagent).

The conclusion:
- The stop rule matches PR #2109's rule in `Cpu::tick`.
  The tracer's other stop, a tick that records no rows, cannot happen for Jolt guests: instruction fetch never faults in machine mode, and a decode failure panics.
- Jolt's tracer expands instructions with the same `jolt_program::expand::expand_instruction` that preprocessing uses (`Instruction::inline_sequence`, `tracer/src/instruction/mod.rs`).
- `SourceInstruction.honestTracerAdvice` matches the tracer's `trace` methods for DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW and REMUW, including division by zero and signed overflow; no other tracer instruction in scope supplies runtime advice.
- `Trace.prover_config` matches `ProverConfig::derive_from_dimensions` (`crates/jolt-prover/src/config.rs`), including its off-by-one RAM rounding.
- `program_size` comes from the image, as in `crates/jolt-host/src/program.rs`; the claimed outputs are the tracer's final device, as in the SDK's `prove_program` (`jolt-sdk/src/host_utils.rs`).
- Every `execInstr` row type matches the tracer's `exec`: arithmetic, jumps, branches, LD and SD, device regions, panic and termination words, advice, assertions, shifts, masks and HostIO apart from finding 2 (subagent).
- The initial CPU state: registers, `misa`, privilege, `mstatus`, PC, virtual registers, RAM size, device contents, advice tape position, live HostIO mode and unchecked overflow (subagent).
- All 101 source instruction kinds expand to exactly Jolt's rows in both destination branches, with matching stamping; `pc_map_ok`, `preprocess` and `get_first_pc` match Jolt's preprocessing (subagent).

## Not checked

- Whether real guest ELFs contain sections that trigger finding 3.
- `RAMPreprocessing` allocation limits.
- That Lean's constructor operands map to Jolt's `rs1` and `rs2` in order (the tracer subagent assumed it; the constraints subagent checked operand presence only).
- The flags of `VirtualPow2I`, `VirtualPow2IW` and `VirtualShiftRightBitmaskI` against an emission site: none exists at this commit.
- Akita, field-inline, zero-knowledge and committed-program modes, and the PCS.

## Documentation drift found

- `JoltBytecode/JoltISA/ExpansionsAutomated.lean` says it is generated by `jolt-lean-gen`; the generator at this commit cannot produce it. Its rows were compared by hand and match.
- Some Lean comments cite the unpinned fork `abiswas3/jolt/tree/main`, older pins, or the crate `jolt-trace`, which does not exist at this commit.
- `metadata.lean` has TODOs asking for checks this audit made.
