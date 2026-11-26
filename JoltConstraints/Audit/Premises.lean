import JoltConstraints.theorems.WholeRun.Top
import JoltConstraints.theorems.Completeness.completeness
import JoltConstraints.Audit.Commands

/-!
# The premises of the headline theorems, checked by the build

`assumptions.toml` at the repository root lists every premise of the headline theorems, every
`sorry`, every field of `Rv64ProgramImage` and the scope premises, each with the Jolt functions it
depends on and either a necessity witness (`JoltConstraints/Audit/Necessity.lean`) or the reason
it has none. `reports/2026-11-25-stale-assumptions.md` explains why: a premise that Jolt stops
needing must be found and removed, not left behind.

This file makes the build fail when the premises change. `#expect_binders T "x : A" …` checks
that the binders of the theorem `T` are exactly the listed ones, in order, each printed as
`name : type` on one line. `#expect_fields S "f : A" …` does the same for the fields of the
structure `S`. On a mismatch the error prints the actual list. The commands are defined in
`JoltConstraints/Audit/Commands.lean`. `JoltConstraints/Audit/Statements.lean` checks the full
statements and the definitions behind them.

When a binder or field is added, removed or changed:

1. run `scripts/update-audit-tables.py`, which rewrites the lists here and the statement table
   in `JoltConstraints/Audit/Statements.lean` from the build;
2. update `assumptions.toml` (`appears_in`), adding or removing the registry entry;
3. run `scripts/check-assumptions.py`, which checks that the two agree.

A premise that a new Jolt check makes provable should be removed, not kept; its necessity witness
stops building when that happens.
-/

/-! ## The headline theorems

`JoltInstance.soundness` and `JoltInstance.completeness` (with its existential form) are the
constraint-level theorems; `HonestTrace.sail_reproduces` and `JoltInstance.sail_soundness` are the
whole-run theorems of `docs/whole-run-theorem.md`. -/

#expect_binders JoltInstance.soundness
  "F : Type"
  "inst : Field F"
  "joltField : JoltField F"
  "joltInstance : JoltInstance SourceInstruction"
  "params : WitnessParams"
  "privateInputs : JoltPrivateInputs"
  "witness : WitnessType F params"
  "satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness"

#expect_binders JoltInstance.completeness
  "F : Type"
  "inst : Field F"
  "joltInstance : JoltInstance SourceInstruction"
  "privateInputs : JoltPrivateInputs"
  "trace : HonestTrace joltInstance privateInputs"
  "claimsRunOutputs : Trace.matches_outputs joltInstance trace.toTrace"
  "spoilAssertsPass : trace.SpoilAssertsPass"
  "config : ProverConfig"
  "proverAccepts : Trace.prover_config joltInstance trace.toTrace = some config"
  "setupSized : joltInstance.max_padded_trace_length.toNat ≤ 2 ^ 63"

#expect_binders JoltInstance.completeness_someWitness
  "F : Type"
  "inst : Field F"
  "joltInstance : JoltInstance SourceInstruction"
  "inLanguage : joltInstance.InLanguage"
  "setupSized : joltInstance.max_padded_trace_length.toNat ≤ 2 ^ 63"

#expect_binders WholeRun.HonestTrace.sail_reproduces
  "joltInstance : JoltInstance SourceInstruction"
  "privateInputs : JoltPrivateInputs"
  "trace : HonestTrace joltInstance privateInputs"
  "elf : WholeRun.ElfSections"
  "hdecoded : joltInstance.program.DecodedFrom elf"
  "pre : List WholeRun.Block"
  "halt : SailJoltState"
  "final : SailJoltState"
  "hp : WholeRun.HaltPrefix trace pre halt final"
  "hconf : ∀ b ∈ pre, WholeRun.BlockConforms joltInstance.program b"

#expect_binders JoltInstance.sail_soundness
  "F : Type"
  "inst : Field F"
  "joltField : JoltField F"
  "joltInstance : JoltInstance SourceInstruction"
  "params : WitnessParams"
  "givenInputs : JoltPrivateInputs"
  "witness : WitnessType F params"
  "satisfied : JoltConstraints.AllConstraints joltInstance givenInputs witness"
  "elf : WholeRun.ElfSections"
  "hdecoded : joltInstance.program.DecodedFrom elf"

/-! ## Structures that carry premises

A premise can also hide in a field: `BlockConforms` is a premise of the whole-run theorems, and
each proof field of `Rv64ProgramImage` is a fact every instance must carry. -/

#expect_fields WholeRun.BlockConforms
  "riscv : ∃ i, b.row.instruction = SourceInstruction.riscv i"

#expect_fields Rv64ProgramImage
  "instructions : Array (SourceInstructionRow Source)"
  "memory_init : List (BitVec 64 × BitVec 8)"
  "program_end : BitVec 64"
  "entry_address : BitVec 64"
  "program_end_ge_ram_start : JoltISA.RAM_START_ADDRESS ≤ self.program_end.toNat"
  "memory_init_in_program : ∀ entry ∈ self.memory_init, JoltISA.RAM_START_ADDRESS ≤ entry.1.toNat ∧ entry.1.toNat < self.program_end.toNat"
  "next_pc_no_wrap : ∀ row ∈ self.instructions, (row.address.toNat + if row.is_compressed = true then 2 else 4) < 2 ^ 64"
  "instruction_loaded : ∀ row ∈ self.instructions, ∃ entry ∈ self.memory_init, row.address.toNat ≤ entry.1.toNat ∧ entry.1.toNat < row.address.toNat + 2"
