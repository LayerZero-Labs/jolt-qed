# Plain steps and division layout: branch-alignment audit

## Result: stopped at the Part 1 alignment check

Read `AGENTS.md`, `methods/layer6/reuse.md`, Part A of `methods/layer6/stage-4a-report.md`, `methods/layer6/stage-6b-report.md`, and `methods/layer6/plain-steps-and-layout.md` before implementation.
The audit snapshot is on `feat/soundness`, at HEAD `f0907c3`, with other agents' working-tree changes present.
The plan explicitly requires stopping if a canonical expanded branch can fail Sail's target-alignment check.
That case exists in the current model and is confirmed by Lean proofs below.

No branch or VirtualAdviceLoad step was staged or proved.
Part 2 was not undertaken after this blocker, and its remaining claims have not received a complete audit in this task.
`JoltInstance.division_expansion_layout` at `JoltConstraints/Soundness/Layer6/DivisionDefs.lean:109` retains its original statement and existing `sorry`.
No Lean source file was edited.

## Exact counterexample

| Item | Value |
| --- | --- |
| Source | `.riscv (.BEQ (.Regidx 0) (.Regidx 0) (1#13))` |
| Source address and entry address | `0x80000000` |
| Compression | `false` |
| Image instructions | This one source row |
| Image memory initialization | `[(0x80000000, 0)]` |
| Program end | `0x80000004` |
| Expanded instruction | `.BEQ (.xreg (.Regidx 0)) (.xreg (.Regidx 0)) (1#128)` |
| Expanded countdown and first-in-sequence flag | `none`, `false`; consequently `starts_source = true` |
| Prepared PC and nextPC | `0x80000000`, `0x80000004` |
| Both operands | `x0 = 0`, so the branch is taken |
| Taken target | `0x80000001`, whose bit 0 is one |
| Execution result | `.error (.Assertion "extensions/I/base_insts.sail:59.25-59.26") pre` |

The image expands successfully and its bytecode passes `preprocess`.
Its row is canonical and satisfies `JoltInstructionRow.Valid`, including `BranchOffsetOk`.
The image also satisfies `NextPCNoWrap` and `ImageNonempty`.
The execution failure holds for every tape answer and every state prepared at this source address.
In particular, the checked `initializedFailure` theorem starts with `init_state`, applies `advance_pc`, proves `AllRegistersPresent`, and proves the exact error result.
The failure therefore persists with all Sail registers present and the PC prepared correctly.
It occurs at the bit-0 assertion before any compressed-extension configuration check.

This refutes the expansion/canonicality-only alignment claim requested by the plan.
No witness satisfying the full `ConstraintEquations` bundle was constructed, so this report does not claim a counterexample to `JoltInstance.soundness` or establish that every possible selected-row branch statement is false.
The explicit alignment gate in Part 1 is sufficient to require stopping here.

## Cause and pinned-tracer comparison

`RiscvInstruction.BEQ` at `JoltBytecode/RiscvInstruction.lean:146` accepts an arbitrary `BitVec 13`, including one.
`JoltISA.Encoded.BEQ` at `JoltBytecode/JoltISA/Instruction.lean:208` sign-extends that value without clearing bit 0.
`SourceInstruction.expand` at `JoltConstraints/expansions.lean:23` emits that encoded branch as a native row.
`ExpansionFacts.BranchOffsetOk` at `JoltConstraints/expansion_facts.lean:589` requires only a sign-extended 13-bit value; it imposes no evenness condition.
`Rv64ProgramImage` at `JoltConstraints/program.lean:186` carries no certificate connecting its instruction values to an actual decoder output.
`bytecode_address_ok`, `pc_map_ok`, and `preprocess` at `JoltConstraints/program.lean:246`, `:256`, and `:267` check source addresses and row layout, without requiring an even branch offset.

The BEQ case of `JoltISA.execInstr` at `JoltBytecode/JoltISA/Semantics.lean:104` invokes Sail's `jump_to` on `PC + imm.setWidth 64`.
`execWithTapeAnswer` at `JoltConstraints/Soundness/Layer5/TapeSemantics.lean:21` uses this same execution rule for branches.
Sail's `jump_to` at `LeanRV64D/BaseInsts.lean:244` asserts that the target's low bit is zero at line 248.
`Projection.jump_to_of_aligned` at `JoltBytecode/InstructionEquivalence/ProofSupport/Projection.lean:353` requires the missing alignment fact; it cannot establish it for this target.

The following Jolt sources were read at pin `5def437f` with `git show` from `/Users/ari.biswas/Work-with-A16z/jolt`.
Repository-relative paths omit the leading `jolt/` used in the project's citations.

- `jolt/tracer/src/instruction/format/format_b.rs`, `FormatB::parse`, assembles a signed branch immediate with bit 0 zero.
  The source instruction above is permitted by the Lean source type but is not the result of that parser.
- `jolt/crates/jolt-program/src/image/decode.rs`, `decode_instruction`, dispatches branch opcodes through the source-instruction decoder.
- `jolt/tracer/src/instruction/beq.rs`, `BEQ::exec`, assigns the taken target directly to `cpu.pc` and has no Sail target-alignment assertion.

The missing fact is that a taken branch target satisfies Sail's alignment requirements.
Expansion and preprocessing alone do not supply even the required bit-0 condition.
Before resuming, the model needs review: one possible correction is to express branch execution using Jolt's direct PC assignment, as the current JAL/JALR interpreter cases do.
Retaining Sail's checked jump would instead require a justified decoder-parity fact and the relevant state-alignment conditions.
These alternatives affect approved definitions or proof interfaces and are outside this task's permitted implementation changes.
No correction, extra premise, restriction, or definition change was made.

## Checked reproduction

The following complete diagnostic module is also saved at `/private/tmp/plain-steps-branch-counterexample.lean`.
It is included here so the evidence survives cleanup of temporary files.
It proves expansion, preprocessing acceptance, canonicality, row validity, the two image conditions, and the exact execution failure.

```lean
import JoltConstraints.trace_interface
import JoltConstraints.Soundness.Layer5.TapeSemantics

open Sail PreSail LeanRV64D.Functions JoltISA
open JoltConstraints.Soundness

namespace BranchAlignmentCounterexample

def source : SourceInstructionRow SourceInstruction :=
  { address := 0x80000000
    instruction := .riscv (.BEQ (.Regidx 0) (.Regidx 0) 1)
    is_compressed := false }

def row : JoltInstructionRow :=
  { address := 0x80000000
    instruction := .BEQ (.xreg (.Regidx 0)) (.xreg (.Regidx 0)) 1
    virtual_sequence_remaining := none
    is_first_in_sequence := false
    is_compressed := false }

def image : Rv64ProgramImage SourceInstruction :=
  { instructions := #[source]
    memory_init := [(0x80000000, 0)]
    program_end := 0x80000004
    entry_address := 0x80000000
    program_end_ge_ram_start := by decide
    memory_init_in_program := by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      decide }

theorem expanded : expand_program image = some #[row] := rfl

theorem preprocessed : ∃ slots, preprocess #[row] = some slots := by
  have accepted : pc_map_ok #[row] = true := by decide
  unfold preprocess
  rw [accepted]
  exact ⟨_, rfl⟩

theorem canonical : JoltRegisterEncoding.instructionIsCanonical row.instruction = true := rfl

theorem offsetAllowed : ExpansionFacts.BranchOffsetOk row.instruction :=
  ⟨1#13, rfl⟩

theorem rowValid : row.Valid :=
  (expand_program_rows_valid image #[row] expanded).rowValid ⟨0, by decide⟩

theorem noWrap : image.NextPCNoWrap := by
  intro r member
  simp only [image, Array.mem_singleton] at member
  subst r
  decide

theorem imageNonempty : image.ImageNonempty := by
  simp [Rv64ProgramImage.ImageNonempty, image]

theorem fails (pre : SailJoltState)
    (pc : pre.sail.regs.get? Register.PC = some 0x80000000)
    (answer : BitVec 64) :
    execWithTapeAnswer row.instruction answer pre =
      .error (.Assertion "extensions/I/base_insts.sail:59.25-59.26") pre := by
  have zero : readSrc (.xreg (.Regidx 0)) pre = .ok 0 pre := rfl
  have readPC : liftSail (Sail.readReg Register.PC) pre = .ok 0x80000000 pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail 0x80000000 pc]
  simp only [row, execWithTapeAnswer, execInstr, bind, EStateM.bind, zero,
    branchDecisionPure, beq_self_eq_true, if_true, readPC]
  rfl

theorem preparedFailure (state : SailJoltState) (answer : BitVec 64) :
    execWithTapeAnswer row.instruction answer (advance_pc source.address false state) =
      .error (.Assertion "extensions/I/base_insts.sail:59.25-59.26")
        (advance_pc source.address false state) := by
  apply fails
  simp [advance_pc, source, Std.ExtDHashMap.get?_insert]

theorem initializedFailure (ram : Array (BitVec 8)) (device : JoltDevice)
    (tape : JoltAdviceTape) (answer : BitVec 64) :
    let pre := advance_pc source.address false
      (init_state source.address ram device tape {})
    AllRegistersPresent pre.sail ∧
      execWithTapeAnswer row.instruction answer pre =
        .error (.Assertion "extensions/I/base_insts.sail:59.25-59.26") pre := by
  exact ⟨advance_pc_keeps_registers _ _ _
    (init_state_registers_present _ _ _ _ _), preparedFailure _ _⟩

#print axioms expanded
#print axioms preprocessed
#print axioms canonical
#print axioms offsetAllowed
#print axioms rowValid
#print axioms noWrap
#print axioms imageNonempty
#print axioms fails
#print axioms preparedFailure
#print axioms initializedFailure

end BranchAlignmentCounterexample
```

## Validation, declarations, and scope

`lake env lean /private/tmp/plain-steps-branch-counterexample.lean` passed.
Its log is `/private/tmp/plain-steps-branch-counterexample.log`.
All ten diagnostic theorems printed in the module have axiom sets contained in `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
None reaches `sorryAx` or a native bit-vector axiom.

`lake build JoltConstraints` passed with 8,818 jobs against the concurrent working tree.
The build log is `/private/tmp/plain-steps-and-layout-build.log`.
`git diff --check` passed before writing this report.

The separate axiom audit `/private/tmp/plain-steps-and-layout-axioms.lean` passed, with output in `/private/tmp/plain-steps-and-layout-axioms.log`.
`#print axioms JoltInstance.division_expansion_layout` reported `[propext, sorryAx, Quot.sound]`.
`#print axioms JoltInstance.division_block`, declared at `JoltConstraints/Soundness/Layer6/DivisionBlock.lean:76`, reported `[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`.
The existing division-layout gap was left in place because the plan requires stopping at the earlier branch failure.
The two requested new steps do not exist, so there are no step declarations to audit.

There are no new or changed repository Lean declarations, no visibility changes, no added hypotheses, and no new staged gaps.
There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, and no proof limits were raised.
No repository proof was added for which a timing report is needed.
The diagnostic proofs use direct reductions and existing lemmas, with no instruction-set case split or copied family proof.
Only this report was added to the repository by this task.
Other agents' files and edits were preserved.
No commit was made.
Work stops after this report.
