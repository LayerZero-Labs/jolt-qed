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


## Follow-up to the corrected plan at `4e546a3`: compressed-state invariant staged

Re-read `AGENTS.md`, `reuse.md`, and the corrected plan, including the witness-derived branch-alignment item.
The witness argument addresses the odd-target issue from the first audit: it supplies a real successor and an even target.
This follow-up does not request any change to the source model, the language, or branch semantics.

The remaining execution-state issue is distinct: Sail also checks target bit 1 when compressed instructions are disabled.
An even target alone therefore does not establish successful `jump_to` execution from an arbitrary state satisfying `RegisterAgreementOn`.
That agreement records register presence and the live architectural/virtual values, without fixing Sail's `misa.C` configuration.
The plan's witness argument does not establish that state configuration.
The missing run invariant has been staged as required by the plan's instruction to stage a nontrivial unnamed fact and stop.
Neither selected-row step nor Part 2 has been completed.

### Checked case with an even real successor

The diagnostic module below proves the following facts.

| Item | Value or checked fact |
| --- | --- |
| Branch source | `BEQ x0, x0, +6` at `0x80000000`, uncompressed |
| Skipped source | Canonical no-op at `0x80000004`, compressed |
| Successor source | FENCE at `0x80000006`, uncompressed |
| Expansion | `expand_program image = some bytecode` |
| Preprocessing | `pc_map_ok bytecode = true` and `preprocess bytecode = some slots` for some slots |
| Branch row | Canonical and `JoltInstructionRow.Valid` |
| Target | `0x80000006`, equal to the successor row's address and accepted by `bytecode_address_ok` |
| Pre-state | PC prepared at `0x80000000`, nextPC prepared at `0x80000004`, then Sail `misa` replaced by zero |
| Presence | Every Sail register remains present whenever every register was present before preparation |
| Live agreement | `RegisterAgreementOn (fun register => register = 0)` for any witness with `RegistersVal 0 t = 0` |
| Operands | Both source registers are x0 and are live; both read zero |
| Compressed configuration | `currentlyEnabled Ext_Zca pre.sail = .ok false pre.sail` |
| Execution | `.ok (Memory_Exception (Virtaddr 0x80000006, E_Fetch_Addr_Align ())) pre` |

The execution result is not `RETIRE_SUCCESS`.
It holds for every tape answer.
The register-presence premise can be instantiated with `init_state_registers_present`; the alteration of `misa` is the part that lacks a run certificate.
The live set deliberately contains only x0, which is sufficient for both branch operands and is allowed by the proposed general live-register interface.
The checked result isolates the missing state premise even when an accepted successor supplies the exact even target.

No witness satisfying all `ConstraintEquations` was constructed for this diagnostic, and no initialized run reaching the altered `misa` state was claimed.
This is not a counterexample to the witness's exclusion of odd targets, to the newly staged run invariant, or to `JoltInstance.soundness`.
It shows why the witness-derived evenness result needs a run-derived compressed-state fact before it yields the requested successful branch step.

### Code audit and required proof

`RegisterAgreementOn` at `JoltConstraints/Soundness/Layer5/Registers.lean:34` has only `present` and `values` fields.
Its values refer to architectural integer registers and Jolt virtual registers, not Sail's `misa` register.
`jump_to` at `LeanRV64D/BaseInsts.lean:244` checks target bit 0 at line 248 and checks bit 1 against `currentlyEnabled Ext_Zca` at lines 249–250.
`currentlyEnabled` reads `misa.C` in the `Ext_C` case at `LeanRV64D/Types.lean:672`, which the `Ext_Zca` case at line 673 uses.
`Projection.jump_to_of_aligned` requires an actual `align_pc` equality and does not turn evenness alone into that equality.

The two proposed witness lemmas were checked in place.
`terminal_real_successor_address` at `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:279` currently returns the successor address and its RAM lower bound; its proof obtains the full `bytecode_address_ok` fact and discards the evenness component.
Generalizing that conclusion can expose evenness as the corrected plan allows.
`terminal_branch_real_target` at the same file's line 335 identifies the successor with the wrapped branch target from the field equation and the 13-bit offset bound.
Neither lemma has an execution-state parameter or a conclusion about `misa`.
No visibility or statement change to these lemmas was made before stopping.

`initialRegisterValue` at `JoltConstraints/program.lean:42` initializes `misa` to `0x800000008014312f`, whose C bit is set.
The pinned Jolt tracer's `Cpu::new` in `jolt/tracer/src/emulator/cpu.rs` writes the same constant to `CSR_MISA_ADDRESS`.
The pinned `BEQ::exec` in `jolt/tracer/src/instruction/beq.rs` assigns `cpu.pc` directly on a taken branch.
Both items were read with `git show 5def437f:<path>` from the local Jolt checkout.

The needed new proof is that successful relaxed execution preserves the compressed configuration from initialization through the final state of a run.
PC preparation then leaves that configuration unchanged for the next attempted row.
I found register-presence, source-value, and device/tape frame lemmas, but no existing run-level `misa` or enabled-compressed invariant.
`InstructionFrame.Rules.sail` permits arbitrary Sail-state replacement, so the existing device-oriented rule cannot directly preserve a Sail register value.
Proving the new invariant requires an appropriate instruction frame and run induction; it is not discharged by either of the two named witness-target lemmas.
A continuation should share or generalize the existing frame arguments rather than duplicate the instruction dispatch proof.
The branch step should obtain this state fact from the actual prefix and its entry linkage, without adding a new soundness assumption.

### New declaration and remaining work

| Declaration or change | Location | Status |
| --- | --- | --- |
| `JoltConstraints.Soundness.UntrustedAnswerRun.final_compressed_enabled` | `JoltConstraints/Soundness/Layer5/Branch.lean:24` | New named staged lemma; one `sorry` |
| Import of the new module | `JoltConstraints.lean:62` | Added so the aggregate target checks the staged statement |

The staged statement is:

```lean
theorem UntrustedAnswerRun.final_compressed_enabled
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    currentlyEnabled extension.Ext_Zca (TraceWitness.finalTraceState run.toTrace).sail =
      .ok true (TraceWitness.finalTraceState run.toTrace).sail := by
  sorry
```

The final state is the initial state for an empty run and the last row's post-state for a nonempty run.
The statement requires the actual initialized, executing, linked relaxed run and no witness, honest-advice, or extra configuration premise.
It is staged for review, not proved or used to claim completion of the branch step.
No caller has acquired a new assumption.

After this invariant is proved, the branch work still needs the witness-target argument, preservation of the live register agreement, and the common execution proof for the six branches.
The VirtualAdviceLoad step and `division_expansion_layout` remain untouched.
The remainder of the plan has not received a complete audit after this stopping point.
No existing public statement or proved fact was changed, and no private declaration was made public.

### Diagnostic reproduction

The complete checked diagnostic is saved at `/private/tmp/plain-steps-branch-zca-counterexample.lean` and reproduced here for persistence.
It introduces no repository declaration.

```lean
import JoltConstraints.trace_interface
import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer5.TapeSemantics

open Sail PreSail LeanRV64D.Functions JoltISA
open JoltConstraints.Soundness

namespace BranchZcaCounterexample

def source : SourceInstructionRow SourceInstruction :=
  { address := 0x80000000
    instruction := .riscv (.BEQ (.Regidx 0) (.Regidx 0) 6)
    is_compressed := false }

def row : JoltInstructionRow :=
  { address := 0x80000000
    instruction := .BEQ (.xreg (.Regidx 0)) (.xreg (.Regidx 0)) 6
    virtual_sequence_remaining := none
    is_first_in_sequence := false
    is_compressed := false }

def skipped : SourceInstructionRow SourceInstruction :=
  { address := 0x80000004
    instruction := .riscv (.ADDI (.Regidx 0) (.Regidx 0) 0)
    is_compressed := true }

def successor : SourceInstructionRow SourceInstruction :=
  { address := 0x80000006
    instruction := .riscv .FENCE
    is_compressed := false }

def image : Rv64ProgramImage SourceInstruction :=
  { instructions := #[source, skipped, successor]
    memory_init := [(0x80000000, 0)]
    program_end := 0x8000000a
    entry_address := 0x80000000
    program_end_ge_ram_start := by decide
    memory_init_in_program := by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      decide }

def bytecode : Array JoltInstructionRow :=
  #[row,
    { address := skipped.address, instruction := Instr.canonicalNoOp,
      virtual_sequence_remaining := none, is_first_in_sequence := false,
      is_compressed := true },
    { address := successor.address, instruction := .FENCE,
      virtual_sequence_remaining := none, is_first_in_sequence := false,
      is_compressed := false }]

theorem expanded : expand_program image = some bytecode := rfl

theorem accepted : pc_map_ok bytecode = true := by decide

theorem preprocessed : ∃ slots, preprocess bytecode = some slots := by
  unfold preprocess
  rw [accepted]
  exact ⟨_, rfl⟩

theorem canonical : JoltRegisterEncoding.instructionIsCanonical row.instruction = true := rfl

theorem rowValid : row.Valid :=
  (expand_program_rows_valid image bytecode expanded).rowValid ⟨0, by decide⟩

theorem targetAccepted : bytecode_address_ok (0x80000006#64) = true := by decide

theorem targetIsSuccessor : bytecode[2].address = row.address + (6#128).setWidth 64 := rfl

theorem disabled (pre : SailJoltState)
    (misa : pre.sail.regs.get? Register.misa = some 0) :
    currentlyEnabled extension.Ext_Zca pre.sail = .ok false pre.sail := by
  have read := readReg_eq_of_get? Register.misa pre.sail 0 misa
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp only [bind, EStateM.bind, read, pure, EStateM.pure]
  congr 1
  simp [hartSupports, _get_Misa_C, LeanRV64D.Functions.not,
    LeanRV64D.Functions.xlen, Sail.BitVec.extractLsb]

theorem fails (pre : SailJoltState)
    (pc : pre.sail.regs.get? Register.PC = some 0x80000000)
    (misa : pre.sail.regs.get? Register.misa = some 0)
    (answer : BitVec 64) :
    execWithTapeAnswer row.instruction answer pre =
      .ok (ExecutionResult.Memory_Exception
        (virtaddr.Virtaddr 0x80000006, ExceptionType.E_Fetch_Addr_Align ())) pre := by
  have zero : readSrc (.xreg (.Regidx 0)) pre = .ok 0 pre := rfl
  have readPC : liftSail (Sail.readReg Register.PC) pre = .ok 0x80000000 pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail 0x80000000 pc]
  simp only [row, execWithTapeAnswer, execInstr, bind, EStateM.bind, zero,
    branchDecisionPure, beq_self_eq_true, if_true, readPC]
  have zca := disabled pre misa
  unfold liftSail
  have jump : jump_to (0x80000006#64) pre.sail =
      .ok (ExecutionResult.Memory_Exception
        (virtaddr.Virtaddr 0x80000006, ExceptionType.E_Fetch_Addr_Align ())) pre.sail := by
    have bit0 : BitVec.access (0x80000006#64) 0 = 0#1 := by decide
    have bit1 : bit_to_bool (BitVec.access (0x80000006#64) 1) = true := by decide
    simp [jump_to, ext_control_check_pc, SailME.run, PreSail.PreSailME.run,
      Sail.assert, PreSail.assert, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.lift, MonadLift.monadLift, monadLift, liftM,
      Functor.map, EStateM.map, bind, EStateM.bind, pure, EStateM.pure, zca,
      bit0, bit1, LeanRV64D.Functions.not]
  rw [show (0x80000000 : BitVec 64) + (6 : BitVec 128).setWidth 64 = 0x80000006#64 by decide, jump]

noncomputable def badPre (state : SailJoltState) : SailJoltState :=
  let prepared := advance_pc source.address false state
  { prepared with sail :=
    { prepared.sail with regs := prepared.sail.regs.insert Register.misa 0 } }

theorem badPre_present (state : SailJoltState) (present : AllRegistersPresent state.sail) :
    AllRegistersPresent (badPre state).sail :=
  insert_keeps_present _ _ _ (advance_pc_keeps_registers _ _ _ present)

theorem badPre_agrees {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (t : Fin params.traceLength)
    (zero : witness.RegistersVal 0 t = 0)
    (state : SailJoltState) (present : AllRegistersPresent state.sail) :
    RegisterAgreementOn (fun register => register = 0) witness t (badPre state) := by
  refine ⟨badPre_present state present, ?_⟩
  intro register live
  subst register
  change witness.RegistersVal 0 t = ((0 : Nat) : F)
  simpa using zero

theorem badPre_failure (state : SailJoltState) (answer : BitVec 64) :
    execWithTapeAnswer row.instruction answer (badPre state) =
      .ok (ExecutionResult.Memory_Exception
        (virtaddr.Virtaddr 0x80000006, ExceptionType.E_Fetch_Addr_Align ())) (badPre state) := by
  apply fails
  · simp [badPre, advance_pc, source, Std.ExtDHashMap.get?_insert]
  · simp [badPre]

#print axioms expanded
#print axioms preprocessed
#print axioms rowValid
#print axioms targetAccepted
#print axioms disabled
#print axioms fails
#print axioms badPre_agrees
#print axioms badPre_failure

end BranchZcaCounterexample
```

### Build and axiom results

`lake env lean /private/tmp/plain-steps-branch-zca-counterexample.lean` passed with no diagnostic warnings.
Its output is `/private/tmp/plain-steps-branch-zca-counterexample.log`.
The eight printed diagnostic roots have axiom sets contained in `[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`.
None reaches `sorryAx` or a native bit-vector axiom.

The final `lake build JoltConstraints` passed with 8,822 jobs after adding the staged module and its import.
The new Branch module took 4.7 seconds to build, including imports and elaboration of the staged statement.
This is not a proof-completion timing: the run invariant remains a `sorry`.
The build log is `/private/tmp/plain-steps-and-layout-staged-final-build.log`.
An earlier build caught a missing import for `TraceWitness.finalTraceState`; adding the existing `witness_helpers.ram_state` import fixed it.
Concurrent source edits made after the successful build were left to their owners.

`lake env lean /private/tmp/plain-steps-and-layout-staged-axioms.lean` passed.
The log is `/private/tmp/plain-steps-and-layout-staged-axioms.log`.
The new `UntrustedAnswerRun.final_compressed_enabled` has `[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`, as expected for the explicitly staged fact.
`JoltInstance.division_expansion_layout` at `DivisionDefs.lean:109` still has `[propext, sorryAx, Quot.sound]`.
`JoltInstance.division_block` at `DivisionBlock.lean:76` still has `[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`.
Neither requested selected-row step exists yet, so neither has an axiom result to report.

`git diff --check` passed on the owned paths before this append.
There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, no raised limits, and no completed repository proof exceeding ten seconds to report.
The one new gap is the named run invariant above; no proved fact was replaced by a gap.
This continuation changes only `JoltConstraints/Soundness/Layer5/Branch.lean`, `JoltConstraints.lean`, and this report.
Other agents' files, including their concurrent edits and commits, were not changed by this task.
No commit was made.
Work stops after this report under the corrected plan's staging rule.

## Misa invariant and branch completion; stop at the tape-width checker claim

### Completed work

The approved `UntrustedAnswerRun.final_compressed_enabled` statement is now proved without changing its hypotheses or conclusion.
The model's initialization stores `0x800000008014312f` in Sail's `misa`, and successful relaxed-answer instructions preserve that register.
PC preparation preserves it as well.
The run proof covers both an empty run and the final post-state of a nonempty run.
No instruction that writes Sail's `misa` was found; the preservation theorem covers every `Instr` constructor and every successful result.

The new `MisaFrame.lean` uses `StatePreservation.Preserves`, its bind and lift rules, and `preservation_auto`.
It supplies primitive rules for source reads, destination writes, Sail register reads, nextPC writes, jumps, doubleword memory operations, and host I/O.
There is one structural dispatch over the instruction syntax followed by those shared rules, with separate handling of the relaxed tape-load state update.
The architectural destination primitive reduces the existing `wX_update_regs` match once; it does not reprove individual instructions.
Neither `InstructionFrame.lean` nor any other JoltBytecode ProofSupport file was edited.

The pinned Jolt code was checked with `git show 5def437f:<path>`.
`jolt/tracer/src/emulator/cpu.rs` (`Cpu::new`) sets MISA to `0x800000008014312f`.
`jolt/crates/jolt-program/src/expand/control_flow/csrrw.rs` (`expand_csrrw`) lowers CSR writes to ADDI operations on the CSR virtual register.
This agrees with the successful-row preservation proof.

`branch_step` is now proved for all six branch kinds through one selected-row theorem.
It requires agreement on the live registers, liveness of both read sources, the prepared PC, and successful enabled-Zca evaluation in the pre-state.
The last premise is supplied by `UntrustedAnswerRun.final_compressed_enabled` for a continued expansion or `UntrustedAnswerRun.prepared_compressed_enabled` after fetching a new source instruction.
These are facts about the constructed execution prefix, not additional soundness assumptions.
The theorem returns successful `execWithTapeAnswer` execution and agreement on the unchanged live set at every existing next cycle.
Its execution conclusion also covers the final witness cycle.

For a taken branch, the witness determines a nonzero next unexpanded PC.
The shift equation rules out the final cycle and a padding successor.
`terminal_real_successor_address` supplies a real successor with an even address, and `terminal_branch_real_target` identifies that address with the branch's word target.
With Zca enabled, this target passes Sail's alignment check.
The untaken case preserves the whole pre-state.
The proof reuses `RegisterAgreementOn.noWrite` and `RegisterAgreementOn.setNextPC` for the register postcondition.

### Declaration inventory

Paths in the following two tables are relative to `JoltConstraints/Soundness/Layer5/`.
All declarations are in `JoltConstraints.Soundness`, and all are proved.

| Declaration | File and line | Role |
| --- | --- | --- |
| `SameMisa` (private abbreviation) | `MisaFrame.lean:20` | Equality of the optional Sail MISA values. |
| `sameMisa_trans` (private) | `MisaFrame.lean:23` | Composition of that equality. |
| `unchanged_rule` (private) | `MisaFrame.lean:26` | Lift unchanged Sail register maps to MISA preservation. |
| `read_rule` (private) | `MisaFrame.lean:33` | Source-read primitive. |
| `lift_rule` (private) | `MisaFrame.lean:37` | Lift a Sail MISA frame into Jolt state. |
| `readReg_rule` (private) | `MisaFrame.lean:43` | Sail register-read primitive. |
| `writeNextPC_rule` (private) | `MisaFrame.lean:47` | Sail nextPC-write primitive. |
| `write_rule` (private) | `MisaFrame.lean:51` | Architectural and virtual destination writes. |
| `jump_rule` (private) | `MisaFrame.lean:70` | Reuse `jump_to_shape`. |
| `load_rule` (private) | `MisaFrame.lean:78` | Doubleword load primitive. |
| `store_rule` (private) | `MisaFrame.lean:82` | Doubleword store primitive. |
| `host_rule` (private) | `MisaFrame.lean:86` | Host I/O primitive. |
| `execWithTapeAnswer_keeps_misa` | `MisaFrame.lean:93` | Frame for every successful relaxed instruction. |
| `advance_pc_misa` | `MisaFrame.lean:119` | MISA survives PC preparation. |
| `initial_state_misa` (private) | `MisaFrame.lean:124` | Initial value from successful initialization. |
| `UntrustedAnswerRun.final_misa` | `MisaFrame.lean:142` | Carry the initialized value through the run. |

| Declaration | File and line | Role |
| --- | --- | --- |
| `compressed_enabled_of_misa` (private) | `Branch.lean:15` | Evaluate Zca from the initialized MISA value. |
| `UntrustedAnswerRun.final_compressed_enabled` | `Branch.lean:36` | Previously staged statement, now proved unchanged. |
| `UntrustedAnswerRun.prepared_compressed_enabled` | `Branch.lean:46` | The same configuration after PC preparation. |
| `branch_shape` (private) | `Branch.lean:55` | Shared metadata and execution form of the six branches. |
| `branch_target_even` (private) | `Branch.lean:72` | Derive target parity from the satisfying witness. |
| `jump_even` (private) | `Branch.lean:128` | Execute Sail's jump with an even target and Zca enabled. |
| `branch_step` | `Branch.lean:149` | Selected-row execution and live-register agreement. |

The following existing declarations were made public in place.
Names are in `JoltInstance`, and paths are relative to `JoltConstraints/Soundness/`.

| Declaration | File and line | Statement change |
| --- | --- | --- |
| `terminal_real_successor_address` | `Layer6/TerminalNextPC.lean:279` | Strengthen its former private conclusion by retaining `row.address.toNat % 2 = 0` alongside the RAM lower bound; no hypothesis added. |
| `terminal_branch_real_target` | `Layer6/TerminalNextPC.lean:335` | Visibility only. |
| `terminal_branch_decision` | `Layer6/TerminalNextPC.lean:392` | Visibility only. |
| `terminal_taken_branch_field` | `Layer6/TerminalNextPC.lean:421` | Visibility only. |
| `branch_target_ne_zero` | `Layer7/LastJump.lean:118` | Visibility only; its docstring now includes an example. |
| `branch_operand_forms` | `Layer7/StallSuffix.lean:308` | Visibility only; added its public docstring. |

The private caller `terminal_taken_branch_target_ram` at `Layer6/TerminalNextPC.lean:451` now selects the RAM-bound component of the strengthened result.
Its statement is unchanged.
Every previously public statement is unchanged.
The existing Branch import at `JoltConstraints.lean:62` remains, and Branch imports the new MISA module transitively.
No new `sorry`, soundness premise, restriction, or core-definition change was introduced.

### Exact error in the remaining plan

The VirtualAdviceLoad item says to prove the permitted widths from the expansion checker.
That implication is false for the current checker.
The exact instruction is:

```lean
.VirtualAdviceLoad (.xreg (.Regidx 1)) (9#64)
```

Both `ExpansionFacts.nativeRowOk instruction = true` and `ExpansionFacts.sequenceOk [instruction] = true` hold.
The width is not 1, 2, 4, or 8.
For every state and answer, `execWithTapeAnswer instruction answer state` returns `.error (Error.Assertion "VirtualAdviceLoad: invalid width") state`.
`advicePairsOk` at `JoltConstraints/expansion_facts.lean:135` imposes its paired-multiply condition only when `width.toNat < 8`, so a width of 9 bypasses it.
The other conjuncts of `nativeRowOk` and `sequenceOk` also accept this instruction.

This is a counterexample to deriving width validity from the checkers alone.
It is not a counterexample to width validity of actual source expansions, and it does not establish a false soundness statement or a model change requirement.
`SourceInstruction.expand` at `JoltConstraints/expansions.lean:118` through its four AdviceLB/LH/LW/LD cases uses the corresponding fixed-width generated programs.
The missing proof should derive width validity from successful source expansion and transport it to the selected bytecode row.
That would supply the width inside the selected step, without adding a caller hypothesis or changing the interpreter or restrictions.
The checker-only argument should be replaced in the plan before that work continues.

The diagnostic is standalone and checked by Lean:

```lean
import JoltConstraints.Soundness.Layer5.MisaFrame
import JoltConstraints.expansion_facts

open Sail PreSail LeanRV64D.Functions JoltISA
open JoltConstraints.Soundness

namespace AdviceWidthCheck

def instruction : Instr := .VirtualAdviceLoad (.xreg (.Regidx 1)) 9

theorem native_checker_accepts : ExpansionFacts.nativeRowOk instruction = true := by decide

theorem sequence_checker_accepts : ExpansionFacts.sequenceOk [instruction] = true := by decide

theorem invalid_width : ¬ ((9#64).toNat = 1 ∨ (9#64).toNat = 2 ∨
    (9#64).toNat = 4 ∨ (9#64).toNat = 8) := by decide

theorem execution_rejects (state : SailJoltState) (answer : BitVec 64) :
    execWithTapeAnswer instruction answer state =
      .error (Error.Assertion "VirtualAdviceLoad: invalid width") state := rfl

#print axioms native_checker_accepts
#print axioms sequence_checker_accepts
#print axioms invalid_width
#print axioms execution_rejects
end AdviceWidthCheck
```

The diagnostic source and log are `/private/tmp/plain-steps-advice-width-check.lean` and `/private/tmp/plain-steps-advice-width-check.log`.
The two checker proofs use `[propext, Classical.choice, Quot.sound]`, the invalid-width proof has no axioms, and the execution proof additionally uses the existing `sys_enable_experimental_extensions` constant.
None reaches `sorryAx` or a native bit-vector axiom.
The pinned tracer's `jolt/tracer/src/instruction/virtual_advice_load.rs` (`VirtualAdviceLoad::exec`) explicitly checks membership in `[1, 2, 4, 8]` with `debug_assert!`, consistent with the interpreter's accepted widths.

Under the instruction to stop and report a false plan claim, no selected VirtualAdviceLoad step was written and Part 2 was not started.
`division_expansion_layout` remains unchanged and staged.
No false checker-implies-width theorem was staged.

### Validation and timings

The final `lake build JoltConstraints` passed with 8,826 jobs, including the other agents' current edits.
The log is `/private/tmp/plain-steps-and-layout-misa-final-build.log`.
The final build reported 5.9 seconds for MisaFrame, 6.8 seconds for Branch, and approximately 10 seconds for TerminalNextPC, each including module processing.
An earlier successful Branch build reported 902 seconds of elapsed time; this was not reproduced by direct proof profiling.
No limit was raised to obtain the build.

`lake env lean -Dtrace.profiler=true -Dprofiler.threshold=10` passed for both new modules.
Logs are `/private/tmp/misa-profile.log` and `/private/tmp/branch-profile.log`.
The longest new proof reported by these runs was `execWithTapeAnswer_keeps_misa` at approximately 0.958 seconds.
`write_rule` took approximately 0.468 seconds, `UntrustedAnswerRun.final_misa` 0.058 seconds, `branch_target_even` 0.031 seconds, and `branch_step` 0.039 seconds.
No new proof over ten seconds was reproduced by profiling.

`lake env lean /private/tmp/plain-steps-misa-axioms.lean` passed; its output is `/private/tmp/plain-steps-misa-axioms.log`.
The five checked roots `execWithTapeAnswer_keeps_misa`, `UntrustedAnswerRun.final_misa`, `UntrustedAnswerRun.final_compressed_enabled`, `UntrustedAnswerRun.prepared_compressed_enabled`, and `branch_step` each depend only on `[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`.
None reaches `sorryAx`.
`JoltInstance.division_expansion_layout` still reaches `[propext, sorryAx, Quot.sound]`, and `JoltInstance.division_block` still reaches `[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`.
There is no VirtualAdviceLoad selected-step declaration to audit yet.

`git diff --check` passed on the owned tracked Lean paths.
There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, and no raised proof limits.
The user-authorized files changed in this continuation are `Layer5/Branch.lean`, the new `Layer5/MisaFrame.lean`, `Layer6/TerminalNextPC.lean`, and the visibility changes in `Layer7/LastJump.lean` and `Layer7/StallSuffix.lean`, plus this report.
Other agents' files were left untouched, including the concurrent Fence, PlainRow, division, register-helper, and row-step work.
No commit was made.
Work stops here for review of the exact checker counterexample and the proposed source-expansion proof route.

## Division layout

Part 2 was audited on `feat/soundness` at `95c69bc`.
The requested `AGENTS.md`, Part 2 and the correction section of `plain-steps-and-layout.md`, `reuse.md`, and Part A of `stage-4a-report.md` were read.
Proof work stopped at a dependency error in the prescribed reuse route.
`division_expansion_layout` remains unchanged, including its existing `sorry`.
This finding concerns the plan's module dependencies; it is not a counterexample to the theorem's statement.

### Dependency error

Part 2 at `methods/layer6/plain-steps-and-layout.md:32` prescribes obtaining the `arithmetic` field from `division_program_rows` in `DivisionPrograms.lean`.
The requested theorem is in `JoltConstraints/Soundness/Layer6/DivisionDefs.lean:109`, but `DivisionPrograms.lean:1` imports `DivisionDefs.lean`.
Importing `DivisionPrograms` into `DivisionDefs` would therefore create a cycle.
The named fact exists and is proved, but it cannot be used at the requested theorem's current location.

| Declaration or dependency | File and line | Checked fact |
| --- | --- | --- |
| `ArithmeticAdviceSequence.arithmetic` | `JoltConstraints/Soundness/Layer6/DivisionDefs.lean:97` | Requires every row of the block to satisfy `DivisionArithmeticRow`. |
| `JoltInstance.division_expansion_layout` | `JoltConstraints/Soundness/Layer6/DivisionDefs.lean:109` | The existing staged target is upstream of `DivisionPrograms`. |
| Import of `DivisionDefs` | `JoltConstraints/Soundness/Layer6/DivisionPrograms.lean:1` | Makes reuse in the reverse direction cyclic. |
| `JoltInstance.division_program_rows_shape` (private) | `JoltConstraints/Soundness/Layer6/DivisionPrograms.lean:250` | Already evaluates the eight generated programs to prove the shared row classification and prefix safety. |
| `JoltInstance.division_program_rows` | `JoltConstraints/Soundness/Layer6/DivisionPrograms.lean:270` | Extracts the full-program classification from that existing proof. |
| `JoltInstance.division_block` | `JoltConstraints/Soundness/Layer6/DivisionBlock.lean:76` | Uses the staged layout theorem. |

The standalone diagnostic `/private/tmp/division-layout-import-check.lean` imports only `DivisionDefs` and queries the Lean environment.
It reports `division_expansion_layout available: true` and `division_program_rows available: false`.
Its log is `/private/tmp/division-layout-import-check.log`.
No tactic proof was attempted after finding the dependency error.
The outstanding arithmetic obligation is still `∀ row ∈ rows, DivisionArithmeticRow row` for the identified generated block.
Copying the existing eight-program classification would conflict with the repository's reuse rule, and the plan's allowed file edits do not include relocating that proof from `DivisionPrograms`.

The proposed repair is to move `division_expansion_layout`, with its name and statement unchanged, into a new `DivisionLayout.lean` importing `DivisionPrograms`, and import the new module from `DivisionBlock.lean`.
This would make the prescribed reuse possible without changing core definitions or theorem hypotheses.
It requires revising the requested location and authorizing the additional `DivisionBlock` import edit, so it was not performed.
There is no new mathematical gap to stage for this dependency issue.
The remaining source-classification and exact-block arguments have not been fully audited or proved; this report does not certify the rest of the plan.

### Validation and scope

`lake env lean JoltConstraints/Soundness/Layer6/DivisionDefs.lean` passed, with the existing `sorry` warning at line 109.
The log is `/private/tmp/division-layout-defs-check.log`.
Only the owned source module was checked directly; no aggregate build or dependency rebuild was requested while the checker work is in progress.

`lake env lean /private/tmp/division-layout-axioms.lean` passed using the existing compiled imports.
The log is `/private/tmp/division-layout-axioms.log`.
Its exact axiom results are:

| Root | Axioms |
| --- | --- |
| `JoltInstance.division_expansion_layout` | `propext`, `sorryAx`, `Quot.sound` |
| `JoltInstance.division_program_rows` | `propext`, `Quot.sound` |
| `JoltInstance.division_block` | `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |

No Lean declaration was added, changed, relocated, or made public.
There are no statement changes, added hypotheses, new staged lemmas, new `bv_decide` uses, `native_decide` uses, `decide +kernel` uses, or raised limits.
No new proof requires a timing report.
`git diff --check` passed.
Only this report was changed in the repository by this task; all excluded files were left untouched.
No commit was made.

### Completion after the module-placement correction

The approved relocation and Part 2 proof are complete on `feat/soundness`; the final working-tree review was at `c7b91ff` after the concurrent agent's commit.
`JoltInstance.division_expansion_layout` now lives in `JoltConstraints/Soundness/Layer6/DivisionLayout.lean:226`.
A text comparison against the saved original declaration confirms that its name, statement and docstring are unchanged.
`DivisionBlock.lean:2` imports the new module, and `JoltConstraints.lean:94` includes it in the aggregate imports.
The old declaration was removed from `DivisionDefs.lean`; its definitions and remaining proofs were left unchanged.

#### Checked claims and proof structure

`expand_program_source_of_row` supplies an actual emitting source in the image.
The source expansion's `starts` certificate puts the selected row at offset zero, and its countdown determines the full row count.
`source_expansion_split` locates the source's rows as a contiguous block in the materialized bytecode using `option_mapM_results`.
`expansion_block_eq` then uses `expand_program_unique` to identify the block's starting index and prove the exact extracted instruction-list equality.
This uses the existing expansion certificates and accepted PC-map uniqueness, without copying the private block proof in `PlainRow.lean` or identifying a block solely by address.

`source_instructionAt` derives address uniqueness through `pc_map_ok_distinct_addresses` and proves that the image's address lookup returns this source.
The short lookup proof needs no new staged fact or hypothesis.

`source_advice_kind` classifies `SourceInstruction.expand` once.
The eight division cases retain their generated programs symbolically and use the shared `division_source_kind` proof to rule out x0.
For the remaining constructors, the generated and handwritten expansion definitions reduce to absence of internal `VirtualAdvice`.
Conditional choices are transported through the advice observers by specialized, pre-order instances of `apply_ite`, without enumerating operand values or splitting each expansion into separate proofs.
`VirtualAdviceLoad` is correctly excluded by `Instr.adviceValue?`.

The existing eight-program evaluation in `division_program_rows_shape` was extracted into the stronger private `division_program_structure` proof.
The original private theorem keeps its exact statement and becomes a projection of that result.
The same evaluation now also establishes advice-word patching and the filtered count of internal-advice rows.
The new public `division_program_advice_shape` exposes those two conclusions for nonzero destinations.
No eight-program evaluation was copied, and `division_source_advice_single` from `DivisionAppend.lean` was not used.

`expanded_division_shape` obtains `arithmetic` from the existing `division_program_rows`, `temporaries` from `sequenceOk_tempsReadAfterWrite`, and `program_eq` and `singleAdvice` from the extracted program-shape result.
The final layout proof assembles these facts without changing its premises.

The pinned-code audit read Jolt's expander in `jolt/crates/jolt-program/src/expand/mod.rs` (`expand_source_instruction_with_provider`), the division recipes including `division/rem.rs` (`expand_rem`) and `division/shared.rs` (`expand_unsigned_word_div_rem`), and `preprocess/bytecode.rs` (`BytecodePCMapper::try_new`) at `5def437f`.
The repository-relative paths passed to `git show` omit the leading `jolt/` directory label.
The checked recipes agree with the x0 no-op rewrite, internal advice positions, and rejection of repeated address runs used by this proof.
No further incorrect claim in the corrected Part 2 plan was found.

#### Declaration inventory

All names below are in namespace `JoltInstance`, and paths are relative to `JoltConstraints/Soundness/Layer6/`.
Every listed theorem is proved.

| Declaration | File and line | Role or change |
| --- | --- | --- |
| `expandedInternalAdvice` (private definition) | `DivisionLayout.lean:14` | Detect internal advice in a native or sequence expansion. |
| `SourceInternalAdvice` (private definition) | `DivisionLayout.lean:20` | Apply that detector to a source expansion. |
| `division_source_kind` (private) | `DivisionLayout.lean:23` | A division with internal advice cannot have destination x0. |
| `source_advice_kind` (private) | `DivisionLayout.lean:34` | The single classification of advice-bearing sources. |
| `source_internal_advice_of_rows` (private) | `DivisionLayout.lean:78` | Transport an advice-bearing materialized row back to its source expansion. |
| `source_expansion_split` (private) | `DivisionLayout.lean:103` | Locate the emitting source's contiguous row block. |
| `expansion_block_eq` (private) | `DivisionLayout.lean:123` | Identify the exact extracted instruction list and row count. |
| `source_instructionAt` (private) | `DivisionLayout.lean:164` | Address lookup returns the source, using preprocessing uniqueness. |
| `division_source_expand` (private) | `DivisionLayout.lean:183` | Connect each division source with `ofPureProgram`. |
| `divisionRows_arithmetic` (private) | `DivisionLayout.lean:189` | Extract arithmetic membership from the existing `DivisionRows` certificate. |
| `expanded_division_shape` (private) | `DivisionLayout.lean:200` | Assemble all four fields of `ArithmeticAdviceSequence`. |
| `division_expansion_layout` | `DivisionLayout.lean:226` | Moved and proved with its name, statement and docstring unchanged. |
| `division_program_structure` (private) | `DivisionPrograms.lean:250` | Generalize the existing single evaluation to retain row safety, patching and advice count together. |
| `division_program_rows_shape` (private) | `DivisionPrograms.lean:272` | Original statement retained; proof now projects the generalized result. |
| `division_program_advice_shape` | `DivisionPrograms.lean:282` | New public patching and single-advice facts for a nonzero destination. |

No existing private declaration was made public.
No existing theorem statement changed, and no hypothesis was added to the layout theorem or its callers.
The new helper's nonzero-destination premise is discharged by the source classification.
There are no new staged gaps, `bv_decide` uses, `native_decide` uses, `decide +kernel` uses, or raised limits.
Every new or reworked proof body is under 60 lines.

#### Validation and timings

Direct `lake env lean` compilation with explicit output files passed for `DivisionDefs`, `DivisionPrograms`, `DivisionLayout`, and `DivisionBlock`, in dependency order.
No aggregate build or rebuild of the other agent's modules was requested.
The final logs are `/private/tmp/division-layout-final-defs.log`, `/private/tmp/division-layout-final-programs.log`, `/private/tmp/division-layout-final-layout.log`, and `/private/tmp/division-layout-final-block.log`.
The only warning in these final runs is the existing unused `nonzero` parameter in `division_append_honest` at `DivisionBlock.lean:31`; that declaration was not changed.

Proof profiling used `lake env lean -j1 -Dtrace.profiler=true -Dprofiler.threshold=10` while compiling `DivisionPrograms` and `DivisionLayout`.
The longest new proof was `source_advice_kind` at 1.642826 seconds, followed by `division_program_structure` at 1.513135 seconds.
`division_expansion_layout` took 0.087818 seconds.
No new or reworked proof exceeded ten seconds.

`lake env lean /private/tmp/division-layout-final-axioms.lean` passed.
The log is `/private/tmp/division-layout-final-axioms.log`.

| Root | Axioms |
| --- | --- |
| `JoltInstance.division_expansion_layout` | `propext`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.division_program_advice_shape` | `propext`, `Quot.sound` |
| `JoltInstance.division_block` | `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |

None of these roots reaches `sorryAx` or a native bit-vector axiom.
The proof-obligation list and soundness status were updated to record completion.
The stale obligation for `division_replay_complete`, already proved at `DivisionAppend.lean:1937` before this task, was also removed from the list; its Lean code was not changed.
`git diff --check` passed.
The excluded Lean files and the other agent's edits, including the separate `AdviceLoad` aggregate import, were left untouched.
No commit was made.
