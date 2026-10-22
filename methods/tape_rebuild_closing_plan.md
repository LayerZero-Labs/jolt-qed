# Closing the tape rebuild: the second half of Layer 7

This file is for a fresh agent with no prior context.
Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` first; its rules apply to everything below.

## What the theorem says

A Jolt program can read private bytes from an advice tape that the prover chooses.
A 1-, 2-, 4- or 8-byte read takes the next bytes from the tape.
The verifier never checks the tape, so a witness may make a 1-byte read deliver a value too large for one byte, such as 300.
The soundness proof therefore first builds a relaxed run, `UntrustedAnswerRun` (`JoltConstraints/Soundness/Layer5/TapeTrace.lean`), in which every read returns an arbitrary 64-bit answer (`execWithTapeAnswer`, `Soundness/Layer5/TapeSemantics.lean`).

The tape rebuild turns any relaxed run into a real run with a fixed tape.
The tape holds the low bytes of each answer in read order, so 300 read as one byte becomes `0x2C`, which is 44.
The real run then reads 44 where the relaxed run read 300.
The two runs differ only in that read's destination register, and only until the next row, a multiply that shifts the value left by `64 - 8 * width` bits and so discards the high bytes.
From that multiply on, the two runs are identical.

The goal is `untrustedAnswerLanguage_implies_inLanguage` in `JoltConstraints/Soundness/Layer7/TapeRebuild.lean`.
Everything in it is proved except one declaration, `rebuild_rows`, which builds the real run's rows.

## Where things are

- Branch `feat/layer7-tape-rebuild`, worktree `/Users/ari.biswas/Lean/jolt-qed-tape-rebuild`, commit `44b8695`.
  `TapeRebuild.lean` elaborates in about 8 seconds; its only `sorry` is `rebuild_rows`.
  Check it with `lake env lean JoltConstraints/Soundness/Layer7/TapeRebuild.lean` from the worktree root.
- Another agent is working on branch `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public`, following `methods/step_c_closing_plan.md`.
  It is extending `ExpansionFacts.sequenceOk` (`JoltConstraints/expansion_facts.lean`) and editing `trace_interface.lean`, `program_facts.lean` and the Layer 7 stopping files.
  Do not edit those files until its Part 1 is committed; see step 6.
- Jolt's Rust code is at `/Users/ari.biswas/Work-with-A16z/jolt`, pinned at `8bbb2357`.
  Read files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 8bbb2357:<path>`; the advice tape is `tracer/src/emulator/cpu.rs:24-60`, the expansions are `crates/jolt-program/src/expand/memory/advice_{lb,lh,lw,ld}.rs`.

## The target

`rebuild_rows` (`TapeRebuild.lean`, near line 1185) must produce a `RebuiltRows original initial`, where `initial` is the relaxed initial state with tape bytes `rebuiltTape original` and read position 0.
`RebuiltRows` (just above it) has six fields: `length`, `executes`, `starts`, `linked`, `agrees` and `sourceStartPre`.
The replayed rows must run under the fixed-tape interpreter `execInstr`, link like the relaxed rows, and agree with them as `ReplayStateAgreement` and `NarrowAdvicePending` describe.

## The construction

Build the rows directly from the relaxed rows; no recursion is needed.
Each replay row keeps the relaxed row's `rowIndex` and `runtimeAdvice`, and maps its pre-state and post-state.

```lean
/-- `some (dst, w)` when bytecode row `k` is a narrow tape read `VirtualAdviceLoad dst width`
with `w = width.toNat < 8`. AdviceLB's load gives `some (dst, 1)`; AdviceLD's gives `none`. -/
private def narrowLoadAt? (bytecode : Array JoltInstructionRow) (k : Nat) : Option (Dst × Nat) :=
  match (bytecode[k]?).map (·.instruction) with
  | some (.VirtualAdviceLoad dst width) => if width.toNat < 8 then some (dst, width.toNat) else none
  | _ => none

/-- The read whose destination is still unmasked when row `k` starts: the row before it. -/
private def pendingBefore? (bytecode : Array JoltInstructionRow) (k : Nat) : Option (Dst × Nat) :=
  if k = 0 then none else narrowLoadAt? bytecode (k - 1)

/-- The source operand naming the same register as a destination. -/
private def dstSource : Dst → Src
  | .xreg r => .xreg r
  | .vreg v => .vreg v

/-- A relaxed state seen in the replay: rebased onto the rebuilt tape, and with a pending
read's destination cut to its low bytes. For a 1-byte read of 300, the destination holds 44. -/
private noncomputable def replayState (run : UntrustedAnswerRun joltInstance privateInputs)
    (pending : Option (Dst × Nat)) (state : SailJoltState) : SailJoltState :=
  let rebased := rebaseTapeState run.initialState.adviceTape.bytes (rebuiltTape run) state
  match pending with
  | none => rebased
  | some (dst, width) =>
      replaceDst dst rebased (lowAnswer (sourceValue (dstSource dst) state) width)
```

The replay row at step `i` has pre-state `replayState run (pendingBefore? run.bytecode k) pre` and post-state `replayState run (narrowLoadAt? run.bytecode k) post`, where `k` is the row's bytecode index and `pre`, `post` are the relaxed row's states.
Define `rows := Array.ofFn (replayRow run)`.
Adjust the names and binders to the file; the shape above is what matters.

## The one bytecode fact

State it as one lemma, with `sorry` for now (step 6 proves it):

```lean
/-- In expanded bytecode, a narrow tape read continues its source instruction and is followed
by the multiply that discards its high bytes. For example, AdviceLB's load is followed by
`VirtualMULI rd rd 2^56`. See jolt/crates/jolt-program/src/expand/memory/advice_lb.rs at 8bbb2357. -/
private theorem narrow_load_shape (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode)
    (k : Nat) (inRange : k < bytecode.size) (dst : Dst) (width : BitVec 64)
    (load : bytecode[k].instruction = .VirtualAdviceLoad dst width) (narrow : width.toNat < 8) :
    ∃ rd, dst = sideEffectingRdZeroDst rd ∧ bytecode[k].continues = true ∧
      ∃ next : k + 1 < bytecode.size,
        bytecode[k + 1].instruction = .VirtualMULI (sideEffectingRdZeroDst rd)
          (adviceReadSource rd) (slliMultiplier (BitVec.ofNat 6 (64 - 8 * width.toNat)))
```

Two consequences are used repeatedly; prove them once:

- A narrow load's next row does not start a source instruction.
  `(expand_program_layout image bytecode expanded).next` (`JoltConstraints/ProgramLayout.lean:30`) gives it `is_first_in_sequence = false` and a countdown, and `starts_source` (`JoltConstraints/program.lean:120`) is `remaining.isNone || is_first_in_sequence`.
- So `pendingBefore? bytecode k = none` whenever row `k` starts a source instruction or is itself a `VirtualAdviceLoad`.

## Proving the six fields

`length`: `Array.size_ofFn`.

`linked`, when the current row continues its instruction: the relaxed run gives `next.rowIndex = current.rowIndex + 1` and `next.preState = current.postState`, and `pendingBefore? bytecode (k + 1) = narrowLoadAt? bytecode k` holds by definition, so the replay states agree with no further work.

`linked`, when the current row ends its instruction: a narrow load always continues (`narrow_load_shape`), so the current post-state is just rebased, and nextPC is unchanged.
The next row starts a source instruction, so its pre-state is just rebased, and `rebaseTapeState_advance_pc` commutes the rebase with `advance_pc`.

`starts`: the first row starts its source, so its pre-state is rebased.
`rebaseTapeState_advance_pc` moves the rebase inside `advance_pc`.
The rebased initial state is `initial`, because the host suffix of the initial tape is empty and `JoltInstance.initial_state_adviceTape_readPosition_zero` (`JoltConstraints/advice_inputs.lean`) gives read position 0.

`sourceStartPre`: a source start has no pending read, so its pre-state is rebased, and `rebaseTapeState_same` gives `SameExceptTapeBytes`.

`agrees`:

- `rowIndex` and `someTracerAdvice?` are equal by construction (`someTracerAdvice?` reads only the bytecode row and the runtime advice).
- nextPC: rebasing touches only tape bytes, and `replaceDst` writes a general register or a virtual register, never nextPC.
  For the register write, look for a frame lemma on `stateAfterWrite` such as `stateAfterWrite_preservesSystemProjectRegs` (`JoltBytecode/InstructionEquivalence/ProofSupport/Projection.lean:324`).
- `ReplayStateAgreement`: prove `NarrowAdvicePending bytecode k false dst ↔ ∃ w, narrowLoadAt? bytecode k = some (dst, w)`, and the same for `true` with `pendingBefore?`, the `←` direction using `narrow_load_shape`.
  The bytecode row determines `dst`, so the pending destination is unique.
  Then for a pending `(dst, w)`, take the witness value `lowAnswer … w`: `replaceDst` commutes with the rebase, and `rebaseTapeState_same` closes it.
  Without a pending read, `rebaseTapeState_same` closes it directly.

`executes`: split on the row's instruction.
`withRuntimeAdvice_eq_of_noAdvice` (`Soundness/Layer5/RuntimeAdvice.lean:16`) removes the runtime advice for loads and multiplies.

1. A row that is neither a `VirtualAdviceLoad` nor right after a narrow load.
   The relaxed `execWithTapeAnswer` is `execInstr` here.
   `swap_execInstr_nonload` gives the run on swapped tape bytes, with the same appended suffix.
   `initial_bytes_prefix` and `execWithTapeAnswer_bytes_extend` give the original bytes as the private tape followed by the host suffix.
   `tapeHostSuffix_of_append` then shows the result is the rebased post-state.
2. The multiply right after a narrow load.
   By `narrow_load_shape`, the instruction is `VirtualMULI (sideEffectingRdZeroDst rd) (adviceReadSource rd) (slliMultiplier …)`.
   The replay reads the low bytes, and the relaxed run reads the full answer.
   The multiply is a left shift, `BitVec.mul_twoPow_eq_shiftLeft` after unfolding `jolt_virtual_muli_value`, `mulWide_low` and `slliMultiplier`.
   `lowAnswer_shift_width` makes both products equal, and the write overrides the pending destination.
3. A narrow `VirtualAdviceLoad`.
   Its pre-state has no pending read, so it is rebased.
   `preCursor_eq_rebuiltTapeOffset` puts the read position at the rebuilt offset, and `rebuiltTape_read_exact` makes the fixed read return `lowAnswer (run.answers i) width`.
   `writeDst_run` (`JoltBytecode/InstructionEquivalence/ProofSupport/NativeDispatch.lean:42`) writes it as `afterDst`.
   The expected post-state replaces the destination of the rebased relaxed post-state with the same low value.
4. An 8-byte `VirtualAdviceLoad`: as case 3 with no pending destination, since `lowAnswer a 8 = a`.

Helpers you will need, with the existing ones to reuse:

- `replaceDst (sideEffectingRdZeroDst rd) s v = NativeDispatch.afterDst s rd v`, by cases on `isX0 rd`.
- `dstSource (sideEffectingRdZeroDst rd) = adviceReadSource rd`.
- Reading after a write, and two writes to one register: `read_afterDst` and `afterDst_afterDst` in `Soundness/Layer5/AdviceExpansion.lean:39` and `:52`.
  They are `private`; make them public rather than copying them.
- The rebase commutes with `replaceDst` and `afterDst`, since neither touches tape bytes.

## Steps

1. Add the definitions and `narrow_load_shape` (with `sorry`) above `RebuiltRows`, and check the file.
2. Prove the two consequences of `narrow_load_shape` and the `NarrowAdvicePending` equivalences.
3. Prove the helpers, then the six fields as above, and assemble `rebuild_rows`.
   `rebuild_rows` is then a `def` whose only dependency on `sorry` is `narrow_load_shape`.
4. Cleanup in `TapeRebuild.lean`:
   - delete `advicel{b,h,w,d}_low_answer` and `lowAnswer_muli_{1,2,4}` if nothing uses them;
   - fix the docstring on `RebuildAgreement.ram_address_eq`, which describes `execution_dimensions_eq`;
   - make sure every public theorem has a docstring;
   - keep every proof under about 60 lines and about one second, unless a slower proof is significantly simpler (see `AGENTS.md`).
5. Commit on `feat/layer7-tape-rebuild` (Ari authorizes this commit; no Co-Authored-By lines), and report.
6. When the step (c) agent's Part 1 is committed on `feat/soundness` (Ari will tell you), rebase onto it and prove `narrow_load_shape`.
   Part 1 adds a check `advicePairsOk` to `sequenceOk`, saying an expansion's narrow loads are followed by exactly this multiply, and makes `expand_ok` prove it for every source instruction.
   Lift it from each expansion's instruction list to the bytecode the way `ShiftPairs` is lifted (`trace_interface.lean:536-624`).
   Do not copy that lift: generalize it to any "row k + 1 matches row k" property, and use the general version for both shift pairs and advice pairs.
   Then nothing in `TapeRebuild.lean` depends on `sorry`.

## Rules for this task

- Do not change the statements of `untrustedAnswerLanguage_implies_inLanguage`, `rebuild_valid_run`, the transfer theorems, `RebuiltRows`, `RebuildAgreement`, `ReplayStateAgreement` or `NarrowAdvicePending`.
- Under the standing approval in `AGENTS.md`, you may add a hypothesis to a private helper if its caller can prove it; list each such change in your report.
- If any step fails because a statement is false, stop and report the exact missing fact.

## Final report

- The elaboration time of every declaration you added or changed, and of the whole file.
- The axiom audit for `untrustedAnswerLanguage_implies_inLanguage`: before step 6 it may carry `sorryAx` only through `narrow_load_shape`, and after step 6 none.
- Every helper hypothesis you added.
