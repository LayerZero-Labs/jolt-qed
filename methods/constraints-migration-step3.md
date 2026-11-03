# Constraints migration, step 3: style fix and the tracer-address premise

Ari approved this step on 2026-11-03.
It is written for an agent that has not seen the earlier steps.
Delete this file once the step is reviewed and its content is in the code and in `JoltConstraints/model_review.md`.

## Context

- Repository: `/Users/ari.biswas/Lean/jolt-qed-public`, branch `review/audit-completeness-soundness`, starting at commit `fcf21c8`.
  Read `AGENTS.md` first; it overrides your defaults.
- The Lean model of Jolt is being migrated from Jolt commit `5def437f` to `c6703570`.
  Jolt's code is in `/Users/ari.biswas/Work-with-A16z/jolt`; read it with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.
- Steps 1 and 2 are done and committed: the model definitions match `c6703570`, and `lake build JoltConstraints.Completeness` succeeds.
  Read `reports/2026-11-02-constraints-migration-definitions.md` and `reports/2026-11-03-constraints-migration-completeness.md`.
  Six soundness modules still fail to build; they are not part of this step.
- In the new ISA, sub-word loads and stores expand into new rows: `VirtualLoadB/H/W (faultClass dst base imm fault)` and `VirtualStoreB/H/W (base value imm fault)`, declared in `JoltBytecode/JoltISA/Instruction.lean`.
  Each accesses the 8-byte word containing `ea = base + imm`, at address `ea &&& ~~~7`.
  Jolt's tracer records the RAM address `ea - (ea &&& mask)`, with `mask` 7, 6 and 4 for B, H and W.
  The retired rows are `VirtualAlignAddr`, `VirtualAssertHalfwordAlignment` and `VirtualAssertWordAlignment`.

## Task A: style fix

The two lemmas `_root_.HonestTrace.shiftData_address_noWrap` (`JoltConstraints/Completeness/RightLookupEqRightInputOtherwise.lean:46`) and `_root_.HonestTrace.floorAccess_address_nonneg` (`JoltConstraints/Completeness/RightLookupAdd.lean:47`) use `_root_.` in their names.
Ari's rule is that no declaration name uses `_root_`.
Declare each one outside `namespace JoltConstraints`, for example by closing the namespace before it and reopening it after, so its name is `HonestTrace.shiftData_address_noWrap` or `HonestTrace.floorAccess_address_nonneg` and dot notation still works.
Change nothing else about them: the statements, the docstrings (approved by Ari) and the `sorry` bodies stay exactly as they are.
Then check that `lake build JoltConstraints.Completeness` still succeeds.

## Task B: draft the tracer-address premise for the new rows

`JoltInstance.TracerAddressChecks` (`JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:86`) is a temporary premise of the soundness theorem, through the field `tracerAddressChecks` (`JoltConstraints/Soundness/Assumptions.lean:86`).
It says: for any private inputs, any partial run of the program (`UntrustedAnswerRun`, `JoltConstraints/Soundness/Layer5/TapeTrace.lean:21`) and the row it would execute next (`UntrustedAnswerRun.NextStep`), an LD's address passes the tracer's read checks and an SD's address passes the write checks (`DoublewordAddressChecks`, same file, line 63, built on `Mmu.effective_address_ok` in `JoltBytecode/JoltISA/DeviceMemory.lean:41`).
Every other row gets `True`.
Its docstring says LD and SD are the only memory accesses after expansion; that is no longer true, so the new rows are now unchecked.

Ari approved on 2026-11-02 extending this premise to the new loads and stores, as a temporary premise added only to fit the new ISA.
Your job is to draft the exact Lean text of that extension and stop, without editing the Lean file.

1. Read how the new rows access memory, in Lean and in Jolt's tracer:
   - Lean: the `VirtualLoadB/H/W` and `VirtualStoreB/H/W` cases of `execInstr` in `JoltBytecode/JoltISA/Semantics.lean`;
   - Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `store`, `addresses`) and `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`, `Mmu::store_doubleword`, `Mmu::assert_effective_address`).
2. For one new row, keep four things apart: the effective address `ea`, the recorded RAM address, the accessed doubleword `ea &&& ~~~7`, and any alignment condition.
   Say which address each check uses, in Lean and in Jolt's tracer.
3. Draft the new `TracerAddressChecks`: the match arms for the six new rows, and a corrected docstring.
   The docstring must keep the FIXME form given in `methods/soundness.md` (Layer 5b) and say the extension was added only to fit the new ISA.
4. Write the draft into a report, `reports/YYYY-MM-DD-tracer-address-checks-floor-rows.md`, one sentence per line, with:
   - the date, the Jolt commit `c6703570` and the Lean commit `fcf21c8`;
   - the current definition and the proposed one, in full;
   - for each new arm, the address it checks and the Lean and Jolt code it follows, by file and item name;
   - any difference you found between Lean's execution rules and Jolt's tracer for these rows.

Do not edit `MemoryAccessRestriction.lean`, any soundness proof, or any other file in task B.

## Rules

- `AGENTS.md` applies.
- No `sorry`, `native_decide`, `decide +kernel` or `bv_decide` in new work, and never raise `maxHeartbeats`.
- No new premise on any theorem.
- Do not commit; Ari commits.
- Builds are allowed to check a change: first check for a running Lake process (`pgrep -fl lake`), then build serially.
- In Markdown, one sentence per line.
- In prose, name the actor: Jolt's tracer, prover or verifier, not "Rust".
- Put scratch files in your session scratchpad, not in the repository or `/tmp`.

## Stop and report to Ari

Stop after task A and the task B report.
Your final message should be short: whether task A builds, and the proposed `TracerAddressChecks` with a few plain sentences on what each new arm checks.
Ari reviews the proposal before any Lean file changes.
