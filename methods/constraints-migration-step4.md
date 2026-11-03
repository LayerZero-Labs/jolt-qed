# Constraints migration, step 4: soundness proofs

Ari approved this step on 2026-11-03.
It is written for an agent that has not seen the earlier steps.
Delete this file once the step is reviewed and its content is in the code, in `methods/soundness.md` and in `JoltConstraints/model_review.md`.

## Context

- Repository: `/Users/ari.biswas/Lean/jolt-qed-public`, branch `review/audit-completeness-soundness`.
  Start from the commit Ari makes after step 3; if the working tree is not clean when you start, stop and ask.
  Read `AGENTS.md` first; it overrides your defaults.
- The Lean model of Jolt is being migrated from Jolt commit `5def437f` to `c6703570`.
  Jolt's code is in `/Users/ari.biswas/Work-with-A16z/jolt`; read it with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.
- Steps 1 to 3 are done.
  Read, in order: `reports/2026-11-02-constraints-migration-definitions.md`, `reports/2026-11-03-constraints-migration-completeness.md` and `reports/2026-11-03-tracer-address-checks-floor-rows.md`.
  The model definitions match `c6703570`, completeness builds, and `JoltInstance.TracerAddressChecks` now covers the new memory rows.
- What changed in the ISA:
  - Sub-word loads and stores expand into new rows, `VirtualLoadB/H/W (faultClass dst base imm fault)` and `VirtualStoreB/H/W (base value imm fault)` (`JoltBytecode/JoltISA/Instruction.lean`).
    Each accesses the 8-byte word at `ea &&& ~~~7`, where `ea = base + imm`; Jolt's tracer records the RAM address `ea - (ea &&& mask)`, with `mask` 7, 6 and 4 for B, H and W.
  - They have circuit flags `Load` or `Store` with `AddOperands`, and look up `AddressOffsetB/H/W`, which returns `ea &&& mask`.
  - `VirtualShiftDataB/H/W` gained an immediate, `(dst value address imm)`, and set `RightOperandIsImm` as well as `RightOperandIsRs2Value`.
  - LD sets the new instruction flag `RightOperandIsRdWriteValue`.
  - `VirtualAlignAddr`, `VirtualAssertHalfwordAlignment` and `VirtualAssertWordAlignment` are gone, with the `AlignAddr`, `HalfwordAlignment` and `WordAlignment` tables.
  - Constraint (01) is now `(Load + Store) · (RamAddress - Rs1Value - Imm + LookupOutput) = 0`, named `ramAddrEqRs1PlusImmMinusLookupIfLoadStore`.
    Constraint (33) adds `RightOperandIsRdWriteValue · RdWriteValue`.
  - `opcodeFlag_load_requiresLD` and `opcodeFlag_store_requiresSD` were replaced by `opcodeFlag_load_cases` and `opcodeFlag_store_cases` (`JoltConstraints/metadata.lean`), whose conclusions include the new rows.
- At Lean commit `7096dca`, before the migration, `JoltInstance.soundness` (`JoltConstraints/Soundness/soundness.lean`) had no `sorry`, and `#print axioms JoltInstance.soundness` listed only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
  The plan and layers of the soundness proof are in `methods/soundness.md`.

## Goal

`lake build JoltConstraints` succeeds, and `JoltInstance.soundness` is again proved with no `sorry`, using the same axioms as before.
The statement of `JoltInstance.soundness`, `JoltInstance.InLanguage` and the soundness assumptions do not change.

## Work

1. The six modules that fail today, with their first errors (from the step 2 report):
   - `Soundness/Layer2/ZeroRegister.lean:45`: unsolved goals.
   - `Soundness/Layer4/Inputs.lean:34`: unsolved goals.
   - `Soundness/Layer4/Word.lean:62`: unknown constant `LookupTableKind.AlignAddr`.
   - `Soundness/Layer4/Assertions.lean:24`: unknown constant `LookupTableKind.HalfwordAlignment`.
   - `Soundness/Layer5/MemoryAddress.lean:40`: unknown identifier `ramAddrEqRs1PlusImmIfLoadStore`.
   - `Soundness/Layer5/TapeSemantics.lean:67`: type mismatch.
   Fix these, then every module they unblock, until the whole library builds.
2. Classifier call sites: `Soundness/Layer6/PlainRow.lean:949` and `:954`, `Soundness/Layer7/TerminationStore.lean:703`, `Soundness/Layer7/StallSuffix.lean:3305`.
   Use `opcodeFlag_load_cases` and `opcodeFlag_store_cases`, and handle the new rows.
3. Align-address proofs: `Soundness/Layer5/AddressMasks.lean:32` and `:124` use `jolt_virtual_align_addr_value64`.
   Replace that reasoning with the new rows' AddressOffset lookup and constraint (01).
4. Memory rows.
   Where a proof about LD and SD must now also cover the new loads and stores, prove it once over the three widths, not once per row.
   `TracerAddressChecks` gives the address checks for the word at `ea &&& ~~~7`.
   Constraint (01), the AddressOffset lookup and the RAM address checks together should pin the accessed word; Jolt's own argument is the comment on row 0 in `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`.

5. Panic and termination restrictions, approved by Ari on 2026-11-03.
   `PanicStoresOne` and `TerminationThenStall`, and their history predicates `StoresPanicAt` and `StoresTerminationAt`, name only LD and SD; the new loads and stores also touch the panic and termination words.
   Extend them exactly as follows, where each new arm checks the 8-byte word the row accesses, `ea &&& ~~~7`, and change nothing else.
   Add one sentence to each restriction's FIXME docstring: the extension to `VirtualLoadB/H/W` and `VirtualStoreB/H/W` was approved by Ari on 2026-11-03, only to fit the new ISA.

   In `Soundness/Layer5/PanicRestriction.lean`, `UntrustedAnswerRun.StoresPanicAt`, before `| _ => False`:

   ```lean
   | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _ | .VirtualStoreW base _ imm _ =>
       TouchesPanic run.rows[i].preState.jolt_device
         ((sourceValue base run.rows[i].preState + imm) &&& ~~~7)
   ```

   In the same file, `JoltInstance.PanicStoresOne`, before `| _ => True`:

   ```lean
   | .VirtualStoreB base value imm _ | .VirtualStoreH base value imm _
   | .VirtualStoreW base value imm _ =>
       JoltConstraints.Soundness.TouchesPanic pre.jolt_device
           ((JoltISA.sourceValue base pre + imm) &&& ~~~7) →
         JoltISA.sourceValue value pre = 1
   | .VirtualLoadB _ _ base imm _ | .VirtualLoadH _ _ base imm _ | .VirtualLoadW _ _ base imm _ =>
       (∃ i, run.StoresPanicAt i) →
         ¬ JoltConstraints.Soundness.TouchesPanic pre.jolt_device
           ((JoltISA.sourceValue base pre + imm) &&& ~~~7)
   ```

   In `Soundness/Layer5/TerminationRestriction.lean`, `UntrustedAnswerRun.StoresTerminationAt`, before `| _ => False`:

   ```lean
   | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _ | .VirtualStoreW base _ imm _ =>
       TouchesTermination run.rows[i].preState.jolt_device
         ((sourceValue base run.rows[i].preState + imm) &&& ~~~7)
   ```

   In the same file, `JoltInstance.TerminationThenStall`, before `| _ => True`:

   ```lean
   | .VirtualLoadB _ _ base imm _ | .VirtualLoadH _ _ base imm _ | .VirtualLoadW _ _ base imm _ =>
       ¬ JoltConstraints.Soundness.TouchesTermination pre.jolt_device
         ((JoltISA.sourceValue base pre + imm) &&& ~~~7)
   ```

   Adjust only the Lean details needed to make these build, and keep their meaning.
   Then finish the blocked proofs from them: `row_panic_of_no_store` (`Soundness/Layer5/DeviceMemory.lean`), `termination_effect_is_sd` (`Soundness/Layer7/TerminationStore.lean`) and the `DeviceMemoryStepAgreement` facts they feed.
   A theorem whose conclusion now names only SD may need to name the new stores too; that is a helper change under "Approved without asking".

## Approved without asking

Ari has approved, in advance, any proof repair, and any new or changed helper lemma, when both of these hold:

- the statement of `JoltInstance.soundness`, `InLanguage`, the assumptions and the restrictions stay as they are;
- the helper is proved, and every caller can prove its hypotheses from the premises it already has.

Make such changes without stopping, and list each one in the report.

## Stop and report to Ari

Do not stop at the first problem.
Leave a blocked lemma as it is, finish everything else, then stop and report all blockers together.
A blocker is:

- A fact the proof needs that you cannot prove from the current premises.
  State it as its own named lemma with `sorry`, check it against "Before staging a statement" in `AGENTS.md`, and report it with the exact missing fact.
  If you believe it is false, give the counterexample instead; do not add a premise.
- A fix that would change the soundness statement, `InLanguage`, an assumption, a restriction, a model definition or a completeness file.
- A rule in "When stuck, discuss first" of `AGENTS.md`.

## Rules

- `AGENTS.md` applies, including "Making proofs general".
- No `native_decide`, `decide +kernel` or `bv_decide`, and never raise `maxHeartbeats`.
- No `sorry` except a blocker lemma as described above.
- Do not commit; Ari commits.
- Builds are allowed to check a change: first check for a running Lake process (`pgrep -fl lake`), then build serially.
  Never start a build while another is running, even one you started yourself.
- Give every new or changed declaration a docstring that defines its terms and gives a concrete example.
- List every proof that takes more than about ten seconds.
- In Markdown, one sentence per line; in prose, name the actor (Jolt's tracer, prover or verifier), not "Rust".
- Put scratch files in your session scratchpad, not in the repository or `/tmp`.

## Deliverables

1. The diff, uncommitted.
2. Update `methods/soundness.md` ("Current state") and "Proofs owed" in `JoltConstraints/model_review.md` to match the code.
3. A report, `reports/YYYY-MM-DD-constraints-migration-soundness.md`, one sentence per line, giving:
   - the date, the Jolt commits (`5def437f`, `c6703570`) and the Lean commit you started from;
   - every declaration changed, added or removed, with file and line;
   - every statement change;
   - the build commands and results, `#print axioms JoltInstance.soundness`, and any proof slower than about ten seconds;
   - every blocker, with its lemma and the exact missing fact.

Then stop for review.
