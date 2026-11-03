# Constraints migration, step 2: completeness proofs

Ari approved this step on 2026-11-02.
Delete this file once the step is reviewed and its content is in the code, in `JoltConstraints/constraints.md` and in `JoltConstraints/model_review.md`.

## Context

- Step 1 changed the model definitions to match Jolt at `c6703570`; see `methods/constraints-migration-step1.md` and `reports/2026-11-02-constraints-migration-definitions.md`.
  Step 1 was reviewed and is uncommitted, on top of Lean commit `5a48604`.
- The last full build failed in 17 modules; 11 are under `JoltConstraints/Completeness/`.
  Modules that depend on them were not built, so more failures may appear as these are fixed.
- Jolt's code: `/Users/ari.biswas/Work-with-A16z/jolt`, read with `git -C /Users/ari.biswas/Work-with-A16z/jolt show c6703570:<path>`.

## Goal

`lake build JoltConstraints.Completeness` succeeds.
The only `sorry`s left in completeness are the four already listed in `JoltConstraints/model_review.md` ("Proofs owed", Completeness), namely (01), (37), (38) and `HonestTrace.corrected_witness_params_ram_bounds`, plus the wrap lemmas of work items 6 and 7.
No other new `sorry`.

Work order: first fix every module that does not depend on a wrap case, then the wrap cases.

## Work

1. Failing modules from the step 1 report:
   `Completeness.Rs2EqRamWriteIfStore`, `Completeness.RightLookupEqRightInputOtherwise`, `Completeness.RightLookupAdd`, `Completeness.RamReadEqRamWriteIfLoad`, `Completeness.RamReadEqRdWriteIfLoad`, `Completeness.RamAddrEqRs1PlusImmIfLoadStore`, `Completeness.RightInstructionInputEqSelection`, `Completeness.Helpers.LookupWriteProofHelpers`, `Completeness.LeftLookupOperandEqInstructionRaf`, `Completeness.RightLookupOperandEqInstructionRaf`, `Completeness.Helpers.RamReadSelection`.
   Fix these, then every completeness module they unblock.
2. Classifier call sites, outline item 9.
   The three completeness callers of the old classifiers use `opcodeFlag_load_cases` or `opcodeFlag_store_cases` and handle the new loads and stores.
3. Constraint (01).
   Rename the theorem to `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` and its file to match, and state it against the new (01).
   Its body stays `sorry`: it is the existing (01) gap, false until a16z/jolt#1949 is fixed.
   Replace its docstring with this one, unchanged (Ari approved it on 2026-11-03):

   ```lean
   /-- Constraint (01) has the form
   `(Load t + Store t) · (RamAddress t - Rs1Value t - Imm t + LookupOutput t) = 0`.
   On a memory row, that is when the instruction at cycle `t` is LD, SD,
   `VirtualLoadB/H/W` or `VirtualStoreB/H/W`, `Load t + Store t = 1`.
   So (01) needs `RamAddress t = Rs1Value t + Imm t - LookupOutput t`.
   Each cell is a trace value cast into the field: `RamAddress t`, `Rs1Value t`
   and `LookupOutput t` are 64-bit values, and `Imm t` is the signed offset.
   The equation adds them in the field, but Jolt's tracer computed
   `RamAddress t` with 64-bit addition, which wraps.
   So the equation holds only when `rs1 + imm` does not wrap. For example,
   `ld x1, -16(x0)` gives `RamAddress t = 2^64 - 16`, but the right side is
   `0 + (-16) - 0 = -16`; they differ by `2^64`, and the constraint is not
   satisfied.
   Left as `sorry` until a16z/jolt#1949 is fixed.

   Rust, at `c6703570`:
   - (01): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
     (`RamAddrEqRs1PlusImmMinusLookupIfLoadStore`, row 0).
   - 64-bit address addition: `tracer/src/instruction/ld.rs` (`LD::exec`),
     `tracer/src/instruction/sd.rs` (`SD::exec`) and
     `tracer/src/instruction/floor_access.rs` (`addresses`), all `wrapping_add`.
   - The cells: `crates/jolt-witness/src/witnesses/ram.rs` (`RamAddress`),
     `registers.rs` (`Rs1Value`), `operands.rs` (`Imm`) and `lookups.rs` (`LookupOutput`). -/
   ```
   Update `Completeness/All.lean`, `Completeness.lean`, the (01) links in `constraints.md` and the (01) row in `model_review.md`.
4. Lookup entries, outline items 6 and 8.
   In `Completeness/Helpers/LookupEntryProofHelpers.lean`, retire `lookupEntryCorrect_AlignAddr`, `lookupEntryCorrect_HalfwordAlignment` and `lookupEntryCorrect_WordAlignment`, and the use of `jolt_virtual_align_addr_value64`.
   Prove the AddressOffset entries once, over the width, and derive B, H and W from it; update the dispatch.
5. Constraint (41), `RightLookupOperandEqInstructionRaf.lean`.
   Its old proof splits on every instruction and now hits the heartbeat limit at line 51.
   `RightLookupOperand` now reads the index's right half directly, so rewrite the proof for that definition; never raise the heartbeat limit.
6. Constraint (11), `RightLookupEqRightInputOtherwise.lean`.
   For rows without combined operands, (11) now needs the index's right half to equal the right instruction input.
   Prove that once, as a lemma over the index cases, and use it.
   On a ShiftData row it holds only when `rs2 + imm` does not wrap, and that is false for some honest runs (a16z/jolt#1949).
   Ari decided on 2026-11-03: no new premise.
   Put exactly that fact in one lemma whose body is `sorry`, stated for one row of an honest trace, as Ari approved on 2026-11-03:

   ```lean
   theorem HonestTrace.shiftData_address_noWrap
       (trace : HonestTrace joltInstance privateInputs) (t : Nat) (inBounds : t < trace.rows.size)
       {address : JoltISA.Src} {imm : BitVec 64}
       (shiftData : shiftDataAddress? trace.bytecode[trace.rows[t].rowIndex].instruction =
         some (address, imm)) :
       let sum := ((JoltISA.sourceValue address trace.rows[t].preState).toNat : Int) + imm.toInt
       0 ≤ sum ∧ sum < 2 ^ 64 := by
     sorry
   ```

   `shiftDataAddress?` is a new helper giving the `address` source and `imm` of `VirtualShiftDataB/H/W`, and `none` for every other instruction.
   Adjust only the Lean details needed to make it build, and keep its meaning.
   It replaces `shiftData_rightOperand_eq_input`, which is stated for all bitvectors and is false for every wrapping input; delete that lemma.
   Prove the field equality the (11) proof needs from the new lemma, use it only for the ShiftData case, and prove the rest of (11) from it.
   Use this docstring for the lemma, unchanged (Ari approved it):

   ```lean
   /-- Constraint (11) has the form
   `g · (RightLookupOperand t - RightInstructionInput t) = 0`,
   where `g = 1 - AddOperands - SubtractOperands - MultiplyOperands - Advice`.
   On a ShiftData row, that is when the instruction at cycle `t` is
   `VirtualShiftDataB`, `VirtualShiftDataH` or `VirtualShiftDataW`, `g = 1`.
   So (11) needs `RightLookupOperand t = RightInstructionInput t`.
   Jolt's prover sets `RightInstructionInput t = rs2 + imm` and
   `RightLookupOperand t = (rs2 + imm) mod 2^64`.
   When `rs2 + imm` wraps, for example `rs2 = 0` and `imm = -16`, the two differ
   by `2^64`, and the constraint is not satisfied.
   Left as `sorry` until a16z/jolt#1949 is fixed.

   Rust, at `c6703570`:
   - (11): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
     (`RightLookupEqRightInputOtherwise`).
   - ShiftData's flags, so `g = 1`: `crates/jolt-riscv/src/instructions/virt/shift_data_b.rs`
     (`jolt_instruction!`).
   - `RightInstructionInput = rs2 + imm`:
     `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs`
     (`LookupQuery::to_instruction_inputs`).
   - `RightLookupOperand` wrapped to 64 bits: `crates/jolt-lookup-tables/src/traits.rs`
     (`LookupQuery::to_lookup_operands`, `(y as u64) as u128`).
   - Both read by Jolt's prover in `crates/jolt-witness/src/witnesses/operands.rs`
     (`RightInstructionInput`, `RightLookupOperand`). -/
   ```

   Add the lemma to "Proofs owed" in `model_review.md`, next to (01), as false until #1949 is fixed.
7. Constraint (08), `RightLookupAdd.lean`, and any further case of the same wrap.
   On a floor row, (08) needs the right lookup operand `(rs1 + imm)` as a 128-bit word to equal `rs1 + imm` in the field; that fails when `rs1 + imm` is negative (a16z/jolt#1949).
   Ari decided on 2026-11-03 to treat it like (01) and (11): no new premise.
   Put exactly that fact in one lemma whose body is `sorry`, stated for one row of an honest trace, as Ari approved on 2026-11-03:

   ```lean
   theorem HonestTrace.floorAccess_address_nonneg
       (trace : HonestTrace joltInstance privateInputs) (t : Nat) (inBounds : t < trace.rows.size)
       {base : JoltISA.Src} {imm : BitVec 64}
       (floor : floorAccess? trace.bytecode[trace.rows[t].rowIndex].instruction =
         some (base, imm)) :
       0 ≤ ((JoltISA.sourceValue base trace.rows[t].preState).toNat : Int) + imm.toInt := by
     sorry
   ```

   `floorAccess?` is a new helper giving the `base` and `imm` of `VirtualLoadB/H/W` and `VirtualStoreB/H/W`, and `none` for every other instruction.
   Adjust only the Lean details needed to make it build, and keep its meaning.
   It replaces `floor_rightOperand_eq_inputs`, which is stated for all bitvectors and is false for every negative sum; delete that lemma.
   Prove the field equality the (08) proof needs from the new lemma, use it only for the six new rows, and prove the rest of (08) from it.
   Use this docstring for the lemma, unchanged (Ari approved it on 2026-11-03):

   ```lean
   /-- Constraint (08) has the form
   `AddOperands t · (RightLookupOperand t - LeftInstructionInput t - RightInstructionInput t) = 0`.
   When the instruction at cycle `t` is `VirtualLoadB/H/W` or `VirtualStoreB/H/W`,
   `AddOperands t = 1`.
   So (08) needs `RightLookupOperand t = LeftInstructionInput t + RightInstructionInput t`.
   Each cell is a trace value cast into the field: `LeftInstructionInput t` is
   the 64-bit `rs1`, `RightInstructionInput t` is the signed offset `imm`, and
   `RightLookupOperand t` is a 128-bit value.
   The equation adds them in the field, but Jolt's prover computed
   `RightLookupOperand t` as `rs1 + imm` modulo `2^128`.
   So the equation holds only when `rs1 + imm` is not negative. For example,
   `lb x1, -16(x0)` gives `RightLookupOperand t = 2^128 - 16`, but the right side
   is `0 + (-16) = -16`; they differ by `2^128`, and the constraint is not
   satisfied.
   Left as `sorry` until a16z/jolt#1949 is fixed.

   Rust, at `c6703570`:
   - (08): `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`RightLookupAdd`).
   - Flags of these instructions, so `AddOperands t = 1`:
     `crates/jolt-riscv/src/instructions/virt/{load,store}_{b,h,w}.rs` (`jolt_instruction!`).
   - Inputs `(rs1, imm)` and `RightLookupOperand = (rs1 as i128 + imm) as u128`:
     `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
     (`to_instruction_inputs`, `to_lookup_operands`).
   - Read by Jolt's prover in `crates/jolt-witness/src/witnesses/operands.rs`
     (`LeftInstructionInput`, `RightInstructionInput`, `RightLookupOperand`). -/
   ```

   For any further wrap case below, give its lemma a short docstring that states the fact and links #1949, and mark it as pending Ari's wording.
   If another honest-witness theorem fails only because an address sum `rs1 + imm` or `rs2 + imm` wraps below 0 or past `2^64`, handle it the same way without stopping, and list it in the report.
   Every such lemma is stated for one row of an honest trace, never for arbitrary bitvectors, and is used only in the case it covers.
8. `Soundness/Layer4/WordEntry.lean`, outline item 8.
   `Completeness/Helpers/LookupEntryProofHelpers.lean` imports it, and it still uses the retired `alignAddrTableEntry`, so the completeness root cannot build.
   Repair it as a proof repair under "Approved without asking", so that `JoltConstraints.Completeness` builds.
   Do not repair other soundness modules in this step.
   Add each such lemma to "Proofs owed" in `model_review.md`, as false until #1949 is fixed.

## Approved without asking

Ari has approved, in advance, any proof repair or helper change these modules need, when both of these hold:

- the completeness theorem's statement, `InLanguage`, the assumptions and the restrictions stay as they are, and each honest-witness theorem changes only where its constraint changed in step 1;
- every caller of a changed helper can still prove it from the premises it already has.

Make such changes without stopping, and list each one in the report.

## Stop and report to Ari

Do not stop at the first problem.
Leave a blocked module as it is, finish everything else, and then stop and report all blockers together.
A blocker is:

- An honest-witness theorem that looks false for some honest trace for a reason other than the address wrap of work item 7.
  Give the exact missing fact; do not add a premise or a `sorry`.
- A fix needs a change to a step 1 definition, to anything under `Soundness/` other than `Soundness/Layer4/WordEntry.lean`, or to `TracerAddressChecks`.
- A rule in "When stuck, discuss first" of `AGENTS.md` applies.

## Rules

`AGENTS.md` applies.
In addition:

- No `sorry` beyond the four listed above and the wrap lemmas of work items 6 and 7, and no `native_decide`, `decide +kernel` or `bv_decide`; never raise `maxHeartbeats`.
- Do not commit.
- Before writing a second proof that looks like an earlier one, extract the shared lemma (`AGENTS.md`, "Making proofs general").
- Give every new or changed declaration a docstring that defines its terms and gives a concrete example.
- List every proof that takes more than about ten seconds.

## Build

Check for a running Lake process (`pgrep -fl lake`), then build serially.
Work towards `lake build JoltConstraints.Completeness`.
At the end, run `lake build JoltConstraints` once and record every failing module with its first error; the soundness failures are expected and are step 3.

## Deliverables

1. The diff, uncommitted.
2. `JoltConstraints/constraints.md`: update the (01) links and any completeness checkbox this step changes.
3. A report, `reports/YYYY-MM-DD-constraints-migration-completeness.md`, one sentence per line, giving:
   - the date, the Jolt commits (`5def437f`, `c6703570`) and the Lean base commit `5a48604` with step 1 uncommitted;
   - every declaration changed, added or removed, with file and line;
   - every statement change;
   - the build commands and their results, and any proof slower than about ten seconds;
   - each failing module from the final full build, with its first error.

Then stop for review.
