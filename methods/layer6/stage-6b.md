# Layer 6, stage 6b: live-register steps for the remaining plain rows

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and the Part A section of `methods/layer6/stage-4a-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in `DivisionBlock.lean` and new division files under `Soundness/Layer6/`, and may use `PlainRow.lean`.
Edit only files under `Soundness/Layer5/` (including new files there) and `JoltConstraints.lean` (to import a new file).
Do not edit `PlainRow.lean`; connecting these steps into `plain_row_step_other` is the next stage.

## Why

`plain_row_step_other` (`Soundness/Layer6/PlainRow.lean`) appends one row of any plain kind (not LD, SD, VirtualHostIO, JAL or JALR) other than the twelve division kinds.
Inside an expansion only some registers agree, so each kind needs a step lemma over `RegisterAgreementOn`, as Part A did for the division kinds.

## The task

1. List every instruction kind that `PlainRow` admits, that expanded bytecode can contain, and that is not in `DivisionArithmeticRow`, with its Layer 5 step lemma.
   Put the list in the report.
2. Port each listed step lemma to `RegisterAgreementOn` as Part A did: its source registers must be live, and its destination joins the live set.
   The shared helpers are already general (`RegisterAgreementOn.read`, `.write`, `.noWrite`, `.registerInputs`, `.immediateInputs`, `registerWriteOn_step`), so most of each port passes liveness through.
   The families still on full agreement are in `AddressMasks`, `AssertionsAlignment`, `Auipc`, `BitwiseBinary`, `Fence`, `ImmediateArithmetic`, `ImmediateLogic`, `ImmediatePowerMask`, `ImmediateShift`, `LoadUpperImmediate`, `Movsign`, `RegisterComparison`, `RegisterShift`, `SetLessThanImmediate`, `WordArithmetic`, `XorImmediate` and `XorRotation`; check this list against step 1.
   Keep a full-agreement version only where a proof still uses it, derived from the general one, and delete the rest.
   Do not copy a proof per family.
3. Two plain kinds have no step lemma; write them in new Layer 5 files.
   - Branches (BEQ, BNE, BLT, BGE, BLTU, BGEU): both operands live, no write, the row executes successfully, and agreement holds on the same live set.
     Execution can fail only if Sail rejects the target; check that a canonical bytecode branch's target cannot fail Sail's alignment check, and if it can, stop and report the exact case.
   - `VirtualAdviceLoad` (a tape read): as `advice_step` (`Advice.lean`), the witness's written value is a 64-bit word `v`, executing with tape answer `v` (`execWithTapeAnswer`, `TapeSemantics.lean`) writes `v`, and the destination becomes live.
     Execution fails for a byte count other than 1, 2, 4 or 8; check that expanded bytecode never has one.
   Check both statements against "Before staging a statement" in `AGENTS.md` and against Jolt's tracer at the pin.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints`, and run the axiom audit on every changed or new step lemma (no new `sorryAx` unless you staged a lemma).
Write `methods/layer6/stage-6b-report.md` with the list from step 1, each changed statement (old and new), each new declaration (file and line), any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
