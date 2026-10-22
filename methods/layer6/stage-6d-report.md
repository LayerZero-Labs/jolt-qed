# Layer 6, stage 6d report

Both staged division program statements moved unchanged and are proved.
No declaration was staged in this task.
No theorem gained a hypothesis or changed its conclusion.

## Plan audit

I checked all eight generated programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean` against `DivisionKind.program` in `JoltConstraints/Soundness/Layer6/DivisionDefs.lean`.
Each program has only the twelve `DivisionArithmeticRow` kinds in `JoltConstraints/Soundness/Layer6/PlainRow.lean:30`, and each destination is architectural or an instruction temporary 40–47.
The `rd = x0` branch is the architectural `ADDI x0, x0, 0` row and satisfies the same frame property.
The eight `*Program_sound` and `*Program_concrete` theorem statements in `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/` have the results and advice properties required by the plan.
`AllRegistersPresent` and `readable_of_present` in `JoltConstraints/execution_facts.lean:132,471` justify their source reads.
`SourceInstruction.honestTracerAdvice` in `JoltConstraints/honest_trace.lean:170` supplies the same eight advice arguments as the concrete program theorems, including DIVW's overflow advice and the zero-divisor cases.
I compared those formulas with the pinned `5def437f` `RISCVTrace::trace` implementations in `tracer/src/instruction/{div,divu,divw,divuw,rem,remu,remw,remuw}.rs`.
`JoltIOSetupFrame.Same` in `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:18` covers only layout, advice buffers, and inputs, so it cannot supply full device equality.
`StatePreservation.Preserves`, `preservation_auto`, and the actual `execInstr` cases in `JoltBytecode/JoltISA/Semantics.lean` support the specialized frame used here.
I found no incorrect plan claim.

## Declarations

Locations below are in `JoltConstraints/Soundness/Layer6/DivisionPrograms.lean` unless stated otherwise.
All listed declarations are proved, except the four private definitions, which introduce predicates.

| Declaration | Line | Role |
| --- | ---: | --- |
| `division_source_read` | 21 | Successful architectural read from register presence |
| `division_result_of_unique_advice` | 29 | Shared deterministic-run argument for DIV, DIVU, DIVW |
| `DivisionFrame` | 48 | Device, tape, host, and persistent virtual-register equality |
| `divisionFrame_refl`, `divisionFrame_trans`, `divisionFrame_sail` | 55, 58, 65 | Frame relation rules |
| `DivisionDestinationSafe`, `DivisionInstructionSafe`, `DivisionRows` | 71, 77, 95 | Destination, row, and instruction-list predicates |
| `divisionInstructionSafe_parts` | 83 | Extracts the row and destination obligations |
| `divisionFrame_read`, `divisionFrame_write`, `divisionFrame_instr` | 99, 112, 134 | Preservation under source reads, safe writes, and division rows |
| `divisionFrame_program` | 146 | One frame proof over a program's instruction list |
| `division_temporary_facts`, `division_program_rows` | 165, 177 | Checks temporary addresses and all eight generated lists |
| `division_program_result` | 194 | Moved from `DivisionDefs.lean`; proved, statement unchanged |
| `division_honest_concrete` | 226 | Matches tracer advice to all eight concrete runs |
| `division_program_honest` | 276 | Moved from `DivisionBlock.lean`; proved, statement unchanged |

`DivisionDefs.lean` only lost the moved `division_program_result` statement through my edit.
`DivisionBlock.lean:2` imports the new module, and its moved `division_program_honest` statement was removed there.
The existing `division_block` caller at `DivisionBlock.lean:76` and `DivisionFinalAgreement` at `DivisionDefs.lean:411` retain their statements.
Concurrent edits by another agent made `patchAdviceWord_runtime` and `runtime_advice_isSome` public in `DivisionDefs.lean`; those edits are not part of my change.
I did not edit `DivisionAppend.lean`, `PlainRow.lean`, `TopLevel.lean`, or Layer 7 files.

No new `bv_decide`, `native_decide`, `decide +kernel`, axiom declaration, or proof-limit change was added.
No final proof took more than about ten seconds; the final `DivisionPrograms` module built in 4.0 seconds.
An early direct simplification of the generated instruction lists hit the default heartbeat limit after about 11–12 seconds.
The final proof uses `DivisionRows` recursively and stays within the default limit.
Each proof body is under 60 lines.

## Validation

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,681 jobs before the concurrent `DivisionAppend.lean` edit resumed.
The first `lake build JoltConstraints` passed with 8,813 jobs.
The final aggregate attempt rebuilt `DivisionPrograms.lean` successfully but failed in the other agent's unfinished `DivisionAppend.lean` at lines 373, 381, 398, and 399; no Stage 6d file failed.
The build logs are `/private/tmp/stage6d-division-build.log`, `/private/tmp/stage6d-aggregate-build.log`, and `/private/tmp/stage6d-aggregate-build-final.log`.
`git diff --check` passed.

`#print axioms JoltInstance.division_program_result` and `#print axioms JoltInstance.division_program_honest` report no `sorryAx`.
`#print axioms JoltInstance.division_block` reports `sorryAx`, together with `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
A transitive constant-dependency check found exactly three reachable direct `sorryAx` users: `division_expansion_layout` in `DivisionDefs.lean:109`, `division_replay_rows` in `DivisionAppend.lean:613`, and `division_replay_complete` in `DivisionAppend.lean:640`.
Those are the remaining staged division gaps; the two moved program theorems have no reachable direct `sorryAx` user.
The axiom checks are in `/private/tmp/stage6d-axioms.log`, `/private/tmp/stage6d-program-axioms.log`, and `/private/tmp/stage6d-direct-sorries.log`.

No commit was made.
