# Layer 6, stage 6b report

## Audit and scope

This work follows the revised `methods/layer6/stage-6b.md` at commit `4f20e2d` and Part A of `methods/layer6/stage-4a-report.md`.
The `PlainRow` definition in `JoltConstraints/Soundness/Layer6/PlainRow.lean:40` excludes LD, SD, VirtualHostIO, JAL and JALR.
The `DivisionArithmeticRow` definition in that file at line 30 covers twelve additional kinds.
The remaining constructor inventory was checked against `JoltBytecode/JoltISA/Instruction.lean:64`, `SourceInstruction.expand` in `JoltConstraints/expansions.lean:15`, and its emitted Jolt ISA programs.
Of the 88 `Instr` constructors, 47 are reachable plain kinds outside `DivisionArithmeticRow` with a selected-row step, seven are reachable plain kinds without one, five are excluded by `PlainRow`, twelve are division kinds, and seventeen are not emitted by source expansion.

The plan correctly identifies the modules whose step lemmas still used full agreement.
The reachability check removes `ImmediatePowerMask` and `XorRotation` from this stage: none of their fifteen instruction constructors appears in `SourceInstruction.expand` or its emitted programs.
The other two non-emitted constructors are VirtualROTRI and VirtualROTRIW; `ExpansionFacts.immShiftOk` in `JoltConstraints/expansion_facts.lean:64` also rejects both.
No port of these two unused families remains in the working tree.

`ExpansionTempLiveness.readSources` in `JoltConstraints/expansion_temp_liveness.lean:18` lists both operands of each register shift.
`ExpansionLive` in `JoltConstraints/Soundness/Layer6/PrefixState.lean:82` makes a temporary live after an earlier row writes it.
The existing `unaryWord_step` in `JoltConstraints/Soundness/Layer5/UnaryWord.lean:228` adds its mask destination to the live set.
The ported `registerShift_step_after_producer` derives liveness of the shift's mask source directly from that destination, while requiring the other source to be live in the producer's postcondition.
The existing mask-shape premise and mask proofs are unchanged.
No branch-alignment or tape-load-width audit was performed.

## Reachable plain kinds and their Layer 5 steps

The table lists every reachable kind admitted by `PlainRow` and outside `DivisionArithmeticRow` that has a selected-row step.
Locations are relative to `JoltConstraints/Soundness/Layer5/`.

| Instruction kinds | Step declaration |
| --- | --- |
| ADD | `arithmetic_step`, `Arithmetic.lean:113` |
| ADDW, SUBW, MULW, MULHU | `wordArithmetic_step`, `WordArithmetic.lean:120` |
| ADDIW, VirtualMULI, VirtualMULIW | `immediateArithmetic_step`, `ImmediateArithmetic.lean:115` |
| AND, OR, ANDN | `bitwise_step`, `BitwiseBinary.lean:99` |
| ANDI, ORI, SLTI | `immediateLogic_step`, `ImmediateLogic.lean:99` |
| AUIPC | `auipc_step`, `Auipc.lean:62` |
| FENCE | `fence_step`, `Fence.lean:33` |
| LUI | `lui_step`, `LoadUpperImmediate.lean:60` |
| SLT, SLTU | `comparison_step`, `RegisterComparison.lean:131` |
| SLTIU | `sltiu_step`, `SetLessThanImmediate.lean:69` |
| XORI | `xori_step`, `XorImmediate.lean:64` |
| VirtualAlignAddr, VirtualWindowMaskB, VirtualWindowMaskH, VirtualWindowMaskW | `addressMask_step`, `AddressMasks.lean:158` |
| VirtualAssertEQ | `binaryAssertion_step`, `AssertionsBinary.lean:115` |
| VirtualAssertHalfwordAlignment, VirtualAssertWordAlignment | `alignmentAssertion_step`, `AssertionsAlignment.lean:110` |
| VirtualMovsign | `movsign_step`, `Movsign.lean:58` |
| VirtualPext, VirtualPextSigned, VirtualShiftDataB, VirtualShiftDataH, VirtualShiftDataW | `virtualBinary_step`, `VirtualBinary.lean:121` |
| VirtualPow2, VirtualPow2W, VirtualShiftRightBitmask, VirtualShiftRightBitmaskW, VirtualRev8W | `unaryWord_step`, `UnaryWord.lean:228` |
| VirtualSRLI, VirtualSRAI, VirtualSRLIW, VirtualSRAIW | `immediateShift_step`, `ImmediateShift.lean:165` |
| VirtualSRL, VirtualSRA, VirtualSRLW, VirtualSRAW | `registerShift_step`, `RegisterShift.lean:172` |

BEQ, BNE, BLT, BGE, BLTU, BGEU and VirtualAdviceLoad are the seven reachable plain kinds outside `DivisionArithmeticRow` with no selected-row Layer 5 step lemma.
`AdviceExpansion.adviceLoad_step` is a concrete-run helper, not a selected-row agreement step.
No step lemma for these seven kinds was written.

## Statement changes

All locations below are relative to `JoltConstraints/Soundness/Layer5/`, and all declarations are in `JoltConstraints.Soundness`.
In the tables, `full` means `RegisterAgreement witness t pre`, `on live` means `RegisterAgreementOn live witness t pre`, `src s` means `TraceWitness.sourceRegisterAddress s`, and `dst d` means `TraceWitness.destinationRegisterAddress d`.
`next full` and `next on P` mean the corresponding agreements at `⟨t.val + 1, next⟩` on the theorem's stated post-state.
`live + d` means the actual predicate `fun register => live register ∨ register = dst d`.
All encoded-value, successful-execution, final-cycle and other premises or conclusions are unchanged unless the row says otherwise.

| Public declaration | Location | Old statement | New statement |
| --- | --- | --- | --- |
| `addressMask_step` | `AddressMasks.lean:158` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `alignmentAssertion_step` | `AssertionsAlignment.lean:110` | `full → next full` | `on live`, `live (src base)` → `next on live` |
| `auipc_step` | `Auipc.lean:62` | `full → next full` | `on live → next on (live + destination)`; the PC premise remains |
| `bitwise_step` | `BitwiseBinary.lean:99` | `full → next full` | `on live`, both sources live → `next on (live + destination)` |
| `fence_step` | `Fence.lean:33` | `full → next full` | `on live → next on live`; RAM agreement and final RAM word remain |
| `immediateArithmetic_step` | `ImmediateArithmetic.lean:115` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `immediateLogic_step` | `ImmediateLogic.lean:99` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `immediateShift_step` | `ImmediateShift.lean:165` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `lui_step` | `LoadUpperImmediate.lean:60` | `full → next full` | `on live → next on (live + destination)` |
| `movsign_step` | `Movsign.lean:58` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `comparison_step` | `RegisterComparison.lean:131` | `full → next full` | `on live`, both sources live → `next on (live + destination)` |
| `registerShift_step` | `RegisterShift.lean:172` | `full`, mask shape → `next full` | `on live`, both sources live, same mask shape → `next on (live + destination)` |
| `registerShift_step_after_producer` | `RegisterShift.lean:293` | `full` at the mask producer's post-state → `next full` | `on (live + written mask)` at that post-state, with `lhs` live there → `next on ((live + written mask) + destination)`; mask-source liveness follows from the write |
| `sltiu_step` | `SetLessThanImmediate.lean:69` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |
| `wordArithmetic_step` | `WordArithmetic.lean:120` | `full → next full` | `on live`, both sources live → `next on (live + destination)` |
| `xori_step` | `XorImmediate.lean:64` | `full → next full` | `on live`, `live (src source)` → `next on (live + destination)` |

The private helper statements below retain their conclusions and change only the incoming agreement and source-liveness premises.
Here “same conclusion” means the original input equation, lookup value, or assertion predicate in that declaration.

| Private declaration | Location | Old statement | New statement |
| --- | --- | --- | --- |
| `addressMask_write_value` | `AddressMasks.lean:89` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `alignmentAssertion_passes` | `AssertionsAlignment.lean:68` | `full → same conclusion` | `on live`, `live (src base)` → same conclusion |
| `bitwise_write_value` | `BitwiseBinary.lean:64` | `full → same conclusion` | `on live`, both sources live → same conclusion |
| `immediateArithmetic_write_value` | `ImmediateArithmetic.lean:67` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `immediateLogic_write_value` | `ImmediateLogic.lean:63` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `immediateShift_write_value` | `ImmediateShift.lean:106` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `movsign_write_value` | `Movsign.lean:36` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `comparison_write_value` | `RegisterComparison.lean:89` | `full → same conclusion` | `on live`, both sources live → same conclusion |
| `registerShift_write_value` | `RegisterShift.lean:113` | `full`, mask shape → same conclusion | `on live`, both sources live, same mask shape → same conclusion |
| `sltiu_inputs` | `SetLessThanImmediate.lean:35` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `sltiu_write_value` | `SetLessThanImmediate.lean:46` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `wordArithmetic_write_value` | `WordArithmetic.lean:69` | `full → same conclusion` | `on live`, both sources live → same conclusion |
| `xori_inputs` | `XorImmediate.lean:36` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |
| `xori_write_value` | `XorImmediate.lean:47` | `full → same conclusion` | `on live`, `live (src source)` → same conclusion |

No declaration, definition, full-agreement wrapper, `sorry`, `bv_decide`, `native_decide`, `decide +kernel`, or proof limit was added.
No existing proved fact was replaced by `sorry`.
The fifteen existing family proofs were ported in place; no proof was copied per instruction kind.

## Validation

`lake env lean` passed on each of the fifteen modified Layer 5 files.
The final `lake build JoltConstraints` completed successfully with 8,810 jobs after the concurrent division edits settled.
`git diff --check` passed on the Layer 5 changes.
`#print axioms` on all sixteen changed public step theorems, including `registerShift_step_after_producer`, reported only `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
None of these theorems reaches `sorryAx` or a native bit-vector axiom.
No changed proof took more than about ten seconds to elaborate.
The aggregate build still reports pre-existing staged `sorry` declarations outside this port.
`PlainRow.lean`, the division files and `JoltConstraints.lean` were not edited for this task.
