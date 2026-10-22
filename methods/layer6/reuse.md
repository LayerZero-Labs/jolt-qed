# What already exists for Layer 6

Before proving anything, look here and use what exists.
Every name below was checked in the code on 2026-10-22; check it again before relying on it, since files move.
Paths under `JoltBytecode/` and `JoltConstraints/` are relative to the repository root.

## Running a whole expansion

- `JoltISA.Program.Run` (`JoltBytecode/InstructionEquivalence/ProofSupport/ProgramComposition.lean`): a program retires from one state to another.
  `Program.Run.append` composes two runs; `Program.Run.append_inv` splits one.
- `execProgram_instr_run_retire` and `execProgram_instr_run_retire_inv` (`JoltBytecode/InstructionEquivalence/ProofSupport/Lemmas.lean`): a program run is its first row's run followed by the rest, in both directions.
- `execProgramWithTapeAnswers_cons` (`JoltConstraints/Soundness/Layer5/Program.lean`): the same for the relaxed, tape-answer semantics.
- `narrowAdviceProgram_exec` (`JoltConstraints/Soundness/Layer5/AdviceExpansion.lean`): a worked example of running a whole expansion under the relaxed semantics.
- `ExpandedSource.ofPureProgram` (`JoltConstraints/expansion_helpers.lean`): shifts, MULH, MULHSU and the eight divisions expand to a sequence of their generated program's rows, or to one no-op when `rd = x0`.

## Division

For each of DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW, in `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/<Name>.lean`:

- `<name>Program_concrete`: from a state whose `rs1` and `rs2` read successfully and `rd ≠ x0`, the program with the honest advice value runs to a state whose Sail part is `stateAfterWrite js.sail rd <honest result>`.
  The starting temporaries are arbitrary.
- `<name>Program_sound`: if the program runs with any advice `q`, then for DIV, DIVU and DIVW `q` is the honest value; for DIVUW, REM, REMU, REMW and REMUW the final Sail state is `stateAfterWrite js.sail rd <honest result>`.
- `virtual_advice_run` and `virtual_advice_run_ex` (`JoltBytecode/InstructionEquivalence/ProofSupport/InstructionLemmas/VirtualAdvice.lean`): one VirtualAdvice row writes its value to a virtual destination and leaves the Sail state unchanged.
- The honest values the tracer uses are `SourceInstruction.honestTracerAdvice` (`JoltConstraints/honest_trace.lean`), which match the `*Program_concrete` advice arguments.

These conclusions cover the Sail state only; frames for the device and the tape come from the frame lemmas below.

## Frames: what an instruction leaves unchanged

- `StatePreservation.Preserves` and `preservation_auto` (`JoltBytecode/InstructionEquivalence/ProofSupport/Preservation.lean`): prove that every successful run of a monadic step keeps a relation.
- `JoltIOSetupFrame.execInstr_rule` and `execProgram_rule` (`JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean`): every instruction and program keeps the device's layout, advice and inputs.
- `InstructionFrame.execInstr_rule` (`JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean`): a relation on device, tape and host state that survives Sail and virtual-register changes and device stores is kept by every instruction.
  It cannot express that PC, memory or registers are kept.
- `execWithTapeAnswer_rule_of_device_relation` (`JoltConstraints/Soundness/Layer5/TapeSemantics.lean`): the same for the relaxed semantics; only device stores change the device.

## Loads and stores

- `JoltISA.Mmu.load_doubleword_ram` and `store_doubleword_ram` (`JoltBytecode/InstructionEquivalence/ProofSupport/Memory/MmuJolt.lean`): an aligned access at or above `RAM_START_ADDRESS` reads or writes `ram_doubleword`.
- `load_doubleword_state` (same file): any successful doubleword load, RAM or device, leaves the state unchanged.
  `store_doubleword_regs`: any successful store leaves registers and virtual registers unchanged.
- Nothing in `JoltBytecode/` covers device addresses beyond these frames; device-memory loads and stores are new work.

## Jumps and branches

- `Natives.jalrNative_run` and `Natives.jalNative_run` (`JoltBytecode/InstructionEquivalence/Instructions/Natives/Jalr.lean`, `Jal.lean`): the full post-state of a JALR with an x-register base and of a JAL.
- `Projection.jump_to_of_aligned` (`JoltBytecode/InstructionEquivalence/ProofSupport/Projection.lean`): a taken branch's post-state.
- Layer 7 already proves the witness side of JAL, JALR and branch rows in `JoltConstraints/Soundness/Layer7/StallSuffix.lean`: `selected_jalr_lookup_target`, `selected_jalr_next_target`, `selected_jump_link_write_value`, and the private `stall_branch_table_decision`, `stall_branch_lookup_decision` and `tape_jalr_target`.
  Make a private lemma public where it is when you need it.

## Registers and runs

- `RegisterAgreement` and its helpers (`JoltConstraints/Soundness/Layer5/Registers.lean`): `.initial`, `.advance_pc`, `.read`, `.write`, `.noWrite`; `RegisterAgreementOn` is defined there too.
- `readSrc_xreg_run_of_read` (`JoltBytecode/InstructionEquivalence/ProofSupport/RegisterAccess.lean`) and `writeDst_run` (`NativeDispatch.lean`): reads and writes at the Sail level.
- `registerWrite_step` (`JoltConstraints/Soundness/Layer5/LookupWrite.lean`): the shared finisher of the register-writing step lemmas; the step lemmas for 77 row kinds are in `JoltConstraints/Soundness/Layer5/`.
- `withRuntimeAdvice_eq_of_noAdvice` and `runtimeAdvice_agrees_of_noAdvice` (`JoltConstraints/Soundness/Layer5/RuntimeAdvice.lean`): a row without advice ignores and records no advice.
- `untrusted_row_pc` and `untrusted_row_next_pc` (`Layer7/StallSuffix.lean`): every run row starts with PC at its source address and nextPC at that address plus its length.
- `honestTracerAdviceAtStepN_extract` and the `UntrustedAnswerRun.truncate` lemmas (`Layer7/TerminationStore.lean`): later rows do not change an earlier row's honest advice; cutting a run keeps it a run.

## Bytecode layout and selection

- `expand_program_layout` (`JoltConstraints/ProgramLayout.lean`), `expand_program_source_of_row` (`JoltConstraints/program_facts.lean`) and the `ExpansionRows` namespace (`JoltConstraints/trace_interface.lean`): where each source instruction's rows sit in the bytecode.
- `ExpansionFacts.expand_ok` and `expand_temps_ok` (`JoltConstraints/expansion_facts.lean`): every expansion passes the row checks and writes each temporary before reading it.
- `selected_entry`, `selected_next_of_remaining`, `selected_interior_predecessor`, `padding_persists` and `padding_from` (`JoltConstraints/Soundness/Layer6/BytecodePC.lean`): which slot the witness selects.
- The private `nonterminal_at_last_cycle_impossible`, `nonterminal_before_padding_impossible` and `last_row_terminal` (`Layer7/LastJump.lean`): an unfinished expansion never ends at the last cycle or before padding.

## Initial state

- `RegisterAgreement.initial` (`Layer5/Registers.lean`), `OrdinaryRamAgreement.initial` (`Layer5/RamAgreement.lean`), `initialRamWord_eq_ram_doubleword` (`Layer5/RamInitialization.lean`), `ramVal_initial_state` (`Soundness/Layer3/State.lean`) and `registersVal_initial_state` (`Soundness/Layer2/State.lean`).
- The private `context_initial_termination_zero` (`Layer7/TerminationStore.lean`): the witness's initial termination word is 0.
