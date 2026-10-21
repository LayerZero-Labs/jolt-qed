# Agent 5: porting the existing step lemmas to live-register agreement

Read `README.md` in this directory first, then `AGENTS.md`, then agent 1's Phase 0 report `methods/layer6/phase0_report.md`.
Start only after Ari has approved Phase 0, and only if Ari chose live-register agreement (option A in the report).
Work in a worktree under `/Users/ari.biswas/Lean/` on a branch `layer6-agent-5`, created from the commit named in the Phase 0 report.

## Your task

Agent 1 generalizes `RegisterAgreement` to `RegisterAgreementOn live` in Phase 0, with the full agreement as a special case, and generalizes its helper API.
You:

1. Port the existing step lemmas under `Soundness/Layer5/`, except LD, SD and the SC files (agent 4's), to take agreement on a live set.
   Each requires its source registers to be live, and returns agreement on that set with its destination added.
2. For each existing family, write the adapter to agent 1's `RowStep` interface: a `RowStep` lemma that applies the family's step lemma and does the bookkeeping.
   The bookkeeping:
   - extend the run by one row;
   - record PC, Rs1Value, Rs2Value and RamAddress;
   - carry RAM and device agreement over a row that does not access memory (`OrdinaryRamAgreement.noAccess`, `Layer5/RamAgreement.lean:102`, and agent 4's device version).
3. HostIO: port `host_call_selected_step` (`Layer5/HostCallRegisterFrame.lean:285`) so that temporary 40 is simply not live after it.
   Then delete the near-duplicate write lemmas in `HostCallRegisterFrame.lean` that the live form makes unnecessary.

## How to port without copying

The families share one proof pattern: the finisher `registerWrite_step` (`Layer5/LookupWrite.lean:65`) for register writes, and the assertion shape for asserts.
Port the finisher and the assertion pattern once, then each family by changing its signature and the source-liveness side conditions.
Do not duplicate a proof per family.
If a family's proof uses `RegisterAgreement` beyond the helper API, stop and report it, since agent 1 counted the API uses in Phase 0.

The families and their files are listed in agent 1's Phase 0 report.
They include `AddImmediate`, `ImmediateArithmetic`, `ImmediateLogic`, `XorImmediate`, `SetLessThanImmediate`, `LoadUpperImmediate`, `Auipc`, `Jal`, `Arithmetic`, `WordArithmetic`, `BitwiseBinary`, `Xor`, `RegisterComparison`, `XorRotation`, `VirtualBinary`, `UnaryWord`, `ImmediatePowerMask`, `AddressMasks`, `Movsign`, `ImmediateShift`, `RegisterShift`, `AssertionsBinary`, `AssertionsAlignment`, `AssertionMulOverflow`, `AssertLessThanEqual`, `Fence` and `HostCallRegisterFrame`.

AUIPC and JAL need the Sail PC to equal the row's address, which `PrefixState` provides (agent 1).
`RegisterShift`'s `registerShift_step_after_producer` needs the producer row's post-state.
Use `selected_registerShift_fed` (`Layer6/BytecodePC.lean:155`) and the previous row in the run.

## Files you own

The step lemma files listed above, and new adapter files under `Layer5/Adapters/`.
Not `Layer5/Registers.lean` (agent 1), and not LD, SD or SC (agent 4).

## Report

Per-declaration timings, the elaboration time of every file you changed before and after, any helper hypotheses you added, any new `bv_decide` use, and your branch's head commit.
