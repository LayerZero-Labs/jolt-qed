# Jolt Qed: Formally Verifying The Jolt Zk-VM

This repository contains proofs written using the Lean theorem proving assistant, towards formally verifying the completeness and soundness of the [Jolt zk-VM](https://github.com/a16z/jolt).
The project is _still on-going_, and as Jolt is relatively complex, we logically decompose the task of formally verifying Jolt into the components shown below.
Blocks in green are complete. 
Blocks in yellow are in-progress and, greyed out boxes are not yet started.
Explicit details about each component, trust assumptions, and current progress can be found [here](https://randomwalks.xyz/blog/jolt-qed/). 
See [CONTRIBUTING](CONTRIBUTING.md) for information about how to contribute to this project.

```mermaid
flowchart LR
    A["Bytecode Expansion"] --> B["Jolt Constraints"] --> C["Jolt Sumchecks"] --> D["Jolt Reductions"] --> E["Commitment Scheme"]

    classDef complete fill:#22c55e,stroke:#15803d,stroke-width:2px,color:#ffffff
    classDef inprogress fill:#fef3c7,stroke:#d97706,stroke-width:3px,stroke-dasharray:8 4,color:#92400e
    classDef pending fill:#f3f4f6,stroke:#9ca3af,stroke-width:2px,color:#6b7280

    class A,B inprogress
    class C,D,E pending

```

## Main result

[`JoltConstraints/WholeRun/Top.lean`](JoltConstraints/WholeRun/Top.lean) proves that the Sail RISC-V model reproduces every run of Jolt's tracer up to its first EBREAK, and in particular every run behind an instance that Jolt's constraints accept.
The theorems hold under premises stated with them, and they check the constraints directly, not through Jolt's sumcheck-based verifier.
They cover both of Jolt's fields: BN254 and Akita's `p = 2^128 - 1780711455`, Jolt's production field since a16z/jolt#2403. `JoltField.akita` and `JoltField.bn254` prove that both fields meet the field premise, with primality checked by Pratt certificates. The field premise `JoltField` asks for characteristic above `2^128 - 2^64`, and below `2^128` the constraints include the canonical lookup-address check that Jolt's `akita` build enforces.
[What the whole-run theorems prove](docs/whole-run-theorem.md) states both theorems, every premise, and what they do not say.
Read it before citing the result.
[`docs/riscv-alignment.md`](docs/riscv-alignment.md) explains each modelling decision behind them.

## Status

The recorded Jolt pin is `c97e9300`, the merge of a16z/jolt#2250.
The system expansions, the decoder and the ELF loader (`decode_elf`) transcribe a later revision, a16z/jolt `c336a6da7`, the head of a16z/jolt#2384 (see [`docs/riscv-alignment.md`](docs/riscv-alignment.md), Sources).
`lake build JoltBytecode` and `lake build JoltConstraints` pass, and `JoltBytecode/` has no `sorry`.
The remaining `sorry`s are in completeness proofs under `JoltConstraints/Completeness/`.
None of them is used by the soundness or whole-run theorems, whose `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
See [the soundness plan](methods/soundness.md) and [proof obligations](JoltConstraints/model_review.md).

A self contained manuscript describing the efforts of formally verifying bytecode expansion is available [here](./jolt-qed.pdf)

To read the bytecode expansion proofs, start at [`JoltBytecode/Step/Instructions.lean`](JoltBytecode/Step/Instructions.lean).
For every RISC-V instruction except ECALL and EBREAK, its theorem `joltRun_eq_execute` proves that Jolt's expansion, projected to Sail's state by `System.systemProject`, agrees with Sail's `execute` of the matching instruction.
The theorem assumes the instruction's `equivAssumptions` and, for division and remainder, honest advice (`AdviceHonest`).
The other files in `JoltBytecode/Step/` lift these theorems, and separate ones for ECALL, to `try_step`, the function the Sail emulator calls once per instruction.
[`JoltBytecode/RiscvInstruction.lean`](JoltBytecode/RiscvInstruction.lean) defines the `RiscvInstruction` type and, in `equivAssumptions`, the assumptions each instruction's theorem makes.

## Trusted Reference Model and Provenance

`LeanRV64D/` contains the trusted RISC-V reference model used by these proofs.
It was generated from [`abiswas3`'s fork](https://github.com/abiswas3/sail-riscv)
of the official [`riscv/sail-riscv`](https://github.com/riscv/sail-riscv)
repository at `266473f8`, using the official
[`rems-project/sail`](https://github.com/rems-project/sail) compiler at `2ae2199f` with one patch.
The complete generation process is documented in
[Sail RISC-V Into Lean](https://randomwalks.xyz/blog/sail-to-lean/).
[`sail-import/PROVENANCE.toml`](sail-import/PROVENANCE.toml) pins the model commit, the compiler and the patches in `sail-import/patches/` that configure the model as Jolt's hart.
`scripts/regen-sail-model.sh` regenerates `LeanRV64D/` from those inputs, and `scripts/check-sail-model.sh`, which CI runs when the model or its inputs change, checks that the checked-in tree matches byte for byte.
The upstream
Sail compiler and Sail RISC-V model are distributed under the BSD 2-Clause
License. The complete notice is included in
[`LeanRV64D/LICENSE`](LeanRV64D/LICENSE).


## AI Usage And Miscellany

As is the case for most projects in present times, AI agents assisted us in writing several proofs.
We did not any use any particular skills or MCP servers so far (perhaps there are better ways to do this).
Our process so far has involved opening two panes, one with an editor equipped with a Lean Language Server (LSP), and the other pane with Codex or Claude.
The chats were free form.

The most frequently used pattern was the following.
A lot of the theorems in the bytecode expansion project are very similar. 
For instance the work done to prove equivalence of `LBU` and `LB` RISC-V instructions is nearly identical. 
They differ in the last step in the application of sign vs unsigned extension. 
In this case, we carefully prove `LB` with guiding comments, and make the proof easily readable (see `LB_main.lean` for example). 
Then, we tell the AI agent to complete the proof for `LBU` following the exact principles and style. 
It seemed to be able to close the theorems with very limited guidance. 
We still skim the proof for `LBU`, but do not read it as thoroughly.
This strategy has proven to be extremely valuable so far, and saved us a lot of time.

On the other hand, we found that agents were not as good at designing definitions from scratch (this could change as models improve, or if we used a better setup). 
It took a lot of back and forth, and iterations for the ISA to reach its current state.
So for the Jolt-ISA definition, almost all of it was written by hand, then the AI-agents was asked to do formatting, and check against the rust code. 
Current code and ISA comments also include agent-authored changes; the review and generality requirements are recorded in [AGENTS.md](AGENTS.md).
We found AI agents were particularly bad at writing clear documentation. 

Different proofs were written at different phases of the project.
This means that some theorems are simpler and easier to follow than others.
A successful build checks Lean proof terms against their statements; it does not establish that admitted cases are proved or that the model matches the target Jolt source.
The goal was always to first have a passing proof for the correct theorem statement.
Often we let an AI agent loose to close the theorem by whatever means necessary. 
Then, we explored the output and made proofs simpler, and more readable (akin to how one would proof things on paper, though this is not always possible).
This process shrunk the code base significantly, and led to greater re-use of theorems.
We would eventually like to do this for all proofs, but in the interest of time, we have not yet done this.
Contributions which make proofs shorter, more general and simple are **always** welcome.
