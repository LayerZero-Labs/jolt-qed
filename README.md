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

    class A complete
    class B inprogress
    class C,D,E pending

```

A self contained manuscript describing the efforts of formally verifying bytecode expansion is available [here](./jolt-qed.pdf)

If you wanted to dig around the bytecode expansion source code.
[This file](JoltBytecode/RiscvInstruction.lean) serves as the main entry point for the bytecode expansion project.
It contains 3 large match blocks. 
Loosely, it says given a RISC-V instruction, here is 

1. The list of assumptions we make to prove equivalence for this instruction.
2. Here is the theorem statement we wish to prove.
3. Here is the proof for the above theorem statement. 

There were 67 expandable RISC-V instructions. 
Only 60 of them were proven. Details about why the remaining seven instructions were unprovable is given in Section 7 of the pre-print.

## Trusted Reference Model and Provenance

`LeanRV64D/` contains the trusted RISC-V reference model used by these proofs.
It was generated from [`abiswas3`'s fork](https://github.com/abiswas3/sail-riscv)
of the official [`riscv/sail-riscv`](https://github.com/riscv/sail-riscv)
repository, using [`abiswas3`'s fork](https://github.com/abiswas3/sail) of the
official [`rems-project/sail`](https://github.com/rems-project/sail) compiler.
The complete generation process is documented in
[Sail RISC-V Into Lean](https://randomwalks.xyz/blog/sail-to-lean/). The upstream
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
As an effort to enforce human eyes on all critical components of the code, all comments and documentation about the ISA are hand-written.
We found AI agents were particularly bad at writing clear documentation. 

This project was completed over a span of two and a half months, during which we learned a great deal about Lean. 
Different proofs were written at different phases.
This means that some theorems are simpler and easier to follow than others (though all pass, so this does not a security concern).
The goal was always to first have a passing proof for the correct theorem statement.
Often we let an AI agent loose to close the theorem by whatever means necessary. 
Then, we explored the output and made proofs simpler, and more readable (akin to how one would proof things on paper, though this is not always possible).
This process shrunk the code base significantly, and led to greater re-use of theorems.
We would eventually like to do this for all proofs, but in the interest of time, we have not yet done this.
Contributions which make proofs shorter, more general and simple are **always** welcome.
