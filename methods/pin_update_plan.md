# Pin update: `8bbb2357` to `5def437f`, part 1 (audit only)

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` and `methods/model_update.md` (the record of the previous pin update) first.
This part changes no Lean file.
Another agent may be editing Lean files and `methods/soundness.md` in the same checkout at the same time; read them, but write only your report.
It finds every change in Jolt between the current pin and the new one that our model mirrors, says what the model must change, and stops for Ari's decision.

## The pins

- Current pin: `8bbb2357890928d8f83b00ca542879077c4d3d28`, recorded in `methods/model_update.md`, `methods/soundness.md` and `AGENTS.md`.
- New pin: a16z's main at `5def437f`, fetched into `/Users/ari.biswas/Work-with-A16z/jolt` on 2026-10-22.
  Read Jolt's files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show <commit>:<path>` and `git -C ... diff 8bbb2357 5def437f -- <path>`.
  The checked-out branch `rust-to-lean-second-round` holds Ari's own generator work; do not modify that checkout.
- The stopping rule currently cites a16z/jolt PR #2109 at head `d2995380`.
  The PR merged as `0249591a`; between `d2995380` and its final head `32eb430e` only tests and one doc comment changed.

## What to inventory

`git diff --stat 8bbb2357 5def437f` changes 226 files; most are dependency bumps and prover internals.
Classify every changed file under these paths, whether or not a Lean file cites it:
`tracer/`, `common/`, `jolt-sdk/`, `jolt-platform/`, `crates/jolt-program/`, `crates/jolt-riscv/`, `crates/jolt-claims/`, `crates/jolt-witness/`, `crates/jolt-verifier/`.
Then grep the Lean sources and `methods/`, `JoltConstraints/*.md` for every cited Jolt path, and classify any changed file found that way too.

Known changes that the model mirrors:
- `bc4bfb1f` "fix(program): decode VirtualHostIO without a destination register": VirtualHostIO now has no operands; both decoders reject a nonzero rd; its bytecode row names no destination, so no register changes.
  Our model has `VirtualHostIO (dst : Dst) (src : Src) (imm)` (`JoltBytecode/JoltISA/Instruction.lean:150`), rewrites an x0 destination to temporary 40 (`sideEffectingDst`, line 456), and assumes `HostCallRdZero` (`JoltConstraints/Soundness/Assumptions.lean:53`) for exactly the bug this commit fixes.
- `0249591a`: PR #2109 merged.
- `521e53f6` "fix(verifier): reject trace lengths below the PCS floor": changes the verifier's input validation (`validate_inputs`), which `InLanguage` uses, and bears on helper C's DANGER cases.

## Report

Write `methods/pin_update_report.md` with one row per changed file under the paths above: the file, the commit, whether the model mirrors it (and where, with Lean file and line), and the model change it needs, or "none" with the reason.
Then list the proposed model changes, grouped:
- changes to L (`InLanguage` and anything it uses, such as `validate_inputs`) or to the restrictions bundle; these need Ari's decision;
- changes to the instruction model, semantics, metadata, witness helpers or constraints;
- citation-only updates (line numbers moved, PR #2109 cited at its merge commit).
For each proposed change, name the Lean declarations and proofs it touches.
Say whether the generated expansions (`JoltBytecode/JoltISA/ExpansionsAutomated.lean`, produced by Ari's `jolt-lean-gen`) need regenerating, by checking the expansion sources (`crates/jolt-program/src/expand/`, `tracer/src/instruction/`) between the pins.

Change nothing.
Do not commit.
Then stop.
