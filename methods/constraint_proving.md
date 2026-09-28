# Method for proving constraint completeness

Use this workflow for each `sorry` in an honest-witness completeness theorem. The
goal is to establish that a witness produced from a Rust-accepted execution
satisfies the corresponding Jolt constraint. A Lean predicate matching a Rust
equation is only the starting point; it does not establish completeness.

## Vocabulary for source instructions and final rows

Use these terms consistently when comparing Rust and Lean:

- A **source instruction** is the original RISC-V instruction from the program.
- An **expansion** lowers a source RISC-V instruction that Jolt does not support
  directly into one or more Jolt-supported instructions. For example, Jolt
  expands `ECALL` into several final rows, ending with a `JALR`.
- A **rewrite** handles a native RISC-V instruction that Jolt supports
  directly, producing its final Jolt row. It may normalize the instruction:
  native `JAL x0, ...`, for example, is rewritten to use a temporary
  destination. Call the native path a rewrite even when the row is unchanged
  and even though Rust's pipeline also places it in `expandedBytecode`.
- A **final row** is one Jolt instruction after expansion or rewrite. The
  constraint and honest witness operate on these rows. When a final row is a
  `JAL` or `JALR`, say whether it came from a rewritten native instruction or
  was emitted inside an unsupported instruction's expansion.

Rust identifiers such as `expand_program` and `expandedBytecode` use
“expanded” for the entire pipeline. Do not let those implementation names
erase the distinction between an expansion and a native rewrite in the
analysis or in explanations to the user.

For control-flow checks, a rewritten native `JAL` or `JALR` is already the
only final row of its source instruction. The nontrivial question is whether
an expansion can emit `JAL` or `JALR` before its last row. While an expansion
is still running, its final rows share the same source (unexpanded) PC; the
next source PC is not selected between those rows. If a jump occurs early,
the next row can retain that old source PC even though the jump's lookup
output is its target. Check this case against Rust's actual expansion and
tracing paths before assuming a jump must be last.

## 1. Select and read one target

Pick an open completeness theorem from
[`constraints.md`](../JoltConstraints/constraints.md), working from easier
targets toward harder ones. Read the exact Lean theorem, its current premises,
the constraint predicate, the witness fields it uses, and their dependencies.
Check [`model_review.md`](../JoltConstraints/model_review.md) for prior findings,
but revalidate claims against the current source. Record the selected target
and what is already proved or admitted; do not count a theorem containing
`sorry` as closed.

## 2. Audit the Rust-to-Lean correspondence first

Inspect the **local Rust checkout** supplied by the user, currently
`$HOME/Work-with-A16z/jolt`. GitHub links are documentation pointers,
not the source scan. Record the local Rust commit and relevant worktree changes
so the comparison is reproducible.

Follow the value all the way from an accepted program through Rust execution,
trace construction, proof-trace conversion, and witness extraction to the
constraint. Record whether each relevant final row came from an expansion or a
native rewrite. Compare those steps with the Lean execution model, trace and
witness definitions, and predicate. Check the relevant boundaries: integer
wrapping versus field arithmetic, signed values, padding and domain sizes,
lookup tables, memory behavior, and any validity assumptions. Only investigate
boundaries relevant to this theorem; do not assume a similar-looking equation
is enough to establish correspondence.

If a translation mismatch or an uncertain mapping appears, **flag it and
discuss it with the user before treating the theorem as ready to prove**.
Present a small, concrete case showing what Rust does and what Lean does, and
identify which definition or assumption causes the difference. Work through
the proposed correction with the user until they are satisfied. They may
instead mark the constraint deferred. A Rust-accepted execution rejected by
Lean is a translation problem worth documenting and fixing; it is not by itself
a Jolt constraint bug. Do not silently change the model to make the proof pass.

## 3. Attempt the theorem as stated

Once the translation is satisfactory, try to prove the existing completeness
theorem with its existing premises. Prove the necessary intermediate lemmas
and use the actual honest-witness definitions. Check that any helper theorem
does not merely move the `sorry` or the same unproved obligation elsewhere.

Before declaring a blocker, inspect the proof inputs already carried by
[`JoltTraceRow`](../JoltConstraints/trace.lean) and
[`JoltTrace`](../JoltConstraints/trace.lean). For a row `trace.rows[i]`, use:

| Row field | Available fact |
| --- | --- |
| `rowIndex`, `validProgramRow` | The selected bytecode row and its `Valid` certificate. The separate Rust-generation proof for program validity may still be deferred. |
| `runtimeAdvice`, `compactImmediateFits` | The per-execution advice payload and signed-immediate bound checked during proof-trace conversion. |
| `preState`, `postState`, `executes` | Full states and successful `execInstr` execution of the selected final instruction **with its runtime advice**. Start here when a frame or state-transition fact appears missing. |
| `hostIOPreservesPC` | An explicit HostIO **PC-only** certificate. It does not state anything about `nextPC`. |
| `storeMemoryPresent`, `loadCaptureMatches` | Store old-word presence and the captured load-value agreement used by proof-trace conversion. |

For the whole trace, use these fields before introducing any new condition:

| Trace field | Available fact |
| --- | --- |
| `rows`, `assumptionOperands`, `allAssumptions` | The execution rows and each row's existing assumption bundle at `preState`. Check the exact conjunct and its operand domain in [`Bundles.lean`](../JoltBytecode/Bundles.lean). |
| `ramAccessAssumed` | Connects the bundle's `memoryWindows` to an `LD` or `SD` effective RAM address. It does **not** cover arbitrary HostIO byte addresses; the bundle's memory-window facts concern 8-byte accesses. |
| `sequenceLayout` | Source/expansion layout, including the current `addressAdvanceNoWrap` assumption. Check which property is actually needed. |
| `initialized`, `startsAtEntry`, `startsAtInitial` | Initial-state shape, first bytecode entry, and first row's prepared state. |
| `noEarlyNextPCChange` | The nextPC frame for a nonfinal expansion row. Its source-to-row justification is separate work. |
| `linked`, `successor` | Consecutive state preparation and the next row's index or source address after a final row. |

[`JoltTrace.Terminated`](../JoltConstraints/execution_conditions.lean) is a
separate theorem premise, not an automatic trace field. When present, it gives
a nonempty trace, a final source-instruction row, and Rust's repeated-PC
stopping condition. Do not infer termination for a trace prefix.

If a proof stalls, search the `JoltBytecode/` project before writing a new
assumption or re-proving ISA facts. Useful starting points are
[`JoltISA/Semantics.lean`](../JoltBytecode/JoltISA/Semantics.lean),
[`Assumptions.lean`](../JoltBytecode/Assumptions.lean),
[`Bundles.lean`](../JoltBytecode/Bundles.lean), and the
[`InstructionEquivalence/ProofSupport`](../JoltBytecode/InstructionEquivalence/ProofSupport/)
lemmas for registers, translation, and memory. Match every helper's exact
premises to the trace: for example, the successful byte-load lemmas in
[`Memory/Read.lean`](../JoltBytecode/InstructionEquivalence/ProofSupport/Memory/Read.lean)
need byte presence and 1-byte PMP/MMIO facts, which an `LD`/`SD` 8-byte
memory window does not supply for HostIO pointers.

For reusable frame facts, check
[`NextPCFrame.lean`](../JoltConstraints/Constraints/NextPCFrame.lean) and
[`SailByteReadFrame.lean`](../JoltConstraints/Constraints/SailByteReadFrame.lean).
The latter proves that Sail's successful byte-read pipeline leaves Sail state
unchanged under the existing machine-mode/MPRV assumptions, including when it
returns a memory fault. It carries those assumptions across all bytes of a
live HostIO call and derives the HostIO nextPC frame from `executes`. Constraint
(17) is the worked example in
[`NextUnexpandedPCUpdateOtherwise.lean`](../JoltConstraints/Constraints/NextUnexpandedPCUpdateOtherwise.lean).

**Never add a premise to a completeness theorem without the user's explicit
permission. NEVER.** This includes adding a condition to a bundled validity
predicate or otherwise narrowing the accepted traces so the theorem becomes
easy. Do not weaken the conclusion or change the constraint for that purpose
either. If a new premise seems necessary, explain precisely which executions
it excludes and whether Rust actually excludes them, then discuss it with the
user. An existing comment proposing a premise is not permission to add it.

If the proof closes, compile the affected Lean module and run relevant build
or regression checks. Verify that no new `sorry` or unjustified axiom was
introduced. Then update the checklist and review notes with the proved
theorem and the validation performed.

## 4. If the proof does not close, establish why

Look for the smallest concrete edge case. Compute the values of the **actual
honest witness** and substitute them into the exact constraint. Keep these
outcomes distinct:

- **Translation issue:** Rust accepts a trace but Lean rejects or represents
  it differently. Document both sides and work out the model fix with the
  user; defer the theorem while that is unresolved.
- **Rust completeness issue:** A valid program runs through Rust's tracer and
  proof-facing conversion, yet its extracted honest witness violates the Rust
  constraint. Give a reproducible counterexample and report it as a Jolt bug.
- **Proof gap:** The theorem has not been proved, but no counterexample or
  mismatch has been established. State the exact missing lemma or unresolved
  correspondence. Do not call proof difficulty evidence of a bug, and do not
  invent a counterexample.

For a counterexample, follow the style in [`bug-report/`](../bug-report/).
Specify the program and initial state; show what the Rust tracer does, whether
the program and trace are accepted by the relevant pipeline, and the concrete
witness extractor outputs. Evaluate the actual Rust constraint with those
values and identify the failing row or residual. State exactly which path was
run and which was not; a failing local R1CS row is not automatically a claim
about a completed end-to-end proof. Explain the corresponding Lean behavior
side by side. Save the reproducer and observations so another person can
check them.

Constraint (01) is an example: `ADDI x1, x0, -8; LD x2, 8(x1)` gives a Rust
load address of `0` by 64-bit wrapping, while the honest witness has
`Rs1Value = 2^64 - 8` and `Imm = 8`. The matching Rust and Lean constraint
has residual `-2^64` in the proof field. The
[report](../bug-report/ram-address-wrap.md) traces this through a valid ELF,
the tracer, proof-trace conversion, witness extraction, and the R1CS row. A
no-wrap premise would exclude that Rust-accepted execution, so it cannot be
added just to close the theorem. Its completeness theorem remains `sorry`
because the counterexample shows a Jolt bug in the current Rust behavior and
constraint; it is not a theorem awaiting only more proof tactics. Once Jolt
fixes the issue, inspect the updated local Rust code, rerun the reproducer,
recheck Rust-to-Lean correspondence, and then try the theorem again.

Record the final status in the relevant review notes: proved, translation
issue, Rust completeness issue, proof gap, or user-deferred. Include the
evidence and the next unresolved step. Do not count a deferred or bug-blocked
`sorry` as a proved completeness theorem.
