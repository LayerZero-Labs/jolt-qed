# Expansion recipes (T6)

`expansion-recipes` derives Jolt's built-in expansion recipe of every source
kind that Lean's `SourceInstruction` models, over symbolic register and
immediate parameters, and writes them as Lean:

| File | Contents |
| --- | --- |
| `JoltBytecode/JoltISA/ExpansionsAutomated.lean` | The 57 `*ProgramAuto` programs that `SourceInstruction.expand` and `joltRun` use, in the format the model has always used. |
| `JoltConstraints/ExpansionGen/Generated.lean` | One function per modelled kind (102 kinds, natives and System instructions included) from its operands to `Option ExpandedSource`, the shift-amount tables, and the dispatcher `ExpansionGen.expand`. |
| `JoltConstraints/ExpansionGen/Equiv.lean` | One theorem per kind that `SourceInstruction.expand` equals the generated recipe, the table lemmas, and `expand_eq_generated`. |

`JoltConstraints/ExpansionGen/Tactic.lean` is handwritten: it holds the register
lemmas and the tactics that the generated proofs call.

## How the generator derives a recipe

Jolt's expanders take concrete registers, so the generator treats them as a
black box and runs every input:

1. For each kind, it encodes every instruction word of the kind: all 32 values
   of each register field the encoding has and every value of its immediate
   field (4096 for I, S and B types, 2^20 for U and J types, every shift
   amount, every CSR address). It decodes each word with Jolt's
   `decode_instruction` and expands it with `expand_instruction_with_provider`
   and a fresh allocator, as `rows.rs` does for T1. Addresses and the
   compressed flag vary across words.
2. It groups the words by the truth values of the register-identity predicates
   over the registers that Lean's constructor carries: `rd = x0`, `rs1 = x0`,
   `rs2 = x0`, `rd = rs1`, `rd = rs2` and `rs1 = rs2`.
   For the CSR forms it also groups by the CSR and, for the immediate forms,
   by the five-bit constant.
3. Within a group it intersects, row by row, what each output field can be:
   a fixed register, or a source register that it equals on every word; for
   the immediate, a constant, the source immediate (modulo 2^64 for a
   `BitVec 64` field, since Jolt stores some immediates `u64`-wrapped), or a
   function of the shift amount (a table).
   The row kinds, the dispatch (one native row or a stamped sequence) and the
   operand presence must agree across the group.
4. It finds the smallest set of predicates on which the rows depend and builds
   a decision tree over them, merging the groups at each leaf.
   If no tree fits, the run fails and names the register pattern and row.

So every decoded word's rows equal its recipe instantiated at its operands; the
generator checks nothing by sampling.
It also checks that every word of a kind decodes, and that Jolt rejects every
CSR address outside the six that Lean models.

## What stays handwritten

Three rules of the Lean model are not in Jolt's rows, so the generator applies
them as fixed rules:

* The source kind to Lean constructor map (the `specs` table in
  `src/bin/expansion-recipes.rs`; T1's `JoltTests/ExpansionParity/Source.lean`
  holds the same map).
* The fault class (`.normal` or `.amo`) and the alignment exception of memory
  rows: atomics, LR and SC use `.amo`; stores, SC and atomics fault with
  `E_SAMO_Addr_Align`.
* The value of the `VirtualAdvice` row of a division or remainder is Lean's
  advice parameter `q`.

## Regenerate

Check out a16z/jolt at the pinned commit (`3cc6e7bd1`, the commit of the
expansion-parity job), then run from the repository root:

```bash
JOLT_DIR=/path/to/jolt EXPANSION_PARITY_FEATURES=zicsr-remaining scripts/expansion-parity/run-expansion-recipes.sh /tmp/expansion-recipes
```

The sweep takes about 20 seconds on eight cores.
Pass `--no-lean` to write only `WORK_DIR/out/recipes.json` and
`WORK_DIR/out/summary.json`.
Then rebuild the proofs:

```bash
lake build JoltConstraints.ExpansionGen.Equiv
```

The `expansion-recipes` workflow runs both steps and fails if the regenerated
files differ from the committed ones.

## Exit status

| Status | Meaning |
| --- | --- |
| 0 | Every recipe was derived and the files were written. |
| 1 | A recipe could not be derived; `summary.json` names the kind and the reason. No Lean is written. |
| 2 | The generator could not run (bad arguments, a Lean rendering it cannot express). |

## Retired generator

Before T6, `ExpansionsAutomated.lean` came from Jolt's `crates/jolt-lean-gen`,
which expanded each kind at one register assignment (`rd = 1`, `rs1 = 2`,
`rs2 = 3`) plus `rd = 0`. It could not see a branch on any other register
pattern, such as `rd = rs1`. That generator is retired: the file is now written
by `expansion-recipes`, which reproduces it byte for byte apart from the header.
