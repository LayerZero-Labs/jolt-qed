# Expansion recipes: T6

Date: 2026-11-12.
T6 finds no disagreement at a16z/jolt#2384 head `3cc6e7bd1`.
A new generator derives Jolt's built-in expansion recipe for each of the 102 source kinds that Lean's `SourceInstruction` models, from every decoded instruction word of the kind, including every branch on register identity.
`JoltBytecode/JoltISA/ExpansionsAutomated.lean` is now written by that generator, and the regenerated file equals the committed one apart from its header.
Lean proves that `SourceInstruction.expand` equals the generated recipe for every source instruction, natives and System instructions included.
A new CI job regenerates the files at the pinned commit, fails on any diff, and rebuilds the proofs.
Jolt's sampling generator `crates/jolt-lean-gen` is retired.

## Revisions

- jolt-qed: branch `track/t6-recipes`, cut from `inline/t2-decoder-sweep` at `5306348`.
- Jolt: a16z/jolt#2384 at `3cc6e7bd179900cfad6a052335c32ea1ef749536` (`3cc6e7bd1`), the commit the expansion-parity CI job checks, built with the cargo feature `zicsr-remaining`.
- Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

## What is generated

`scripts/expansion-parity/src/bin/expansion-recipes.rs` is a new binary in the T1 crate.
`scripts/expansion-parity/EXPANSION-RECIPES.md` describes the method; in short:

1. For each modelled kind, the binary encodes every instruction word of that kind (all 32 values of each register field the encoding has, every value of the immediate field, every CSR address, the AMO ordering bits), decodes it with Jolt's `decode_instruction`, and expands it through `expand_instruction_with_provider` with a fresh allocator, as T1 does.
   That is 243,245,059 words over the 102 kinds; the sweep takes about 20 seconds on eight cores.
2. It groups the words by which of `rd = x0`, `rs1 = x0`, `rs2 = x0`, `rd = rs1`, `rd = rs2`, `rs1 = rs2` hold, over the registers Lean's constructor carries; for the CSR forms also by CSR and by five-bit constant.
3. Within a group it keeps only what holds on every word: each output register is a fixed register or a source register; each immediate is a constant, the source immediate, or a function of the shift amount.
4. It builds the smallest decision tree over those predicates that fits all groups.

Every word's rows therefore equal its recipe at its operands; nothing is sampled.
All 102 kinds yield a recipe.
Every word decodes to its kind.
For the six CSR kinds, the decoder accepts every CSR address and Jolt's expander rejects all 25,128,960 words whose address is not one of the six CSRs Lean models; Lean's `SystemCSR` has no constructor for them, so the generated recipes cover exactly the CSRs Lean can express.

The generator writes three files:

| File | Contents |
| --- | --- |
| `JoltBytecode/JoltISA/ExpansionsAutomated.lean` | The 57 `*ProgramAuto` programs, in the model's existing format and order |
| `JoltConstraints/ExpansionGen/Generated.lean` | One recipe per kind, `genX : operands → Option ExpandedSource`, six shift-amount tables, and the dispatcher `ExpansionGen.expand` |
| `JoltConstraints/ExpansionGen/Equiv.lean` | `expand_x` per kind, the six table lemmas, and `expand_eq_generated : i.expand = ExpansionGen.expand i` |

`JoltConstraints/ExpansionGen/Tactic.lean` is handwritten: register lemmas (`isX0_eq_true`, `sameXReg_eq_true` and their negations), the tactic `recipe` that unfolds both sides, splits every `if`, substitutes register equations and closes each branch, and `bitvec_cases`, which enumerates a shift amount or a five-bit constant.
For `CSRRWI`, `CSRRSI` and `CSRRCI`, `Equiv.lean` proves one lemma per CSR: for each of the 32 constants it unfolds both sides, abstracts `isX0 rd` and closes both cases by `rfl`, because `simp` on the constant bit-vector arithmetic exceeds the default limits.
The proofs use no `native_decide`, `decide +kernel` or `bv_decide`, and raise no heartbeat or recursion limit.
`lake build JoltConstraints.ExpansionGen.Equiv` takes about a minute on a laptop.
`JoltAudit/Axioms.lean` now gates `ExpansionGen.expand_eq_generated`, which depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Branch structure Jolt has

The recipes show which register patterns each kind branches on:

- Every pure native kind (the R-type and I-type ALU kinds, `LUI`, `AUIPC`, `VirtualRev8W`) and every pure sequence kind (shifts, `MULH`, `MULHSU`, the divisions and remainders) branches on `rd = x0` only: a no-op `ADDI x0, x0, 0` native row when `rd = x0`.
- `JAL`, `JALR` and `LD` branch on `rd = x0` only: the destination becomes the first temporary `v40`.
- Loads, `LR`, the advice loads, `SC` and the atomics branch on `rd = x0` only, through the temporaries the expansion allocates.
- Branches, stores, `SD`, `FENCE`, `VirtualAssertEQ` and `VirtualHostIO` do not branch.
- `CSRRW` branches on `rd = x0` and `rd = rs1` for five CSRs, and on `rd = x0` and `rs1 = x0` for `mtvec`.
- `CSRRS` and `CSRRC` branch on `rd = x0` and `rs1 = x0`; `CSRRC` on all six CSRs and `CSRRS` on `mscratch`, `mcause` and `mtval` also branch on `rd = rs1`.
- `CSRRWI`, `CSRRSI` and `CSRRCI` branch on `rd = x0` and on the constant.

No builder branches on anything else, such as `rs1 = rs2`.
The sampling generator could not have seen the `rd = rs1` branches; the proofs now check the handwritten System programs against the derived recipes.

## Anything the format cannot express

Nothing at this pin.
The generator fails, naming the kind, register pattern and row, if a later Jolt adds a branch on something other than register identity, a register that is neither fixed nor a source register, or an immediate that is not a constant, the source immediate or a function of the shift amount.

## What stays handwritten

- The map from Jolt's source kind to Lean's constructor (the `specs` table of the binary; T1's `JoltTests/ExpansionParity/Source.lean` holds the same map).
- The fault class and alignment exception of memory rows, which Jolt's rows do not carry: atomics, `LR` and `SC` use `.amo`; stores, `SC` and atomics fault with `E_SAMO_Addr_Align`.
- The value of the `VirtualAdvice` row of a division or remainder, which is Lean's advice parameter `q`.
- The System programs in `JoltBytecode/JoltISA/Expansions/System.lean` and the native-row construction in `JoltConstraints/expansions.lean` stay as they are; `Equiv.lean` proves them equal to the generated recipes.

## Limits

- The recipes cover the operand values Jolt's decoder can produce.
  Lean's constructors also admit a few values no word decodes to, such as an odd 13-bit branch offset; the generated recipe extends to them by the same formula, and Lean's expansion agrees with it there, but Jolt never sees such an instruction.
- The generator trusts Jolt's decoder to produce the source rows; T2 checks the decoder against Lean separately.
