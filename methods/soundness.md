---
title : Plan For Deterministic Non Succinct Soundness
--- 

Resources to get up to speed can be found here:

1. The high level overview  of how to think about Jolt as a concept - [My blog post]:(https://randomwalks.xyz/blog/jolt-qed/01-jolt-why/) 
2. A brief overview of how we found bugs in Jolt (completeness bugs) - [ai generated notes](./constraint_proving.md).
3. Some known gaps in the modelling that will be fixed imminently. - [ai generates notes](../JoltConstraints/model_review.md).

NOTE: The blog/ is stale and does not contain anything meaningful. 

Always read these in detail before beginning work.
Having read this we will have some common vocabulary for talking about Soundness.

The idea of soundness is to prove the converse of the NP statement.
Now we will imagine that there is some witness that satisfies constraints. 
And we want to show that this will force the Jolt tracer to run every instruction correctly.
Before we go all formal, let us discuss why such a thing might be true. 
Well one reason is that the witness is bunch of tables with meaning. 
For a time step when the prover says the `IsLoad` table (the actual name might be different) is 1,
that is a claim that time step $t$ had a load instruction. 
Similarly, there are other arrays that say what was loaded, what was written etc. 
We have defined the witness type already in `../JoltConstraints/witness.lean`.
Now a constraint limits the possible values that can go into these witness tables.
Therefore it constraints the claims the prover can make about machine state at time $t$.
Of course the constraints do not reduce to a single witness. 
That would be ideal, but that would be inefficient. 
What is most important is the constraints being restrictive enough to only allow claims about machine state that essentially lock the prover to following each instructions semantics. 
This is what the essence of soundness is.


## Soundness Definition

What does Jolt mean when they say a proof system is sound. 
We will be extremely precise here.


## Plan

The theorem is `JoltInstance.soundness` in `../JoltConstraints/Soundness/soundness.lean`.
If a witness satisfies every constraint, the instance is in Jolt's language: for some
private inputs there is an honest trace whose outputs are the ones the instance claims.

We prove it bottom up, in layers. Layers 0 to 3 are algebra about one-hot vectors and
prefix sums; they say nothing about Jolt's instructions. Layer 5 is where the
constraints must force each instruction's semantics. A goal we cannot close there
names a value the constraints leave free, which is how we expect to find problems.

| Layer | What it proves | From |
|---|---|---|
| 0. Field to bits | A field value known to be a natural number below 2^64 determines that number, so an equation in the field between such values is an equation between 64-bit words. | `2^127 < ringChar F` |
| 1. Selection | (a) Each chunk of a selector is one-hot. (b) So the full bytecode selector is one-hot: each cycle `t` selects one bytecode row, `sel t`. (c) A value read from the bytecode at `t` is the bytecode's value at `sel t`. The same for the RAM and lookup selectors. | booleanity, Hamming weight, `oneHotFitsSetup` |
| 2. Registers | The register file at cycle `t` is `RegistersVal · t`. A read at `t` returns it; after cycle `t` only the destination register changes, to `RdWriteValue t`. | `RegistersValEqPrefixRdInc`, the register read and write constraints, Layer 1 |
| 3. RAM | The same for memory, from `RamVal`, the RAM selector and `RamInc`, with the address remapping. | the RAM constraints, Layer 1 |
| 4. Lookups | The lookup output at `t` is the selected table applied to the operands. Each table computes its operation; the completeness lemmas `lookupEntryCorrect_*` are equalities and can be reused. | the instruction read-raf constraints |
| 5. One step | For each Jolt instruction, by family as in completeness (ALU, load and store, jump and branch, assert, advice, virtual): the values at cycle `t` follow the instruction's semantics. | Layers 2 to 4 |
| 6. Control flow | `starts`, `linked`, `stops` and `runs_until_stop`. | the PC and sequence constraints |
| 7. The trace | The rows are the cycles before padding; their states come from Layers 2 and 3 and their advice from the advice rows. The instance fields (`expands`, `accepted`, `valid_inputs`, `initialized`) come from `ConstraintContext`. | all of the above |
| 8. Outputs | `matches_outputs`. | `RamOutputEqPublicIo`, Layer 3 |

### Done

- The one-hot chunk width is bounded by the verifier's Dory setup
  (`ConstraintContext.oneHotFitsSetup`). Layer 1 needs `2^chunkBits` below the
  field's characteristic, and nothing else in the model bounds the width, which the
  prover picks.

### Where we expect to get stuck

- SC.W and SC.D (Layer 5): the constraints allow the advice to report failure when
  the reservation holds; our language follows Jolt's tracer, which reports success.
  Waiting on a16z: `../bug-report/sc-forced-failure/issue.md`.
- The end of the run (Layers 6 and 8): the two cases under "Known not sound for this
  L" in `review_completeness_and_soundness.md`.
- The advice tape (Layer 7): `VirtualAdviceLen` reports the remaining bytes, so the
  tape we build must agree with every read along the run.

### First step

Layer 0, then Layer 1(a): one chunk of a selector is one-hot.
