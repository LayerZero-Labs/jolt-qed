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
