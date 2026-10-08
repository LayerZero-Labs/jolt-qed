+++
title = "A lookup argument: the claim"
date = 2026-10-03
weight = 30
draft = true

[taxonomies]
tutorials = ["Demo Series 2: Lookup Arguments"]
tags = ["lookup", "proofs"]
+++

**Demo document 1 of 3** in the Lookup Arguments series.

A lookup claim says that every queried value occurs in a fixed table. For a table $T$ and query values $q_i$, the claim is:

$$
\forall i,\quad q_i \in T.
$$

This is a tiny Lean model of the statement:

```lean
def InTable (table : List Nat) (query : Nat) : Prop :=
  query ∈ table
```

The next documents sketch how a proof system can encode this claim and check it efficiently.
