+++
title = "Simplifying a goal"
date = 2026-10-02
weight = 20
draft = true

[taxonomies]
tutorials = ["Demo Series 1: Lean Proofs"]
tags = ["Lean", "proofs"]
+++

**Demo document 2 of 2** in the Lean Proofs series.

Lean's simplifier uses known definitions and theorems to rewrite expressions. For example, it knows that adding zero on the right leaves a natural number unchanged:

$$
n + 0 = n.
$$

```lean
theorem add_zero_right' (n : Nat) : n + 0 = n := by
  simp
```

This proof uses `simp` instead of relying on definitional reduction with `rfl`. The result is the same proposition, proved by a tactic that can also simplify more involved expressions.
