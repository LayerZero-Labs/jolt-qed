+++
title = "A first Lean proof"
date = 2026-10-01
weight = 10
draft = true

[taxonomies]
tutorials = ["Demo Series 1: Lean Proofs"]
tags = ["Lean", "proofs"]
+++

This sample tutorial exercises the blog's code, math, and callout rendering. It uses a small arithmetic theorem so the proof is easy to read without needing the Jolt definitions first.

{{<callout title="How to use this sample" message="This is sample content for previewing the theme. Replace or remove it when you start the real tutorial."/>}}

## State the goal

Lean checks proofs against a precise statement. Here the goal says that adding zero to a natural number leaves it unchanged:

$$
\forall n \in \mathbb{N},\quad n + 0 = n.
$$

In Lean, we write the proposition directly:

```lean,linenos
theorem add_zero_right (n : Nat) : n + 0 = n := by
  rfl
```

The tactic `rfl` closes this goal because both sides reduce to the same expression by computation. For this definition of natural-number addition, adding zero on the right unfolds directly to `n`.

## Follow the computation

Natural numbers are built from zero and the successor operation. For example, `2` is notation for `Nat.succ (Nat.succ 0)`. Addition recursively processes its first argument, so `2 + 2` reduces to `4`:

$$
2 + 2 \quad\longrightarrow\quad 3 + 1 \quad\longrightarrow\quad 4 + 0 \quad\longrightarrow\quad 4.
$$

The same computation gives another tiny theorem:

```lean
theorem two_plus_two : 2 + 2 = 4 := by
  rfl
```

The `lean` fence gets syntax highlighting, and `,linenos` adds line numbers when a longer proof benefits from them. MathJax renders both the display equations above and inline expressions such as $n + 0 = n$.

## A small executable example

Code fences can use other supported languages too:

```rust
fn add_zero_right(n: u64) -> u64 {
    n + 0
}
```

This lesson is part of [Demo Series 1: Lean Proofs]({{ get_taxonomy_url(kind="tutorials", term="Demo Series 1: Lean Proofs") }}).
