+++
title = "Notes On Soundness"
date = 2026-09-29
draft = true
+++

## The statement

The statement is

$$x = (P, i, o, p)$$

- $P$ is the ELF file.
- $i$ is the input bytes.
- $o$ is the output bytes.
- $p$ is the panic flag.

If the program uses trusted advice, the statement also includes $c$, a commitment to the trusted advice.

The claim about $x$ is:

```text
Claim(x):  there are untrusted advice bytes u, and trusted advice bytes t matching c,
           such that running P with i, u and t stops, and at the end
               the bytes in the output region  = o    (trailing zeros ignored)
               the panic flag                  = p
```

- **Running** means running $P$ in Jolt's model of RISC-V, started the way Jolt starts it.
  Every register is 0, the program counter is the ELF's entry address, and $i$, $u$ and $t$ are in their memory regions.
- **Stops** means the run ends by jumping to itself, stores `1` at the termination word unless it panicked, and fits within the maximum trace length.

The claim is only about the output region and the panic flag at the end of the run.
It says nothing about the final registers, the final program counter, or the final memory from `0x80000000` up.

## The constraints

The witness $w$ is a set of tables.
Every constraint is an equation over the cells of $w$.

The statement $x$ never appears as a variable in a constraint.
It appears as fixed constants inside the constraints:

- $P$ gives the constants of the bytecode rows, and the program's initial memory.
- $i$ gives the initial memory of the input region, and part of the expected final memory of the I/O region.
- $o$ and $p$ give the rest of the expected final memory of the I/O region.

So there is one set of constraints for each statement.
Write $C_x(w)$ for "$w$ satisfies every constraint for $x$".

## Completeness

```text
Completeness:  for every run of P with i, u and t that stops with output o and panic flag p,
               the witness built from that run, w = Witness(run), satisfies C_x(w).
```

In words: if the claim holds, the honest witness passes the constraints.

## Soundness

```text
Soundness:     if some w satisfies C_x(w), then Claim(x) holds.
```

In words: no witness passes the constraints unless the claim is true.

## Toy example: addition by computation

A small arithmetic statement illustrates how a proof assistant checks a
mathematical claim. For every natural number $n$, adding zero on the right
leaves $n$ unchanged:

\[
  \forall n \in \mathbb{N},\quad n + 0 = n.
\]

In Lean, this theorem follows by reflexivity. The expression on the left
reduces to the expression on the right by unfolding natural-number addition:

```lean
theorem add_zero_right (n : Nat) : n + 0 = n := by
  rfl
```

The same computation proves a concrete instance. Natural-number addition
reduces by unfolding its second argument:

\[
  2 + 2 = \operatorname{succ}(2 + 1) = \operatorname{succ}(\operatorname{succ}(2 + 0)) = 4.
\]

Lean checks the result directly:

```lean
theorem two_plus_two : 2 + 2 = 4 := by
  rfl
```
