+++
title = "A lookup argument: the check"
date = 2026-10-05
weight = 50
draft = true

[taxonomies]
tutorials = ["Demo Series 2: Lookup Arguments"]
tags = ["lookup", "Lean"]
+++

**Demo document 3 of 3** in the Lookup Arguments series.

The final step connects the compact algebraic check to the original membership claim. A proof establishes that the query multiset and the selected table values have the same encoding:

$$
\prod_i (\beta + q_i) = \prod_j (\beta + t_j).
$$

In a formalization, keep the two jobs separate: prove the algebraic identity in Lean, then prove that the identity implies the desired lookup property under the protocol's stated assumptions.
