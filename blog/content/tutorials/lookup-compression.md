+++
title = "A lookup argument: compression"
date = 2026-10-04
weight = 40
draft = true

[taxonomies]
tutorials = ["Demo Series 2: Lookup Arguments"]
tags = ["lookup", "polynomials"]
+++

**Demo document 2 of 3** in the Lookup Arguments series.

One way to compare multisets is to map their values into a product. Given a challenge $\beta$, encode a value $x$ as $\beta + x$ and multiply the encodings:

$$
P_T(\beta) = \prod_{t \in T}(\beta + t).
$$

If the query and table products agree for a suitable challenge, that gives a compact check that the two multisets match. The actual protocol needs additional machinery to make this probabilistic check sound.
