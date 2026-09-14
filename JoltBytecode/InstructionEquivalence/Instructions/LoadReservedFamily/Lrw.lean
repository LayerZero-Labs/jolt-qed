/-!
# LR.W proof boundary

There is intentionally no `lrwProgram_eq_sail` theorem in this file.

The Rust-faithful Jolt expansion for `LR.W` is concrete:

1. write `rs1` into `reservation_w`;
2. clear `reservation_d`;
3. run the ordinary Jolt `LW` expansion.

The generated Lean Sail semantics is not just an ordinary word load. `LR.W` runs
`execute_LOADRES`, which performs the memory read and then calls
`load_reservation (bits_of_physaddr paddr) 4`.

That hook is an opaque axiom:

```
axiom load_reservation : Arch.pa -> Nat -> SailM Unit
```

The Sail state has no visible reservation field in `SequentialState`, and the
`regs` map is keyed only by the generated architectural `Register` enum. There
is no `Register` key for LR/SC reservation state. The related query hooks
`match_reservation` and `valid_reservation` are pure `Bool` functions, so they
cannot inspect the Sail state either.

As a result, this equivalence is not currently provable as a closed theorem.
Assuming `load_reservation p 4 s = .ok () s` would collapse Sail `LR.W` to an
ordinary `LW`, but that would be an external trust assumption and would not prove
the reservation behavior that Jolt models with virtual registers.

There is no theorem target in this file until Sail exposes a trustworthy
reservation-state contract.
-/

namespace LoadReservedFamily

end LoadReservedFamily
