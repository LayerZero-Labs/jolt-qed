/-!
# LR.D proof boundary

There is intentionally no `lrdProgram_eq_sail` theorem in this file.

The Rust-faithful Jolt expansion for `LR.D` is concrete:

1. write `rs1` into `reservation_d`;
2. write `rs1` into `reservation_w`;
3. run an ordinary `LD` into `rd`.

The generated Lean Sail semantics is not just an ordinary load. `LR.D` runs
`execute_LOADRES`, which performs the memory read and then calls
`load_reservation (bits_of_physaddr paddr) 8`.

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
Assuming `load_reservation p 8 s = .ok () s` would collapse Sail `LR.D` to an
ordinary `LD`, but that would be an external trust assumption and would not prove
the reservation behavior that Jolt models with virtual registers.

There is no theorem target in this file until Sail exposes a trustworthy
reservation-state contract.
-/

namespace LoadReservedFamily

end LoadReservedFamily
