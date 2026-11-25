/-!
# LR.D proof boundary

There is intentionally no `lrdProgram_eq_sail` theorem in this file.

The Rust-faithful Jolt expansion for `LR.D` is concrete:

1. write `rs1` into `reservation_d`;
2. write `rs1` into `reservation_w`;
3. run an ordinary `LD` into `rd`.

The generated Lean Sail semantics runs `execute_LOADRES`, which performs the
memory read and then calls `load_reservation (bits_of_physaddr paddr) 8`.
The Sail model holds the reservation in the registers `reservation_valid`,
`reservation_addr` and `reservation_width` (`model/sys/sys_reservation.sail`
after `sail-import/patches/sail-riscv-jolt-hart.patch`), so `load_reservation`
is an ordinary register update rather than an axiom.

The theorem relating those registers to Jolt's `reservation_w` and
`reservation_d` virtual registers is not stated yet; the policy it will use is
described in `docs/riscv-alignment.md`, section 3.
-/

namespace LoadReservedFamily

end LoadReservedFamily
