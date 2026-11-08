import JoltBytecode.JoltISA.Core

open LeanRV64D

/-!
# SC.W proof boundary

There is intentionally no active `scwProgram_eq_sail` theorem in this file yet.

The Rust-faithful Jolt expansion for `SC.W` is not a primitive Sail-style
store-conditional step. At public pin `8bbb2357`, `scwProgramAuto` uses ordinary
Jolt rows:

1. require the target address to be in RAM;
2. compute `success = (reservation_w = rs1)` using XOR and SLTIU;
3. spill `success` through `reservation_w` because the nested
   `LW` and `SW` expansions need the allocator temporaries free;
4. load the current word with the ordinary Jolt `LW` expansion;
5. compute `old + (rs2 - old) * success`;
6. spill that computed store value through `reservation_d`;
7. run the ordinary Jolt `SW` expansion;
8. write `rd = success XOR 1`;
9. clear both reservation virtual registers.

No runtime advice supplies SC success. Rust source:
https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/expand/memory/scw.rs

The generated Lean Sail semantics for `SC.W` checks `match_reservation` on the
store-conditional memory path and clears the reservation with
`cancel_reservation`. The Sail model holds the reservation in the registers
`reservation_valid`, `reservation_addr` and `reservation_width`
(`model/sys/sys_reservation.sail` after
`sail-import/patches/sail-riscv-jolt-hart.patch`): an SC succeeds when a
reservation is held at its exact address and the SC is no wider than the LR.
Both hooks are ordinary functions of the Sail state rather than axioms.

The theorem relating those registers to Jolt's `reservation_w` and
`reservation_d` virtual registers is not stated yet; the policy it will use is
described in `docs/riscv-alignment.md`, section 3.
-/

set_option linter.unusedVariables false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace StoreConditionalFamily

end StoreConditionalFamily

end
