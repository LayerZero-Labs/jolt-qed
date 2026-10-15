import JoltBytecode.JoltISA.Core

/-!
# SC.D proof boundary

There is intentionally no active `scdProgram_eq_sail` theorem in this file yet.

The Rust-faithful Jolt expansion for `SC.D` is not a primitive Sail-style
store-conditional step. At public pin `8bbb2357`, `scdProgramAuto` uses ordinary
Jolt rows:

1. require the target address to be in RAM;
2. compute `success = (reservation_d = rs1)` using XOR and SLTIU;
3. load the current memory value;
4. store `rs2` when `success = 1`, otherwise store the old memory value;
5. clear both reservation virtual registers;
6. write `rd = success XOR 1`.

No runtime advice supplies SC success. Rust source:
https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/expand/memory/scd.rs

The generated Lean Sail semantics for `SC.D` instead uses opaque reservation
hooks. The store-conditional memory path checks `match_reservation`, and the
instruction later clears reservation state through `cancel_reservation`.

Those hooks are axioms:

```
axiom match_reservation : Arch.pa -> Bool
axiom cancel_reservation : Unit -> SailM Unit
```

The Sail state has no visible reservation field in `SequentialState`, and the
`regs` map is keyed only by the generated architectural `Register` enum. There
is no `Register` key for LR/SC reservation state. Since `match_reservation` is a
pure function, it cannot inspect `regs` or any other Sail state field.

As a result, a closed equivalence theorem for `SC.D` is not currently provable.
It would require a trusted contract connecting Sail's opaque reservation hooks
to Jolt's concrete virtual-register reservation model and derived `success`
bit.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace StoreConditionalFamily

end StoreConditionalFamily

end
