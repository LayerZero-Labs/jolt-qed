import JoltBytecode.JoltISA.Core

/-!
# SC.D proof boundary

There is intentionally no active `scdProgram_eq_sail` theorem in this file yet.

The Rust-faithful Jolt expansion for `SC.D` is not a primitive Sail-style
store-conditional step. It uses ordinary Jolt rows:

1. read an advised `success` bit;
2. constrain `success <= 1`;
3. constrain `success * (reservation_d - rs1) = 0`;
4. load the current memory value;
5. store `rs2` when `success = 1`, otherwise store the old memory value;
6. clear both reservation virtual registers;
7. write `rd = success XOR 1`.

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
to Jolt's concrete virtual-register reservation model and advised `success`
bit.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace StoreConditionalFamily

end StoreConditionalFamily

end
