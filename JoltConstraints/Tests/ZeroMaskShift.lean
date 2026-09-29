import JoltBytecode.JoltISA.Values

set_option autoImplicit false

namespace ZeroMaskShiftChecks

-- Rust: tracer/src/instruction/virtual_srliw.rs, test zero_mask_outputs_zero (66f35559).
-- Before that fix the reference tracer overflowed and the x86 tracer wrote 1;
-- Lean's former `ctz 0 = 0` shift also gave 1. A zero mask now gives zero.
example : jolt_virtual_srliw_value 1 0 = 0 := rfl

end ZeroMaskShiftChecks
