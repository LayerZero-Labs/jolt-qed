import JoltBytecode.JoltISA.Core

set_option autoImplicit false

namespace JoltISA

-- Rust: [AdviceTape::read](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:51).
-- Rust: [VirtualAdviceLoad::exec](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/virtual_advice_load.rs:18).
-- Read 1, 2, 4, or 8 little-endian bytes and advance the cursor. Failure leaves
-- the tape unchanged. The bounds proof supplies every array access; no missing
-- byte is replaced by zero. Unused high bits of the resulting word are zero.
def readAdviceTape (tape : JoltAdviceTape) (byteCount : BitVec 64) :
    Option (BitVec 64 × JoltAdviceTape) :=
  let count := byteCount.toNat
  if count = 1 ∨ count = 2 ∨ count = 4 ∨ count = 8 then
    if available : tape.readPosition + count ≤ tape.bytes.size then
      let value := (List.finRange count).foldl (fun value offset =>
        let byte := getElem tape.bytes (tape.readPosition + offset.val)
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt tape.readPosition) available)
        value ||| (byte.zeroExtend 64 <<< (8 * offset.val))) 0
      some (value, { tape with readPosition := tape.readPosition + count })
    else none
  else none

end JoltISA
