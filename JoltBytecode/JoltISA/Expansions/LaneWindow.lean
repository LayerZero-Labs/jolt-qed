import JoltBytecode.JoltISA.Instruction

/-! Shared program fragments for the addressed lane of a containing doubleword.
These mirror `LaneWindow` in `crates/jolt-program/src/expand/memory/shared.rs`.
Each fragment continues with its caller's `tail` after successful retirement.
Offsets are decoded 64-bit immediates; an encoded 12-bit offset is sign-extended
before being passed to these fragments.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Width of the addressed lane, mirroring `AccessWidth` in
`crates/jolt-program/src/expand/memory/shared.rs`.
For example, `halfword` selects two bytes within the containing doubleword. -/
inductive AccessWidth where
  | byte
  | halfword
  | word
  deriving Repr

/-- Read the same register named by a destination operand.
For example, an architectural destination becomes an architectural source. -/
private def laneWindowSrc : Dst → Src
  | .vreg register => .vreg register
  | .xreg register => .xreg register

/-- Mirror `LaneWindow::open` in `crates/jolt-program/src/expand/memory/shared.rs`:
load the doubleword containing `base + offset` into `doubleword`, then write the
`width`-byte lane mask to `lane` before `tail`.
`faultClass` supplies the load classification and `fault` the alignment exception.
For example, word width at effective address 12 loads address 8 and masks its
upper four bytes. -/
def laneWindowOpen (width : AccessWidth) (doubleword lane : Dst)
    (base : Src) (offset : BitVec 64) (faultClass : LoadFaultClass)
    (fault : ExceptionType) (tail : Program) : Program :=
  let rows : Instr × Instr := match width with
    | .byte =>
        (.VirtualLoadB faultClass doubleword base offset fault,
         .VirtualWindowMaskB lane base offset)
    | .halfword =>
        (.VirtualLoadH faultClass doubleword base offset fault,
         .VirtualWindowMaskH lane base offset)
    | .word =>
        (.VirtualLoadW faultClass doubleword base offset fault,
         .VirtualWindowMaskW lane base offset)
  .instr rows.1 (.instr rows.2 tail)

/-- Mirror `LaneWindow::extract` in `crates/jolt-program/src/expand/memory/shared.rs`:
extract the bits selected by `lane` from `doubleword` into `destination`, then
continue with `tail`; `signed` selects sign extension instead of zero extension.
The lane mask already determines the width and position.
For example, extracting byte 0x80 with `signed = true` produces the 64-bit value -128.
-/
def laneWindowExtract (doubleword lane destination : Dst) (signed : Bool)
    (tail : Program) : Program :=
  .instr
    (if signed then
      .VirtualPextSigned destination (laneWindowSrc doubleword) (laneWindowSrc lane)
    else
      .VirtualPext destination (laneWindowSrc doubleword) (laneWindowSrc lane))
    tail

/-- Mirror `LaneWindow::merge` in `crates/jolt-program/src/expand/memory/shared.rs`:
clear the mask held in `lane` from `doubleword`, shift the low `width` bytes of
`value` into that lane using `base + offset`, add them, and store the doubleword
before `tail`; `fault` supplies the alignment exception.
This overwrites both `doubleword` and `lane`.
For example, byte width at effective address 9 places the low byte of `value`
in bits 8 through 15 of the doubleword at address 8. -/
def laneWindowMerge (width : AccessWidth) (doubleword lane : Dst)
    (base : Src) (offset : BitVec 64) (value : Src) (fault : ExceptionType)
    (tail : Program) : Program :=
  let dword := laneWindowSrc doubleword
  let mask := laneWindowSrc lane
  let rows : Instr × Instr := match width with
    | .byte =>
        (.VirtualShiftDataB lane value base offset,
         .VirtualStoreB base dword offset fault)
    | .halfword =>
        (.VirtualShiftDataH lane value base offset,
         .VirtualStoreH base dword offset fault)
    | .word =>
        (.VirtualShiftDataW lane value base offset,
         .VirtualStoreW base dword offset fault)
  .instr (.ANDN doubleword dword mask) <|
  .instr rows.1 <|
  .instr (.ADD doubleword dword mask) <|
  .instr rows.2 tail

end JoltISA
