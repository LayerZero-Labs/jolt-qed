import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# Frame and footprint of straight-line inline rows (statement stage)

This module states the generic frame lemma of `docs/inline-precompiles.md`, section 5.4.
A *write set* names the virtual registers and architectural registers that a program's
rows may write, and the store rows of the program.
`Program.WritesWithin p ws` checks on the syntax of `p`, row by row, that

* every row is a straight-line row: no branch, `JAL`, `JALR`, `VirtualAdviceLoad` or
  `VirtualHostIO`;
* every row's destination is in the write set;
* every store row (`SD`, `VirtualStoreB/H/W`) is listed in the write set, and its base
  operand is an architectural register that no row writes.

The main theorem `frame_of_run` says that every successful run of such a program from any
start state satisfies `Frame ws s s'`.
`Frame` says that registers outside the write set keep their values, that memory changes
only at the footprint (the eight bytes of each store row, addressed from the base value in
`s`), that the device changes only by successful `JoltDevice.store?` steps at footprint
addresses, and that the advice tape, the host-I/O settings and the remaining Sail fields
are unchanged.
The lemma has no precondition on the start state.

The pool-reset clause of the spec is a separate per-program predicate,
`Program.ResetsPool`, with a static checker `Program.resetsPoolCheck`.

Every lemma is proved; the module has no `sorry`.
The per-row proofs run `execInstr` through `StatePreservation` with two relations:
`RowEffect` (Sail registers, virtual registers, tape, host settings) and, for store rows,
`MemStep` (memory and device at one doubleword).
The design note `reports/2026-11-11-inline-frame-statement.md` explains the statement.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Store slots and write sets -/

/-- How a store row addresses its doubleword.
`SD` stores at `ea = base + imm`; the floor stores `VirtualStoreB/H/W` store at the
doubleword containing `ea`, that is `ea &&& ~~~7`.
Example: `SD (.xreg x10) v 8` has kind `.dword`, and `VirtualStoreB (.xreg x10) v 3 f`
has kind `.floor`. -/
inductive StoreKind where
  | dword
  | floor
  deriving DecidableEq, Repr

/-- The syntactic shape of one store row: its base operand, its immediate and its
addressing kind. The stored value does not affect the footprint.
Example: the row `SD (.xreg x10) (.vreg vr50) 16` has slot `⟨.xreg x10, 16, .dword⟩`. -/
structure StoreSlot where
  base : Src
  imm : BitVec 64
  kind : StoreKind
  deriving Repr

/-- The doubleword address a store slot writes, with the base read in `s`.
It matches `execInstr`: `SD` passes `base + imm` to `Mmu.store_doubleword`, the floor
stores pass `(base + imm) &&& ~~~7`.
Example: if `x10` holds `0x80000000` in `s`, the slot `⟨.xreg x10, 8, .dword⟩` has address
`0x80000008`, and the slot `⟨.xreg x10, 3, .floor⟩` has address `0x80000000`. -/
def StoreSlot.address (slot : StoreSlot) (s : SailJoltState) : BitVec 64 :=
  let ea := sourceValue slot.base s + slot.imm
  match slot.kind with
  | .dword => ea
  | .floor => ea &&& ~~~(7 : BitVec 64)

/-- Whether a source operand is an architectural register.
Example: `(.xreg x10).isXReg = true` and `(.vreg vr40).isXReg = false`. -/
def _root_.JoltISA.Src.isXReg : Src → Bool
  | .xreg _ => true
  | .vreg _ => false

/-- What a program's rows may write.
For the in-scope inlines `vregs` lists the pool registers (`vr48..127`) and instruction
temporaries (`vr40..47`) the rows write, `xregs` is empty, and `stores` lists the store
rows.
Example: a program whose rows are `ADDI (.vreg vr48) (.xreg x0) 0` and
`SD (.xreg x10) (.vreg vr48) 0` has the write set
`⟨[vr48], [], [⟨.xreg x10, 0, .dword⟩]⟩`. -/
structure WriteSet where
  vregs : List VReg
  xregs : List regidx
  stores : List StoreSlot

namespace WriteSet

variable (ws : WriteSet)

/-- A destination is allowed when it is a listed virtual register, a listed
architectural register, or `x0` (a write to `x0` changes nothing).
Example: for `ws = ⟨[vr48], [], []⟩`, the destinations `.vreg vr48` and `.xreg x0` are
allowed, and `.vreg vr49` and `.xreg x10` are not. -/
def allowsDst : Dst → Bool
  | .vreg v => ws.vregs.contains v
  | .xreg r => isX0 r || ws.xregs.any (fun w => sameXReg w r)

/-- A source operand that no allowed row writes: an unlisted virtual register or an
unlisted architectural register.
Example: for `ws = ⟨[vr48], [], []⟩`, the sources `.xreg x10` and `.vreg vr32` are kept,
and `.vreg vr48` is not. -/
def keepsSrc : Src → Bool
  | .vreg v => !ws.vregs.contains v
  | .xreg r => !ws.xregs.any (fun w => sameXReg w r)

/-- Every store slot's base is an architectural register that no allowed row writes.
Requiring `.xreg` rules out bases such as `vr40`, the instruction temporary that Jolt's
`rd = x0` rewrite of secp256k1 inlines stores through: its value at entry is not an
operand of the source instruction.
Decision D7 of `docs/inline-precompiles.md` excludes those encodings.
At the generated-row pin `a6b6dc717` Jolt still accepts them; the open pull request
a16z/jolt#2414 adds the rejection upstream.
Example: `⟨[vr48], [], [⟨.xreg x10, 0, .dword⟩]⟩` passes, and
`⟨[vr40], [], [⟨.vreg vr40, 0, .dword⟩]⟩` fails. -/
def basesKept : Bool :=
  ws.stores.all (fun slot => slot.base.isXReg && ws.keepsSrc slot.base)

/-- The byte addresses the store rows may write, with bases read in `s`:
`address .. address + 7` for each slot.
The byte addresses are natural numbers, as in `Mmu.write_ram_doubleword` and
`Mmu.store_raw?`.
Example: with the single slot `⟨.xreg x10, 8, .dword⟩` and `x10 = 0x80000000` in `s`, the
footprint is the addresses `0x80000008 .. 0x8000000f`. -/
def Footprint (s : SailJoltState) (a : Nat) : Prop :=
  ∃ slot ∈ ws.stores, (slot.address s).toNat ≤ a ∧ a < (slot.address s).toNat + 8

end WriteSet

/-- The Sail register an architectural index names, or `none` for `x0`.
It matches the register `wX` writes and `rX` reads.
Example: `xRegister? x10 = some Register.x10` and `xRegister? x0 = none`. -/
def xRegister? : regidx → Option Register
  | .Regidx rs =>
    match rs.toNat with
    | 1 => some Register.x1 | 2 => some Register.x2 | 3 => some Register.x3
    | 4 => some Register.x4 | 5 => some Register.x5 | 6 => some Register.x6
    | 7 => some Register.x7 | 8 => some Register.x8 | 9 => some Register.x9
    | 10 => some Register.x10 | 11 => some Register.x11 | 12 => some Register.x12
    | 13 => some Register.x13 | 14 => some Register.x14 | 15 => some Register.x15
    | 16 => some Register.x16 | 17 => some Register.x17 | 18 => some Register.x18
    | 19 => some Register.x19 | 20 => some Register.x20 | 21 => some Register.x21
    | 22 => some Register.x22 | 23 => some Register.x23 | 24 => some Register.x24
    | 25 => some Register.x25 | 26 => some Register.x26 | 27 => some Register.x27
    | 28 => some Register.x28 | 29 => some Register.x29 | 30 => some Register.x30
    | 31 => some Register.x31
    | _ => none

/-- The Sail registers the write set allows rows to change: the registers of the listed
architectural indices.
Example: for `ws.xregs = [x5]` only `Register.x5` qualifies; for `ws.xregs = []` no
register does, so `PC`, `nextPC` and every CSR must keep their values. -/
def WriteSet.WritesSailReg (ws : WriteSet) (r : Register) : Prop :=
  ∃ i ∈ ws.xregs, xRegister? i = some r

/-- One successful device byte store at a footprint address below RAM.
`d'` is the device after `JoltDevice.store? d a v` writes byte `v` at address `a`.
Example: a store row whose footprint contains the output region's first address `a`
changes the device to `d'` with `JoltDevice.store? d a v = some d'`, which appends `v` to
the output buffer. -/
def DeviceStoreAt (footprint : Nat → Prop) (d d' : JoltDevice) : Prop :=
  ∃ a v, footprint a ∧ a < RAM_START_ADDRESS ∧ JoltDevice.store? d a v = some d'

end JoltISA.Inlines

namespace JoltISA

open Inlines

/-! ## The per-row static check -/

/-- Rows the frame lemma covers, decided per constructor.
The excluded rows change state the frame does not allow: branches, `JAL` and `JALR`
write the Sail PC or `nextPC`, `VirtualAdviceLoad` moves the advice-tape cursor, and
`VirtualHostIO` can change the tape, the device and the host settings.
Every other row changes at most its destination and, for a store row, memory or the
device at its own address. The match lists every constructor so that a new constructor
needs an explicit decision.
Example: `ADDI (.vreg vr48) (.xreg x0) 0` is a frame row, and `BEQ (.xreg x5) (.xreg x6) 8`
is not. -/
def Instr.isFrameRow : Instr → Bool
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _
  | .JAL _ _ | .JALR _ _ _ | .VirtualAdviceLoad _ _ | .VirtualHostIO => false
  | .ADDI _ _ _ | .ADDIW _ _ _ | .ANDI _ _ _ | .ORI _ _ _ | .XORI _ _ _
  | .SLTI _ _ _ | .SLTIU _ _ _ | .LUI _ _ | .AUIPC _ _ | .FENCE
  | .ADD _ _ _ | .ADDW _ _ _ | .SUB _ _ _ | .SUBW _ _ _ | .MUL _ _ _
  | .MULW _ _ _ | .MULHU _ _ _ | .ANDN _ _ _ | .VirtualMULI _ _ _
  | .VirtualMULIW _ _ _ | .VirtualPow2 _ _ _ | .VirtualPow2W _ _ _
  | .VirtualPow2I _ _ | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmask _ _ _ | .VirtualShiftRightBitmaskI _ _
  | .VirtualShiftRightBitmaskW _ _ _ | .VirtualSRLI _ _ _ | .VirtualSRAI _ _ _
  | .VirtualSRLIW _ _ _ | .VirtualSRAIW _ _ _ | .VirtualSRL _ _ _
  | .VirtualSRA _ _ _ | .VirtualSRLW _ _ _ | .VirtualSRAW _ _ _
  | .VirtualROTRI _ _ _ | .VirtualROTRIW _ _ _ | .VirtualRev8W _ _ _
  | .VirtualXORROT32 _ _ _ | .VirtualXORROT24 _ _ _ | .VirtualXORROT16 _ _ _
  | .VirtualXORROT63 _ _ _ | .VirtualXORROTL1 _ _ _
  | .VirtualXORROTW16 _ _ _ | .VirtualXORROTW12 _ _ _ | .VirtualXORROTW8 _ _ _
  | .VirtualXORROTW7 _ _ _ | .VirtualXORROTW22 _ _ _ | .VirtualXORROTW19 _ _ _
  | .VirtualXORROTW6 _ _ _ | .OR _ _ _ | .XOR _ _ _ | .AND _ _ _
  | .SLT _ _ _ | .SLTU _ _ _
  | .VirtualWindowMaskB _ _ _ | .VirtualWindowMaskH _ _ _
  | .VirtualWindowMaskW _ _ _ | .VirtualPext _ _ _ | .VirtualPextSigned _ _ _
  | .VirtualShiftDataB _ _ _ _ | .VirtualShiftDataH _ _ _ _ | .VirtualShiftDataW _ _ _ _
  | .VirtualSignExtendWord _ _ _ | .VirtualZeroExtendWord _ _ _
  | .VirtualMovsign _ _ _ | .VirtualAdvice _ _ _ | .VirtualNegateIf _ _ _
  | .VirtualLoadB _ _ _ _ _ | .VirtualLoadH _ _ _ _ _ | .VirtualLoadW _ _ _ _ _
  | .VirtualStoreB _ _ _ _ | .VirtualStoreH _ _ _ _ | .VirtualStoreW _ _ _ _
  | .LD _ _ _ _ | .SD _ _ _
  | .VirtualAssertEQ _ _ _ | .VirtualAssertValidDiv0 _ _ _
  | .VirtualAssertValidUnsignedRemainder _ _ _
  | .VirtualAssertMulUNoOverflow _ _ _ | .VirtualAssertLTE _ _ _ => true

/-- The store slot of a store row, and `none` for every other row.
Example: `(SD (.xreg x10) (.vreg vr50) 16).storeSlot? = some ⟨.xreg x10, 16, .dword⟩`, and
`(ADDI (.vreg vr48) (.xreg x0) 0).storeSlot? = none`. -/
def Instr.storeSlot? : Instr → Option StoreSlot
  | .SD base _ imm => some ⟨base, imm, .dword⟩
  | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
  | .VirtualStoreW base _ imm _ => some ⟨base, imm, .floor⟩
  | _ => none

/-- The per-row check: the row is a frame row and its destination, if any, is allowed.
Example: for `ws = ⟨[vr48], [], []⟩`, the row `ADDI (.vreg vr48) (.xreg x0) 0` passes, and
`ADDI (.vreg vr49) (.xreg x0) 0` fails. -/
def Instr.writesWithin (ws : WriteSet) (i : Instr) : Bool :=
  i.isFrameRow &&
    match i.destination? with
    | some d => ws.allowsDst d
    | none => true

/-- The rows of a program, up to its terminal result.
Example: `(Program.seq [i, j]).rows = [i, j]`. -/
def Program.rows : Program → List Instr
  | .done _ => []
  | .instr i rest => i :: rest.rows

/-- `Program.seq` and `Program.rows` are inverse on rows.
Example: `(Program.seq [i, j]).rows = [i, j]`. -/
@[simp] theorem Program.rows_seq (l : List Instr) : (Program.seq l).rows = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show x :: (Program.seq l).rows = x :: l
    rw [ih]

/-- The store slots of a program's store rows, in row order.
Example: the program with rows `ADDI (.vreg vr48) (.xreg x0) 0` and
`SD (.xreg x10) (.vreg vr48) 0` has store slots `[⟨.xreg x10, 0, .dword⟩]`. -/
def Program.storeSlots (p : Program) : List StoreSlot :=
  p.rows.filterMap Instr.storeSlot?

/-- The Boolean row check of a whole program: every row passes `Instr.writesWithin`.
Example: for `ws = ⟨[vr48], [], []⟩`, the program with the single row
`ADDI (.vreg vr48) (.xreg x0) 0` passes. -/
def Program.rowsWithin (ws : WriteSet) (p : Program) : Bool :=
  p.rows.all (Instr.writesWithin ws)

/-- The static condition of the frame lemma: every row passes `Instr.writesWithin`, every
store row is listed in the write set, and every listed store base is an architectural
register that no allowed row writes.
For generated rows, `p.storeSlots` reduces by `rfl` to the explicit list in `ws.stores`,
so the second conjunct is `List.Subset.refl _`; the first and third conjuncts reduce to
`true` by `rfl` even when the rows take free register parameters, because the checks
never compare two architectural registers when `ws.xregs = []`.
`decide` does not apply to such goals, since they contain free variables.
On a program of a few thousand rows a single `rfl` exceeds the default recursion depth,
so `FrameInstances` checks each generated chunk separately and assembles the chunks with
`Program.rowsWithin_seq_append` and `Program.storeSlots_seq_append`.
Example: `FrameInstances.sha256_writesWithin` proves this for the SHA-256 compression
rows and `sha256WriteSet`. -/
def Program.WritesWithin (p : Program) (ws : WriteSet) : Prop :=
  p.rowsWithin ws = true ∧ p.storeSlots ⊆ ws.stores ∧ ws.basesKept = true

/-- Chunked form of the row check, for generated programs built with `Program.seq`
from concatenated chunks.
Example: `(Program.seq (c₁ ++ c₂)).rowsWithin ws` reduces to the checks of the chunks
`c₁` and `c₂`, each of which `rfl` decides. -/
theorem Program.rowsWithin_seq_append (ws : WriteSet) (l₁ l₂ : List Instr) :
    (Program.seq (l₁ ++ l₂)).rowsWithin ws =
      ((Program.seq l₁).rowsWithin ws && (Program.seq l₂).rowsWithin ws) := by
  simp [Program.rowsWithin, List.all_append]

/-- Chunked form of `Program.storeSlots`: the slots of `l₁ ++ l₂` are those of `l₁`
followed by those of `l₂`.
Example: if chunk `c₁` has no store row, the slots of `c₁ ++ c₂` are the slots of `c₂`. -/
theorem Program.storeSlots_seq_append (l₁ l₂ : List Instr) :
    (Program.seq (l₁ ++ l₂)).storeSlots =
      (Program.seq l₁).storeSlots ++ (Program.seq l₂).storeSlots := by
  simp [Program.storeSlots, List.filterMap_append]

/-! ### Soundness of the Boolean check -/

/-- The meaning of an allowed destination, as a proposition.
Example: for `ws = ⟨[vr48], [], []⟩`, `ws.AllowsDst (.vreg vr48)` is `vr48 ∈ [vr48]`. -/
def Inlines.WriteSet.AllowsDst (ws : WriteSet) : Dst → Prop
  | .vreg v => v ∈ ws.vregs
  | .xreg r => isX0 r = true ∨ ∃ w ∈ ws.xregs, sameXReg w r = true

/-- Soundness and completeness of the Boolean destination check `WriteSet.allowsDst`.
Example: `ws.allowsDst (.vreg vr48) = true` exactly when `vr48 ∈ ws.vregs`. -/
theorem Inlines.WriteSet.allowsDst_iff (ws : WriteSet) (d : Dst) :
    ws.allowsDst d = true ↔ ws.AllowsDst d := by
  cases d <;> simp [WriteSet.allowsDst, WriteSet.AllowsDst]

/-- Soundness and completeness of the per-row check.
Example: `(ADDI (.vreg vr48) (.xreg x0) 0).writesWithin ws = true` exactly when the row is
a frame row (it is) and `vr48 ∈ ws.vregs`. -/
theorem Instr.writesWithin_iff (ws : WriteSet) (i : Instr) :
    i.writesWithin ws = true ↔
      i.isFrameRow = true ∧ ∀ d, i.destination? = some d → ws.AllowsDst d := by
  unfold Instr.writesWithin
  cases h : i.destination? with
  | none => simp
  | some d => simp [WriteSet.allowsDst_iff]

/-- Soundness and completeness of the program check.
Example: a program passes `rowsWithin ws` exactly when each of its rows passes
`Instr.writesWithin_iff`. -/
theorem Program.rowsWithin_iff (ws : WriteSet) (p : Program) :
    p.rowsWithin ws = true ↔
      ∀ i ∈ p.rows, i.isFrameRow = true ∧ ∀ d, i.destination? = some d → ws.AllowsDst d := by
  simp only [Program.rowsWithin, List.all_eq_true, Instr.writesWithin_iff]

/-- The row check is decidable, since it is a Boolean equation.
Example: `decide ((Program.seq [ADDI (.vreg vr48) (.xreg x0) 0]).rowsWithin ws = true)`
evaluates the check for a closed program. -/
instance (p : Program) (ws : WriteSet) : Decidable (p.rowsWithin ws = true) :=
  inferInstance

end JoltISA

namespace JoltISA.Inlines

/-! ## Architectural register indices -/

/-- The index of an architectural Sail register, `none` for every other register. -/
private def xIndex : Register → Option Nat
  | .x1 => some 1 | .x2 => some 2 | .x3 => some 3 | .x4 => some 4 | .x5 => some 5
  | .x6 => some 6 | .x7 => some 7 | .x8 => some 8 | .x9 => some 9 | .x10 => some 10
  | .x11 => some 11 | .x12 => some 12 | .x13 => some 13 | .x14 => some 14
  | .x15 => some 15 | .x16 => some 16 | .x17 => some 17 | .x18 => some 18
  | .x19 => some 19 | .x20 => some 20 | .x21 => some 21 | .x22 => some 22
  | .x23 => some 23 | .x24 => some 24 | .x25 => some 25 | .x26 => some 26
  | .x27 => some 27 | .x28 => some 28 | .x29 => some 29 | .x30 => some 30
  | .x31 => some 31
  | _ => none

private theorem xIndex_of_xRegister? {b : BitVec 5} {R : Register}
    (h : xRegister? (.Regidx b) = some R) : xIndex R = some b.toNat := by
  have hb : b.toNat < 32 := b.isLt
  unfold xRegister? at h
  dsimp only at h
  generalize b.toNat = n at h hb ⊢
  interval_cases n <;> simp at h <;> subst h <;> rfl

/-- Two indices that name the same Sail register are equal as indices.
Example: if `xRegister? i = some Register.x10` and `xRegister? r = some Register.x10`, then
`sameXReg i r = true`. -/
theorem sameXReg_of_xRegister?_eq {i r : regidx} {R : Register}
    (hi : xRegister? i = some R) (hr : xRegister? r = some R) : sameXReg i r = true := by
  obtain ⟨a⟩ := i
  obtain ⟨b⟩ := r
  have ha := xIndex_of_xRegister? hi
  have hb := xIndex_of_xRegister? hr
  rw [ha] at hb
  simp only [sameXReg, decide_eq_true_eq]
  exact BitVec.eq_of_toNat_eq (Option.some.inj hb)

/-- `sameXReg` is equality of indices.
Example: `sameXReg x10 x10 = true`, so `x10 = x10`. -/
theorem eq_of_sameXReg {w r : regidx} (h : sameXReg w r = true) : w = r := by
  obtain ⟨a⟩ := w
  obtain ⟨b⟩ := r
  simp only [sameXReg, decide_eq_true_eq] at h
  rw [h]

/-- The index `x0` names no Sail register.
Example: `xRegister? x0 = none`, since `wX` ignores writes to `x0`. -/
theorem xRegister?_of_isX0 {r : regidx} (h : isX0 r = true) : xRegister? r = none := by
  obtain ⟨b⟩ := r
  simp only [isX0, decide_eq_true_eq] at h
  simp [xRegister?, h]

private theorem get?_insert_of_ne {m : Std.ExtDHashMap Register RegisterType}
    {written read : Register} (v : RegisterType written) (h : written ≠ read) :
    (m.insert written v).get? read = m.get? read := by
  rw [Std.ExtDHashMap.get?_insert]
  simp [beq_false_of_ne h]

/-- An architectural register write leaves every Sail register other than its target
unchanged.
Example: `(wX_update_regs x5 v regs).get? Register.x6 = regs.get? Register.x6`, and
`wX_update_regs x0 v regs` changes no register. -/
theorem wX_update_regs_get?_of_ne (rd : regidx) (v : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType) {R : Register}
    (h : xRegister? rd ≠ some R) : (wX_update_regs rd v regs).get? R = regs.get? R := by
  obtain ⟨b⟩ := rd
  have hb : b.toNat < 32 := b.isLt
  unfold wX_update_regs
  unfold xRegister? at h
  dsimp only at h ⊢
  generalize b.toNat = n at h hb ⊢
  interval_cases n <;> (try simp only at h) <;>
    first | rfl | (apply get?_insert_of_ne; rintro rfl; exact h rfl)

/-! ## The frame relation -/

/-- The state relation every successful run of a `WritesWithin` program satisfies.

* `sailRegs`: every Sail register outside the write set keeps its value. This covers
  `x1..x31` (read by `rX_bits`, see `Frame.sourceValue_xreg_eq`), `PC`, `nextPC`, the
  CSRs and the reservation registers.
* `choiceState`, `cycleCount`, `sailOutput`: the remaining Sail fields are unchanged
  (`tags` has type `Unit`).
* `vregs`: every virtual register outside the write set keeps its value, in particular
  `vr32..39` and the pool registers the rows do not write.
* `mem`, `mem_present`, `mem_belowRam`: Sail memory changes only at footprint addresses,
  never loses a byte, and is unchanged below `RAM_START_ADDRESS`.
* `device`: the device changes only by successful `JoltDevice.store?` steps at footprint
  addresses below RAM. Corollaries: the I/O setup (`JoltIOSetupFrame.Same`) is unchanged
  and the panic flag only goes from `false` to `true`.
* `adviceTape`, `hostIO`: unchanged. `VirtualAdvice` writes its literal value and does not
  touch the tape; only the excluded `VirtualAdviceLoad` and `VirtualHostIO` touch it.

Example: for `ws = ⟨[vr48], [], [⟨.xreg x10, 0, .dword⟩]⟩` and a run of the rows
`ADDI (.vreg vr48) (.xreg x0) 0; SD (.xreg x10) (.vreg vr48) 0`, `Frame ws s s'` says that
only `vr48` and the eight bytes at the address `x10` holds in `s` may change. -/
structure Frame (ws : WriteSet) (s s' : SailJoltState) : Prop where
  sailRegs : ∀ r : Register, ¬ ws.WritesSailReg r → s'.sail.regs.get? r = s.sail.regs.get? r
  choiceState : s'.sail.choiceState = s.sail.choiceState
  cycleCount : s'.sail.cycleCount = s.sail.cycleCount
  sailOutput : s'.sail.sailOutput = s.sail.sailOutput
  vregs : ∀ v : VReg, v ∉ ws.vregs → s'.vregs v = s.vregs v
  mem : ∀ a : Nat, ¬ ws.Footprint s a → s'.sail.mem.get? a = s.sail.mem.get? a
  mem_present : ∀ a : Nat, (s.sail.mem.get? a).isSome → (s'.sail.mem.get? a).isSome
  mem_belowRam : ∀ a : Nat, a < RAM_START_ADDRESS → s'.sail.mem.get? a = s.sail.mem.get? a
  device : Relation.ReflTransGen (DeviceStoreAt (ws.Footprint s)) s.jolt_device s'.jolt_device
  adviceTape : s'.adviceTape = s.adviceTape
  hostIO : s'.hostIO = s.hostIO

namespace Frame

variable {ws : WriteSet}

/-- The empty run satisfies every frame.
Example: `Frame.refl ws s` is the frame of the program `.done RETIRE_SUCCESS`. -/
theorem refl (ws : WriteSet) (s : SailJoltState) : Frame ws s s where
  sailRegs _ _ := rfl
  choiceState := rfl
  cycleCount := rfl
  sailOutput := rfl
  vregs _ _ := rfl
  mem _ _ := rfl
  mem_present _ h := h
  mem_belowRam _ _ := rfl
  device := Relation.ReflTransGen.refl
  adviceTape := rfl
  hostIO := rfl

/-- An architectural register no allowed row writes keeps its value.
This is the `rX_bits` form of `sailRegs`: `sourceValue (.xreg r)` is exactly the value a
successful `readSrc (.xreg r)` (that is `rX_bits r`) returns.
Example: for `ws.xregs = []`, the base `x10` of every store row reads the same value at
the end of the run as at the start.
Proof: `keepsSrc` rules out every listed index `i` with `xRegister? i = xRegister? r`, so
`sailRegs` applies to the register `r` names; then case on the 32 values of `r`. -/
theorem sourceValue_xreg_eq {s s' : SailJoltState} (f : Frame ws s s') {r : regidx}
    (h : ws.keepsSrc (.xreg r) = true) :
    sourceValue (.xreg r) s' = sourceValue (.xreg r) s := by
  have key : ∀ R, xRegister? r = some R → s'.sail.regs.get? R = s.sail.regs.get? R := by
    intro R hR
    apply f.sailRegs
    rintro ⟨i, hi, hiR⟩
    have hs := sameXReg_of_xRegister?_eq hiR hR
    simp only [WriteSet.keepsSrc, Bool.not_eq_true', List.any_eq_false] at h
    exact h i hi (by simp [hs])
  obtain ⟨b⟩ := r
  have hb : b.toNat < 32 := b.isLt
  unfold xRegister? at key
  unfold sourceValue
  dsimp only at key ⊢
  generalize b.toNat = n at key hb ⊢
  interval_cases n <;> first | rfl | (simp only at key; simp only [key _ rfl])

/-- A kept source operand, virtual or architectural, reads the same value in both states.
Example: for `ws = ⟨[vr48], [], []⟩`, the source `.vreg vr32` keeps its value. -/
theorem sourceValue_eq_of_keepsSrc {s s' : SailJoltState} (f : Frame ws s s') {src : Src}
    (h : ws.keepsSrc src = true) : sourceValue src s' = sourceValue src s := by
  cases src with
  | vreg v =>
    have hv : v ∉ ws.vregs := by
      intro hm
      simp [WriteSet.keepsSrc, hm] at h
    exact f.vregs v hv
  | xreg r => exact f.sourceValue_xreg_eq h

/-- With kept bases, the footprint read in the end state equals the footprint read in
the start state.
Example: if no row writes `x10`, the slot `⟨.xreg x10, 0, .dword⟩` covers the same eight
bytes whether `x10` is read before or after the run. -/
theorem footprint_eq {s s' : SailJoltState} (f : Frame ws s s') (hk : ws.basesKept = true) :
    ws.Footprint s' = ws.Footprint s := by
  have haddr : ∀ slot ∈ ws.stores, slot.address s' = slot.address s := by
    intro slot hslot
    have hkeep : ws.keepsSrc slot.base = true := by
      have h := (List.all_eq_true.1 hk) slot hslot
      simp only [Bool.and_eq_true] at h
      exact h.2
    simp only [StoreSlot.address, f.sourceValue_eq_of_keepsSrc hkeep]
  funext a
  apply propext
  constructor
  · rintro ⟨slot, hs, h⟩
    exact ⟨slot, hs, by rwa [haddr slot hs] at h⟩
  · rintro ⟨slot, hs, h⟩
    exact ⟨slot, hs, by rwa [haddr slot hs]⟩

/-- Frames compose when no allowed row writes a store base.
Example: `frame_of_run` composes the frames of single rows with `trans`. -/
theorem trans {s m s' : SailJoltState} (f₁ : Frame ws s m) (f₂ : Frame ws m s')
    (hk : ws.basesKept = true) : Frame ws s s' := by
  have hfp := f₁.footprint_eq hk
  have hdev := f₂.device
  rw [hfp] at hdev
  exact {
    sailRegs := fun r hr => (f₂.sailRegs r hr).trans (f₁.sailRegs r hr)
    choiceState := f₂.choiceState.trans f₁.choiceState
    cycleCount := f₂.cycleCount.trans f₁.cycleCount
    sailOutput := f₂.sailOutput.trans f₁.sailOutput
    vregs := fun v hv => (f₂.vregs v hv).trans (f₁.vregs v hv)
    mem := fun a ha => (f₂.mem a (by rw [hfp]; exact ha)).trans (f₁.mem a ha)
    mem_present := fun a ha => f₂.mem_present a (f₁.mem_present a ha)
    mem_belowRam := fun a ha => (f₂.mem_belowRam a ha).trans (f₁.mem_belowRam a ha)
    device := f₁.device.trans hdev
    adviceTape := f₂.adviceTape.trans f₁.adviceTape
    hostIO := f₂.hostIO.trans f₁.hostIO }

/-- With no listed architectural register, the whole Sail register file is unchanged.
Example: every in-scope inline has `xregs = []`, so its runs keep `PC`, `x1..x31` and the
CSRs. -/
theorem sailRegs_eq_of_xregs_nil {s s' : SailJoltState} (f : Frame ws s s')
    (h : ws.xregs = []) : s'.sail.regs = s.sail.regs := by
  apply Std.ExtDHashMap.ext_get?
  intro r
  apply f.sailRegs r
  rintro ⟨i, hi, _⟩
  simp [h] at hi

/-- The I/O setup of the device (layout, inputs, advice) is unchanged.
Example: a store row that writes an output byte appends to `outputs` and keeps
`memory_layout` and `inputs`. -/
theorem device_same {s s' : SailJoltState} (f : Frame ws s s') :
    JoltIOSetupFrame.Same s.jolt_device s'.jolt_device := by
  have hd := f.device
  generalize s'.jolt_device = d at hd ⊢
  induction hd with
  | refl => exact JoltIOSetupFrame.Same.refl _
  | tail _ hstep ih =>
    obtain ⟨a, v, _, _, hs⟩ := hstep
    exact ih.trans (JoltIOSetupFrame.storeDeviceByte_same _ _ a v hs)

/-- One successful device byte store never clears the panic flag.
Example: a store to the panic address sets `panic := true`, and any other store keeps the
flag. -/
theorem store?_panic_mono {d d' : JoltDevice} {a : Nat} {v : BitVec 8}
    (h : JoltDevice.store? d a v = some d') : d.panic = true → d'.panic = true := by
  unfold JoltDevice.store? at h
  split_ifs at h <;> cases h <;> simp

/-- The panic flag never goes from `true` back to `false`.
Example: a run that starts in a panicked device ends in a panicked device. -/
theorem panic_mono {s s' : SailJoltState} (f : Frame ws s s') :
    s.jolt_device.panic = true → s'.jolt_device.panic = true := by
  have hd := f.device
  generalize s'.jolt_device = d at hd ⊢
  induction hd with
  | refl => exact id
  | tail _ hstep ih =>
    obtain ⟨a, v, _, _, hs⟩ := hstep
    exact fun h => store?_panic_mono hs (ih h)

/-- The output buffer stays inside the output region (`Related.outputs_size`), given that
it did at the start and that the layout has the output span `MemoryLayout.new` gives it
(`new_io_geometry` in `JoltConstraints/layout_facts.lean`).
Example: if the start device has 3 output bytes and `max_output_size = 4096`, the end
device has at most 4096 output bytes. -/
theorem outputs_size {s s' : SailJoltState} (f : Frame ws s s')
    (outputSpan : s.jolt_device.memory_layout.panic.toNat =
      s.jolt_device.memory_layout.output_start.toNat +
        s.jolt_device.memory_layout.max_output_size.toNat)
    (h : s.jolt_device.outputs.size ≤ s.jolt_device.memory_layout.max_output_size.toNat) :
    s'.jolt_device.outputs.size ≤ s'.jolt_device.memory_layout.max_output_size.toNat := by
  suffices H : s'.jolt_device.memory_layout = s.jolt_device.memory_layout ∧
      s'.jolt_device.outputs.size ≤ s.jolt_device.memory_layout.max_output_size.toNat by
    rw [H.1]
    exact H.2
  have hd := f.device
  generalize s'.jolt_device = d at hd ⊢
  induction hd with
  | refl => exact ⟨rfl, h⟩
  | tail _ hstep ih =>
    obtain ⟨a, v, _, _, hs⟩ := hstep
    exact JoltIOSetupFrame.storeDeviceByte_outputs_fit _ outputSpan _ _ a v ih.1 ih.2 hs

end Frame

/-! ## Per-row lemmas -/

/-! ### Reading operands -/

private theorem readReg_get? (register : Register) (sail after : SailState)
    (value : RegisterType register)
    (runs : (LeanRV64D.readReg register : SailM (RegisterType register)) sail = .ok value after) :
    sail.regs.get? register = some value := by
  unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg at runs
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure] at runs
  generalize lookup : sail.regs.get? register = stored at runs
  cases stored with
  | some storedValue =>
    cases runs
    rfl
  | none =>
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at runs
    cases runs

/-- A successful operand read leaves the state unchanged and returns `sourceValue`.
Example: if `x10` holds `0x80000000`, then `readSrc (.xreg x10)` returns `0x80000000`, and
`readSrc (.xreg x0)` returns `0`.
The proof follows `readSrc_value` in `JoltConstraints/execution_facts.lean`, which this
library cannot import. -/
theorem readSrc_run {src : Src} {s t : SailJoltState} {value : BitVec 64}
    (runs : readSrc src s = .ok value t) : t = s ∧ value = sourceValue src s := by
  cases src with
  | vreg register =>
    simp only [readSrc_vreg, readVReg_run] at runs
    cases runs
    exact ⟨rfl, rfl⟩
  | xreg register =>
    simp only [readSrc_xreg] at runs
    unfold liftSail at runs
    cases readResult : rX_bits register s.sail with
    | error failure sail =>
      rw [readResult] at runs
      cases runs
    | ok readValue sail =>
      have same := rX_bits_pure register s.sail readValue sail readResult
      subst same
      rw [readResult] at runs
      cases runs
      refine ⟨rfl, ?_⟩
      obtain ⟨index⟩ := register
      unfold rX_bits rX regval_from_reg at readResult
      simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
        bind, EStateM.bind, pure, EStateM.pure] at readResult
      unfold sourceValue
      have small : index.toNat < 32 := index.isLt
      generalize registerNumber : index.toNat = number at small readResult
      simp only [registerNumber]
      interval_cases number
      all_goals try simp only at readResult ⊢
      · cases readResult
        rfl
      all_goals
        split at readResult
        · rename_i storedValue _ readStored
          cases readResult
          rw [readReg_get? _ _ _ _ readStored]
          rfl
        · cases readResult

private theorem bind_ok {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s t : σ} {r : β} (h : (x >>= f) s = .ok r t) :
    ∃ a m, x s = .ok a m ∧ f a m = .ok r t := by
  simp only [bind, EStateM.bind] at h
  cases hx : x s with
  | error e m => rw [hx] at h; cases h
  | ok a m => rw [hx] at h; exact ⟨a, m, rfl, h⟩

private theorem loadDoubleword_keeps (a : BitVec 64) (s t : SailJoltState)
    (v : Result (BitVec 64) ExecutionResult) (h : Mmu.load_doubleword a s = .ok v t) : t = s := by
  simp only [Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

private theorem getArchPc_keeps (s t : SailJoltState) (v : BitVec 64)
    (h : liftSail (get_arch_pc ()) s = .ok v t) : t = s := by
  unfold liftSail at h
  cases hr : get_arch_pc () s.sail with
  | error e s1 => rw [hr] at h; cases h
  | ok a s1 =>
    rw [hr] at h
    cases h
    rw [readReg_pure _ _ _ _ hr]

/-! ### Registers, tape and host settings: `RowEffect` -/

/-- The effect of one row with destination `d` on everything except memory and the device:
the Sail fields other than `regs` and `mem` are unchanged, the Sail registers are unchanged
or updated by `wX_update_regs` at an architectural destination `d`, every virtual register
other than a virtual destination `d` is unchanged, and the tape and host settings are
unchanged.
Example: `RowEffect (some (.vreg vr48)) s t` allows `t.vregs vr48 ≠ s.vregs vr48` and
nothing else outside memory and the device. -/
def RowEffect (d : Option Dst) (s t : SailJoltState) : Prop :=
  t.sail.choiceState = s.sail.choiceState ∧
  t.sail.cycleCount = s.sail.cycleCount ∧
  t.sail.sailOutput = s.sail.sailOutput ∧
  (t.sail.regs = s.sail.regs ∨
    ∃ rd v, d = some (.xreg rd) ∧ t.sail.regs = wX_update_regs rd v s.sail.regs) ∧
  (∀ vr, d ≠ some (.vreg vr) → t.vregs vr = s.vregs vr) ∧
  t.adviceTape = s.adviceTape ∧ t.hostIO = s.hostIO

/-- `RowEffect` is reflexive.
Example: a row that throws before any write relates its state to itself. -/
theorem RowEffect.refl (d : Option Dst) (s : SailJoltState) : RowEffect d s s :=
  ⟨rfl, rfl, rfl, Or.inl rfl, fun _ _ => rfl, rfl, rfl⟩

/-- `RowEffect` is transitive: two writes to the same architectural destination compose
to the second write (`wX_update_regs_idem`).
Example: two successive writes to `x5` compose to the second one. -/
theorem RowEffect.trans {d : Option Dst} (s m t : SailJoltState) (h₁ : RowEffect d s m)
    (h₂ : RowEffect d m t) : RowEffect d s t := by
  obtain ⟨a₁, b₁, c₁, r₁, v₁, t₁, o₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, r₂, v₂, t₂, o₂⟩ := h₂
  refine ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, ?_, fun vr h => (v₂ vr h).trans (v₁ vr h),
    t₂.trans t₁, o₂.trans o₁⟩
  rcases r₁ with r₁ | ⟨rd, v, hd, r₁⟩ <;> rcases r₂ with r₂ | ⟨rd', v', hd', r₂⟩
  · exact Or.inl (r₂.trans r₁)
  · exact Or.inr ⟨rd', v', hd', by rw [r₂, r₁]⟩
  · exact Or.inr ⟨rd, v, hd, by rw [r₂, r₁]⟩
  · rw [hd] at hd'
    cases hd'
    exact Or.inr ⟨rd, v', hd, by rw [r₂, r₁, wX_update_regs_idem]⟩

open StatePreservation in
private theorem keeps_rowEffect {α : Type} (d : Option Dst) {m : JoltMonad α}
    (keeps : ∀ s t v, m s = .ok v t → t = s) : Preserves (RowEffect d) m := by
  intro s t v h
  rw [keeps s t v h]
  exact RowEffect.refl d s

open StatePreservation in
private theorem readSrc_rowEffect (d : Option Dst) (src : Src) :
    Preserves (RowEffect d) (readSrc src) :=
  keeps_rowEffect d fun _ _ _ h => (readSrc_run h).1

open StatePreservation in
private theorem writeDst_rowEffect (dst : Dst) (v : BitVec 64) :
    Preserves (RowEffect (some dst)) (writeDst dst v) := by
  cases dst with
  | vreg vr =>
    intro s t u h
    simp only [writeDst, writeVReg] at h
    split at h
    · cases h
    · cases h
      refine ⟨rfl, rfl, rfl, Or.inl rfl, fun r hr => ?_, rfl, rfl⟩
      have hne : r ≠ vr := fun e => hr (by rw [e])
      simp [hne]
  | xreg rd =>
    intro s t u h
    simp only [writeDst] at h
    unfold liftSail at h
    cases hw : wX_bits rd v s.sail with
    | error e s1 => rw [hw] at h; cases h
    | ok u' s1 =>
      rw [hw] at h
      cases h
      obtain ⟨s2, hs2, hregs⟩ := wX_regs_spec rd v s.sail
      obtain ⟨-, rfl⟩ := eStateM_deterministic hw hs2
      have hm := wX_eq_modify_regs rd v s.sail s1 hw
      refine ⟨?_, ?_, ?_, Or.inr ⟨rd, v, rfl, hregs⟩, fun _ _ => rfl, rfl, rfl⟩ <;>
        (dsimp only; rw [hm])

/-! ### Memory and device at one doubleword: `MemStep` -/

/-- A step that changes only Sail memory and the device, at the addresses `F`: memory changes
only at `F`, never loses a byte, and is unchanged below RAM, and the device changes only by
`DeviceStoreAt F` steps.
Example: a successful `Mmu.store_doubleword addr v` is a `MemStep` for the eight addresses
`addr .. addr + 7` (`storeDoubleword_memStep`). -/
structure MemStep (F : Nat → Prop) (s t : SailJoltState) : Prop where
  regs : t.sail.regs = s.sail.regs
  choiceState : t.sail.choiceState = s.sail.choiceState
  cycleCount : t.sail.cycleCount = s.sail.cycleCount
  sailOutput : t.sail.sailOutput = s.sail.sailOutput
  vregs : t.vregs = s.vregs
  adviceTape : t.adviceTape = s.adviceTape
  hostIO : t.hostIO = s.hostIO
  mem : ∀ a, ¬ F a → t.sail.mem.get? a = s.sail.mem.get? a
  present : ∀ a, (s.sail.mem.get? a).isSome → (t.sail.mem.get? a).isSome
  belowRam : ∀ a, a < RAM_START_ADDRESS → t.sail.mem.get? a = s.sail.mem.get? a
  device : Relation.ReflTransGen (DeviceStoreAt F) s.jolt_device t.jolt_device

/-- `MemStep` is reflexive.
Example: a store that fails leaves the state unchanged, which is a `MemStep`. -/
theorem MemStep.refl (F : Nat → Prop) (s : SailJoltState) : MemStep F s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => h, fun _ _ => rfl,
    Relation.ReflTransGen.refl⟩

/-- `MemStep` is transitive for a fixed address set.
Example: the eight byte stores of a device doubleword store compose. -/
theorem MemStep.trans {F : Nat → Prop} (s m t : SailJoltState) (h₁ : MemStep F s m)
    (h₂ : MemStep F m t) : MemStep F s t :=
  ⟨h₂.regs.trans h₁.regs, h₂.choiceState.trans h₁.choiceState,
    h₂.cycleCount.trans h₁.cycleCount, h₂.sailOutput.trans h₁.sailOutput,
    h₂.vregs.trans h₁.vregs, h₂.adviceTape.trans h₁.adviceTape, h₂.hostIO.trans h₁.hostIO,
    fun a ha => (h₂.mem a ha).trans (h₁.mem a ha),
    fun a ha => h₂.present a (h₁.present a ha),
    fun a ha => (h₂.belowRam a ha).trans (h₁.belowRam a ha),
    h₁.device.trans h₂.device⟩

/-- A `MemStep` at `F` is a `MemStep` at every larger address set.
Example: a store at one slot's doubleword is a `MemStep` at the footprint of the write set. -/
theorem MemStep.mono {F G : Nat → Prop} (hFG : ∀ a, F a → G a) {s t : SailJoltState}
    (h : MemStep F s t) : MemStep G s t :=
  { h with
    mem := fun a ha => h.mem a (fun hf => ha (hFG a hf))
    device := Relation.ReflTransGen.mono (fun _ _ hs => by
      obtain ⟨a, v, hf, hl, hs⟩ := hs
      exact ⟨a, v, hFG a hf, hl, hs⟩) _ _ h.device }

/-- A `MemStep` changes no register, so it is a `RowEffect` for every destination.
Example: a store row's `Mmu.store_doubleword` call is a `RowEffect none` step. -/
theorem MemStep.rowEffect {F : Nat → Prop} (d : Option Dst) {s t : SailJoltState}
    (h : MemStep F s t) : RowEffect d s t :=
  ⟨h.choiceState, h.cycleCount, h.sailOutput, Or.inl h.regs, fun vr _ => by rw [h.vregs],
    h.adviceTape, h.hostIO⟩

/-- Inserting bytes at addresses `ea + k`, `k ∈ L`, leaves every other address unchanged.
Example: storing the doubleword at `0x8000_0000` leaves the byte at `0x8000_0008` alone. -/
theorem foldl_insert_get?_of_ne (L : List Nat) (f : Nat → BitVec 8) (ea a : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (h : ∀ k ∈ L, ea + k ≠ a) :
    (L.foldl (fun mem k => mem.insert (ea + k) (f k)) mem).get? a = mem.get? a := by
  induction L generalizing mem with
  | nil => rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]
    simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, h k List.mem_cons_self]

private theorem foldl_insert_isSome (L : List Nat) (f : Nat → BitVec 8) (ea a : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (h : (mem.get? a).isSome) :
    (L.foldl (fun mem k => mem.insert (ea + k) (f k)) mem).get? a |>.isSome := by
  induction L generalizing mem with
  | nil => exact h
  | cons k L ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert] at h ⊢
    split <;> simp [h]

/-- A successful raw byte store at an address in `F` is a `MemStep` at `F`.
Example: a byte store at RAM address `a` inserts into `sail.mem` at `a`, and a byte store at
an output address below RAM is one `DeviceStoreAt` step. -/
theorem storeRaw_memStep {F : Nat → Prop} {s t : SailJoltState} {a : Nat} {v : BitVec 8}
    (hF : F a) (h : Mmu.store_raw? s a v = some t) : MemStep F s t := by
  unfold Mmu.store_raw? at h
  split at h
  · split at h
    · cases h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
        fun b hb => ?_, Relation.ReflTransGen.refl⟩
      · have hne : a ≠ b := fun e => hb (e ▸ hF)
        simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, hne]
      · simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert] at hb ⊢
        split <;> simp [hb]
      · have hne : a ≠ b := by omega
        simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, hne]
    · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : s.jolt_device.store? a v with
        | none => simp [hd] at h
        | some d =>
          simp only [hd, Option.map_some] at h
          cases h
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => h,
            fun _ _ => rfl, Relation.ReflTransGen.single ⟨a, v, hF, by omega, hd⟩⟩

/-- A successful doubleword store at `addr` is a `MemStep` at `addr .. addr + 7`.
Example: `Mmu.store_doubleword 0x80000008 v` changes at most the RAM bytes
`0x80000008 .. 0x8000000f`. -/
theorem storeDoubleword_memStep {addr value : BitVec 64} {s t : SailJoltState}
    {r : Result Bool ExecutionResult} (h : Mmu.store_doubleword addr value s = .ok r t) :
    MemStep (fun a => addr.toNat ≤ a ∧ a < addr.toNat + 8) s t := by
  unfold Mmu.store_doubleword at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
          fun b hb => ?_, Relation.ReflTransGen.refl⟩
        · apply foldl_insert_get?_of_ne
          intro k hk
          simp only [List.mem_range] at hk
          omega
        · exact foldl_insert_isSome _ _ _ _ _ hb
        · apply foldl_insert_get?_of_ne
          intro k hk
          omega
      · cases h
    · split at h
      · rename_i heq
        cases h
        exact InstructionFrame.storeFold_rule_of_step (relation := MemStep _) addr.toNat value s
          (List.range 8)
          (fun k hk s₁ s₂ h₁ hs => h₁.trans _ _ _ (storeRaw_memStep
            (by simp only [List.mem_range] at hk; omega) hs))
          (some s) (fun s₁ hs₁ => by cases hs₁; exact MemStep.refl _ _) _ heq
      · cases h

open StatePreservation in
private theorem storeDoubleword_rowEffect (d : Option Dst) (addr value : BitVec 64) :
    Preserves (RowEffect d) (Mmu.store_doubleword addr value) :=
  fun _ _ _ h => (storeDoubleword_memStep h).rowEffect d

/-! ### Rows -/

open StatePreservation in
/-- Every frame row satisfies `RowEffect` for its own destination, whatever its result.
Example: `ADDI (.vreg vr48) (.xreg x0) 0` changes only `vr48` outside memory and the
device, and `SD (.xreg x10) (.vreg vr48) 0` changes nothing outside them. -/
theorem execInstr_rowEffect {i : Instr} (hi : i.isFrameRow = true) :
    Preserves (RowEffect i.destination?) (execInstr i) := by
  cases i <;> simp only [Instr.isFrameRow, Bool.false_eq_true] at hi
  all_goals simp only [execInstr, Instr.destination?]
  all_goals preservation_auto [readSrc_rowEffect _ _, writeDst_rowEffect _ _,
    pure_rule (RowEffect.refl _) _, throw_rule _ _,
    keeps_rowEffect _ (loadDoubleword_keeps _), keeps_rowEffect _ getArchPc_keeps,
    storeDoubleword_rowEffect _ _ _]
    using (bind_rule RowEffect.trans)

/-- Memory and the device are unchanged.
Example: an `ADDI` row relates its start and end states by `MemDevEq`. -/
def MemDevEq (s t : SailJoltState) : Prop :=
  t.sail.mem = s.sail.mem ∧ t.jolt_device = s.jolt_device

private theorem MemDevEq.refl (s : SailJoltState) : MemDevEq s s := ⟨rfl, rfl⟩

private theorem MemDevEq.trans (s m t : SailJoltState) (h₁ : MemDevEq s m)
    (h₂ : MemDevEq m t) : MemDevEq s t :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

open StatePreservation in
private theorem keeps_memDevEq {α : Type} {m : JoltMonad α}
    (keeps : ∀ s t v, m s = .ok v t → t = s) : Preserves MemDevEq m := by
  intro s t v h
  rw [keeps s t v h]
  exact MemDevEq.refl s

open StatePreservation in
private theorem writeDst_memDevEq (dst : Dst) (v : BitVec 64) :
    Preserves MemDevEq (writeDst dst v) := by
  cases dst with
  | vreg vr =>
    intro s t u h
    simp only [writeDst, writeVReg] at h
    split at h
    · cases h
    · cases h
      exact MemDevEq.refl s
  | xreg rd =>
    intro s t u h
    simp only [writeDst] at h
    unfold liftSail at h
    cases hw : wX_bits rd v s.sail with
    | error e s1 => rw [hw] at h; cases h
    | ok u' s1 =>
      rw [hw] at h
      cases h
      have hm := wX_eq_modify_regs rd v s.sail s1 hw
      exact ⟨by dsimp only; rw [hm], rfl⟩

open StatePreservation in
/-- A frame row that is not a store row leaves memory and the device unchanged.
Example: `LD` reads memory with `Mmu.load_doubleword` and changes neither. -/
theorem execInstr_memDevEq {i : Instr} (hi : i.isFrameRow = true) (hs : i.storeSlot? = none) :
    Preserves MemDevEq (execInstr i) := by
  cases i <;>
    simp only [Instr.isFrameRow, Instr.storeSlot?, Bool.false_eq_true, reduceCtorEq] at hi hs
  all_goals simp only [execInstr]
  all_goals preservation_auto [keeps_memDevEq (fun _ _ _ h => (readSrc_run h).1),
    writeDst_memDevEq _ _, pure_rule MemDevEq.refl _, throw_rule _ _,
    keeps_memDevEq (loadDoubleword_keeps _), keeps_memDevEq getArchPc_keeps]
    using (bind_rule MemDevEq.trans)

/-- The store step shared by every store row.
A run of `readSrc value` followed by `Mmu.store_doubleword a` and any continuation `k`
that ends in `.ok r s'` performs one doubleword store at `a` from the start state `s`
whose result state is `s'`, because `readSrc` leaves the state unchanged and the
continuation of a store row is `pure`.
Example: the `VirtualStoreB` body `stored ← readSrc value; match ← Mmu.store_doubleword
(ea &&& ~~~7) stored with ...` is this shape with `a = ea &&& ~~~7`. -/
private theorem readThenStore_run {β : Type} {value : Src} {a : BitVec 64}
    {k : Result Bool ExecutionResult → JoltMonad β}
    (hk : ∀ x m r t, k x m = .ok r t → t = m)
    {s s' : SailJoltState} {r : β}
    (h : (readSrc value >>= fun v => Mmu.store_doubleword a v >>= k) s = .ok r s') :
    ∃ v res, Mmu.store_doubleword a v s = .ok res s' := by
  obtain ⟨v, m, hv, hrest⟩ := bind_ok h
  obtain ⟨rfl, -⟩ := readSrc_run hv
  obtain ⟨res, m, hst, hk'⟩ := bind_ok hrest
  exact ⟨v, res, (hk _ _ _ _ hk') ▸ hst⟩

/-- A store row either leaves the state unchanged or stores one doubleword at its slot's
address, with the base read in the start state.
Example: `SD (.xreg x10) (.vreg vr48) 8` with `x10 = 0x80000000` either fails its
alignment check or calls `Mmu.store_doubleword 0x80000008 v`. -/
theorem storeRow_run {i : Instr} {slot : StoreSlot} (hslot : i.storeSlot? = some slot)
    {s s' : SailJoltState} {r : ExecutionResult} (h : (execInstr i).run s = .ok r s') :
    s' = s ∨ ∃ v res, Mmu.store_doubleword (slot.address s) v s = .ok res s' := by
  have hk : ∀ (x : Result Bool ExecutionResult) m r t,
      (match x with
        | .Ok _ => pure RETIRE_SUCCESS
        | .Err e => pure e : JoltMonad ExecutionResult) m = .ok r t → t = m := by
    intro x m r t h
    split at h <;> (cases h; rfl)
  cases i <;> simp only [Instr.storeSlot?, reduceCtorEq, Option.some.injEq] at hslot
  all_goals subst hslot
  all_goals simp only [execInstr, EStateM.run] at h
  all_goals
    obtain ⟨b, m, hb, h⟩ := bind_ok h
    obtain ⟨rfl, rfl⟩ := readSrc_run hb
  case VirtualStoreB => exact Or.inr (readThenStore_run hk h)
  case VirtualStoreH | VirtualStoreW =>
    -- The value is read and stored only when the alignment check passes.
    split at h
    · exact Or.inr (readThenStore_run hk h)
    · cases h
      exact Or.inl rfl
  case SD =>
    -- SD reads the value before its alignment check.
    obtain ⟨v, m, hv, h⟩ := bind_ok h
    obtain ⟨rfl, -⟩ := readSrc_run hv
    split at h
    · obtain ⟨res, m, hst, h⟩ := bind_ok h
      exact Or.inr ⟨v, res, (hk _ _ _ _ h) ▸ hst⟩
    · cases h
      exact Or.inl rfl

/-- The finer Sail fact the frame proof needs.
`InstructionFrame.Rules.sail` lets an instruction replace the Sail state arbitrarily,
which cannot prove `Frame.sailRegs`. For a frame row, the Sail registers change only by
`wX_bits` on an architectural destination (`wX_update_regs`), and the other Sail fields
except memory are unchanged.
Proof: the first four components of `execInstr_rowEffect`.
Example: `ADDI (.xreg x5) (.xreg x0) 1` changes the Sail registers by
`wX_update_regs x5 1`, and `SD (.xreg x10) (.vreg vr48) 0` leaves them unchanged. -/
theorem execInstr_sail_effect {i : Instr} (hi : i.isFrameRow = true)
    {s s' : SailJoltState} {r : ExecutionResult}
    (h : (execInstr i).run s = .ok r s') :
    s'.sail.choiceState = s.sail.choiceState ∧
    s'.sail.cycleCount = s.sail.cycleCount ∧
    s'.sail.sailOutput = s.sail.sailOutput ∧
    (s'.sail.regs = s.sail.regs ∨
      ∃ rd v, i.destination? = some (.xreg rd) ∧ s'.sail.regs = wX_update_regs rd v s.sail.regs) := by
  obtain ⟨hc, hcy, ho, hr, -⟩ := execInstr_rowEffect hi s s' r h
  exact ⟨hc, hcy, ho, hr⟩

/-- The frame of one row.
Proof: `execInstr_sail_effect` gives the Sail clauses, and `execInstr_rowEffect` gives
the virtual-register, tape and host clauses.
A non-store row leaves memory and the device unchanged (`execInstr_memDevEq`).
A store row either changes nothing or calls `Mmu.store_doubleword` at `slot.address s`
(`storeRow_run`), which is a `MemStep` at that doubleword (`storeDoubleword_memStep`), and
the doubleword lies in the footprint.
Example: `SD (.xreg x10) (.vreg vr48) 0` with its slot in `ws.stores` satisfies the frame,
writing only the eight bytes at the address `x10` holds. -/
theorem execInstr_frame {ws : WriteSet} {i : Instr} (hi : i.writesWithin ws = true)
    (hslot : ∀ slot, i.storeSlot? = some slot → slot ∈ ws.stores)
    {s s' : SailJoltState} (h : (execInstr i).run s = .ok RETIRE_SUCCESS s') :
    Frame ws s s' := by
  have hw := (Instr.writesWithin_iff ws i).1 hi
  obtain ⟨hc, hcy, ho, hregs⟩ := execInstr_sail_effect hw.1 h
  obtain ⟨-, -, -, -, hv, ht, hh⟩ := execInstr_rowEffect hw.1 s s' _ h
  have hmem : MemStep (ws.Footprint s) s s' ∨ MemDevEq s s' := by
    cases hs : i.storeSlot? with
    | none => exact Or.inr (execInstr_memDevEq hw.1 hs s s' _ h)
    | some slot =>
      rcases storeRow_run hs h with rfl | ⟨v, res, hst⟩
      · exact Or.inr (MemDevEq.refl _)
      · exact Or.inl ((storeDoubleword_memStep hst).mono
          (fun a ha => ⟨slot, hslot slot hs, ha⟩))
  refine
    { sailRegs := fun R hR => ?_
      choiceState := hc
      cycleCount := hcy
      sailOutput := ho
      vregs := fun vr hvr => hv vr (fun hd => hvr (hw.2 _ hd))
      mem := fun a ha => ?_
      mem_present := fun a ha => ?_
      mem_belowRam := fun a ha => ?_
      device := ?_
      adviceTape := ht
      hostIO := hh }
  · rcases hregs with e | ⟨rd, v, hd, e⟩
    · rw [e]
    · rw [e]
      apply wX_update_regs_get?_of_ne
      intro hrd
      rcases hw.2 _ hd with h0 | ⟨w, hwm, hsame⟩
      · rw [xRegister?_of_isX0 h0] at hrd
        cases hrd
      · exact hR ⟨w, hwm, by rw [eq_of_sameXReg hsame]; exact hrd⟩
  · rcases hmem with m | m
    · exact m.mem a ha
    · rw [m.1]
  · rcases hmem with m | m
    · exact m.present a ha
    · rw [m.1]; exact ha
  · rcases hmem with m | m
    · exact m.belowRam a ha
    · rw [m.1]
  · rcases hmem with m | m
    · exact m.device
    · rw [m.2]

/-! ## The frame lemma -/

/-- **Generic inline frame lemma.** Every successful run of a program that passes the
static check satisfies the frame relation. There is no precondition on the start state,
on the inputs or on the advice.
Example: `FrameInstances.sha256_frame` applies it to the SHA-256 compression rows. -/
theorem frame_of_run {p : Program} {ws : WriteSet} (hp : p.WritesWithin ws)
    {s s' : SailJoltState} (h : p.Run s s') : Frame ws s s' := by
  obtain ⟨hrows, hslots, hk⟩ := hp
  revert s
  induction p with
  | done r =>
    intro s h
    have hs : s' = s := by
      simp only [Program.Run, execProgram_done, EStateM.run, pure, EStateM.pure] at h
      cases h
      rfl
    subst hs
    exact Frame.refl ws _
  | instr i rest ih =>
    intro s h
    obtain ⟨m, hi, hrest⟩ := execProgram_instr_run_retire_inv i rest s s' h
    simp only [Program.rowsWithin, Program.rows, List.all_cons, Bool.and_eq_true] at hrows
    have hhead : ∀ slot, i.storeSlot? = some slot → slot ∈ ws.stores := by
      intro slot hsl
      apply hslots
      simp only [Program.storeSlots, Program.rows, List.mem_filterMap]
      exact ⟨i, by simp, hsl⟩
    have htail : rest.storeSlots ⊆ ws.stores := by
      intro slot hsl
      apply hslots
      simp only [Program.storeSlots, Program.rows, List.mem_filterMap] at hsl ⊢
      obtain ⟨j, hj, hjs⟩ := hsl
      exact ⟨j, by simp [hj], hjs⟩
    exact (execInstr_frame hrows.1 hhead hi).trans (ih hrows.2 htail hrest) hk

end JoltISA.Inlines

namespace JoltISA

open Inlines

/-! ## Pool reset (per program) -/

/-- The pool-reset clause of the spec, stated per program: after every successful run,
the listed pool registers hold zero. It is separate from `Frame`, which is generic.
Example: the program with the single row `ADDI (.vreg vr48) (.xreg x0) 0` resets the pool
`[vr48]`. -/
def Program.ResetsPool (p : Program) (pool : List VReg) : Prop :=
  ∀ ⦃s s' : SailJoltState⦄, p.Run s s' → ∀ v ∈ pool, s'.vregs v = 0

/-- The row `ADDI (.vreg v) (.xreg x0) 0`, the reset Jolt emits for a pool register.
Example: `(ADDI (.vreg vr48) (.xreg x0) 0).isZeroReset vr48 = true`, and the same row with
immediate `1` gives `false`. -/
def Instr.isZeroReset (v : VReg) : Instr → Bool
  | .ADDI (.vreg d) (.xreg r) imm => d == v && isX0 r && imm == 0
  | _ => false

/-- The row writes virtual register `v`.
Example: `(ADDI (.vreg vr48) (.xreg x5) 1).writesVReg vr48 = true`, and
`SD (.xreg x10) (.vreg vr48) 0` writes no register. -/
def Instr.writesVReg (v : VReg) (i : Instr) : Bool :=
  match i.destination? with
  | some (.vreg d) => d == v
  | _ => false

/-- The last row of `rows` that writes `v` exists and is a zero reset of `v`.
Example: for the rows `ADDI (.vreg vr48) (.xreg x5) 1; ADDI (.vreg vr48) (.xreg x0) 0` it
is `true`, and in the reverse order it is `false`. -/
def Instr.lastWriteResets (v : VReg) (rows : List Instr) : Bool :=
  match rows.reverse.find? (Instr.writesVReg v) with
  | some i => i.isZeroReset v
  | none => false

/-- Appending rows in front keeps the last write of `v`, once `l₂` has one.
Example: if `l₂ = [ADDI (.vreg vr48) (.xreg x0) 0]`, then `lastWriteResets vr48 (l₁ ++ l₂)`
holds for every `l₁`. -/
theorem Instr.lastWriteResets_append (v : VReg) (l₁ : List Instr) {l₂ : List Instr}
    (h : Instr.lastWriteResets v l₂ = true) : Instr.lastWriteResets v (l₁ ++ l₂) = true := by
  unfold Instr.lastWriteResets at h ⊢
  rw [List.reverse_append, List.find?_append]
  cases h₂ : l₂.reverse.find? (Instr.writesVReg v) with
  | none => simp [h₂] at h
  | some i => simpa [h₂] using h

/-- Chunked form of the pool-reset check: it suffices to check a final segment.
Example: the generated instances check only the last chunk, which holds the pool
resets. -/
theorem Instr.lastWriteResets_all_append (l₁ : List Instr) {l₂ : List Instr}
    {pool : List VReg} (h : pool.all (fun v => Instr.lastWriteResets v l₂) = true) :
    pool.all (fun v => Instr.lastWriteResets v (l₁ ++ l₂)) = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun v hv => Instr.lastWriteResets_append v l₁ (h v hv)

/-- Static check for `Program.ResetsPool`: for every pool register, the last row that
writes it is a zero reset.
Example: the program with the single row `ADDI (.vreg vr48) (.xreg x0) 0` passes the check
for the pool `[vr48]`. -/
def Program.resetsPoolCheck (p : Program) (pool : List VReg) : Bool :=
  pool.all (fun v => Instr.lastWriteResets v p.rows)

/-- Chunked form of the pool-reset check: rows in front of a segment that passes
the check do not matter.
Example: `sha256_resetsPoolCheck` applies it with the last chunk of the SHA-256 rows. -/
theorem Program.resetsPoolCheck_seq_append (l₁ : List Instr) {l₂ : List Instr}
    {pool : List VReg} (h : (Program.seq l₂).resetsPoolCheck pool = true) :
    (Program.seq (l₁ ++ l₂)).resetsPoolCheck pool = true := by
  simp only [Program.resetsPoolCheck, Program.rows_seq] at h ⊢
  exact Instr.lastWriteResets_all_append l₁ h

/-- Variant of `Program.resetsPoolCheck_seq_append` for a final segment of two chunks, in the
left-nested form that `l₁ ++ l₂ ++ l₃` elaborates to.
Example: a program whose pool resets span its last two chunks `l₂` and `l₃`. -/
theorem Program.resetsPoolCheck_seq_append_append (l₁ : List Instr) {l₂ l₃ : List Instr}
    {pool : List VReg} (h : (Program.seq (l₂ ++ l₃)).resetsPoolCheck pool = true) :
    (Program.seq (l₁ ++ l₂ ++ l₃)).resetsPoolCheck pool = true := by
  rw [List.append_assoc]
  exact Program.resetsPoolCheck_seq_append l₁ h

/-- A run of frame rows none of which writes `v` keeps `v`.
Example: the SHA-256 rows after the last reset of `vr48` keep `vr48` at zero. -/
theorem Program.vreg_eq_of_run {v : VReg} : ∀ {p : Program} {s s' : SailJoltState},
    (∀ j ∈ p.rows, j.isFrameRow = true ∧ j.writesVReg v = false) → p.Run s s' →
    s'.vregs v = s.vregs v
  | .done _, s, s', _, h => by
    have hs : s' = s := by
      simp only [Program.Run, execProgram_done, EStateM.run, pure, EStateM.pure] at h
      cases h
      rfl
    rw [hs]
  | .instr i rest, s, s', hrows, h => by
    obtain ⟨m, hi, hrest⟩ := execProgram_instr_run_retire_inv i rest s s' h
    have hrow := hrows i (by simp [Program.rows])
    have e₁ : m.vregs v = s.vregs v := by
      refine (execInstr_rowEffect hrow.1 s m _ hi).2.2.2.2.1 v (fun hd => ?_)
      have := hrow.2
      simp [Instr.writesVReg, hd] at this
    rw [Program.vreg_eq_of_run (fun j hj => hrows j (by simp [Program.rows, hj])) hrest, e₁]

/-- A successful zero reset of `v` leaves `v` at zero.
Example: `ADDI (.vreg vr48) (.xreg x0) 0` sets `vr48` to `0 + 0 = 0`. -/
theorem Instr.zeroReset_run {v : VReg} {i : Instr} (hz : i.isZeroReset v = true)
    {s m : SailJoltState} {r : ExecutionResult} (h : (execInstr i).run s = .ok r m) :
    m.vregs v = 0 := by
  unfold Instr.isZeroReset at hz
  split at hz
  · rename_i d x imm
    simp only [Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨⟨rfl, hx⟩, rfl⟩ := hz
    simp only [execInstr, EStateM.run] at h
    obtain ⟨a, m₁, ha, h⟩ := bind_ok h
    obtain ⟨rfl, rfl⟩ := readSrc_run ha
    obtain ⟨u, m₂, hw, h⟩ := bind_ok h
    cases h
    obtain ⟨b⟩ := x
    simp only [isX0, decide_eq_true_eq] at hx
    simp only [writeDst, writeVReg] at hw
    split at hw
    · cases hw
    · cases hw
      simp [sourceValue, hx, addWide]
  · cases hz

/-- A run of frame rows whose last write of `v` is a zero reset ends with `v` at zero.
Example: the rows `ADDI (.vreg vr48) (.xreg x5) 1; ADDI (.vreg vr48) (.xreg x0) 0` end with
`vr48 = 0`. -/
theorem Program.vreg_zero_of_lastWriteResets {v : VReg} :
    ∀ {p : Program} {s s' : SailJoltState},
    (∀ j ∈ p.rows, j.isFrameRow = true) → Instr.lastWriteResets v p.rows = true →
    p.Run s s' → s'.vregs v = 0
  | .done _, _, _, _, hl, _ => by simp [Program.rows, Instr.lastWriteResets] at hl
  | .instr i rest, s, s', hrows, hl, h => by
    obtain ⟨m, hi, hrest⟩ := execProgram_instr_run_retire_inv i rest s s' h
    have hrows' : ∀ j ∈ rest.rows, j.isFrameRow = true :=
      fun j hj => hrows j (by simp [Program.rows, hj])
    unfold Instr.lastWriteResets at hl
    simp only [Program.rows, List.reverse_cons, List.find?_append] at hl
    cases hf : rest.rows.reverse.find? (Instr.writesVReg v) with
    | some j =>
      apply Program.vreg_zero_of_lastWriteResets hrows' _ hrest
      unfold Instr.lastWriteResets
      rw [hf]
      simpa [hf] using hl
    | none =>
      rw [hf] at hl
      have hnone : ∀ j ∈ rest.rows, j.writesVReg v = false := by
        intro j hj
        have := List.find?_eq_none.1 hf j (List.mem_reverse.2 hj)
        simpa using this
      cases hwi : i.writesVReg v
      · simp [hwi] at hl
      · simp only [hwi, List.find?_cons_of_pos, Option.none_or] at hl
        rw [Program.vreg_eq_of_run (fun j hj => ⟨hrows' j hj, hnone j hj⟩) hrest]
        exact Instr.zeroReset_run (by simpa using hl) hi

/-- Soundness of the pool-reset check.
Proof: for each pool register `v`, the last row that writes `v` is a zero reset
(`Instr.zeroReset_run`), and the later rows are frame rows that do not write `v`
(`Program.vreg_eq_of_run`). The check needs every row to be a frame row, which
`WritesWithin` gives.
Example: applied to `FrameInstances.sha256_writesWithin` and
`FrameInstances.sha256_resetsPoolCheck`, it says that every successful SHA-256 run leaves
`vr48..vr83` at zero. -/
theorem Program.resetsPool_of_check {p : Program} {pool : List VReg} {ws : WriteSet}
    (hp : p.WritesWithin ws) (h : p.resetsPoolCheck pool = true) : p.ResetsPool pool := by
  intro s s' hrun v hv
  have hrows : ∀ j ∈ p.rows, j.isFrameRow = true :=
    fun j hj => ((Program.rowsWithin_iff ws p).1 hp.1 j hj).1
  exact Program.vreg_zero_of_lastWriteResets hrows ((List.all_eq_true.1 h) v hv) hrun

end JoltISA
