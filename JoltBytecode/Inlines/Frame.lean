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

Staged `sorry`s: `execInstr_sail_effect`, `execInstr_frame`, `Frame.sourceValue_xreg_eq`
and `Program.resetsPool_of_check`.
The design note `reports/2026-11-11-inline-frame-statement.md` explains the proof plan.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Store slots and write sets -/

/-- How a store row addresses its doubleword.
`SD` stores at `ea = base + imm`; the floor stores `VirtualStoreB/H/W` store at the
doubleword containing `ea`, that is `ea &&& ~~~7`. -/
inductive StoreKind where
  | dword
  | floor
  deriving DecidableEq, Repr

/-- The syntactic shape of one store row: its base operand, its immediate and its
addressing kind. The stored value does not affect the footprint. -/
structure StoreSlot where
  base : Src
  imm : BitVec 64
  kind : StoreKind
  deriving Repr

/-- The doubleword address a store slot writes, with the base read in `s`.
It matches `execInstr`: `SD` passes `base + imm` to `Mmu.store_doubleword`, the floor
stores pass `(base + imm) &&& ~~~7`. -/
def StoreSlot.address (slot : StoreSlot) (s : SailJoltState) : BitVec 64 :=
  let ea := sourceValue slot.base s + slot.imm
  match slot.kind with
  | .dword => ea
  | .floor => ea &&& ~~~(7 : BitVec 64)

/-- Whether a source operand is an architectural register. -/
def _root_.JoltISA.Src.isXReg : Src → Bool
  | .xreg _ => true
  | .vreg _ => false

/-- What a program's rows may write.
For the in-scope inlines `vregs` lists the pool registers (`vr48..127`) and instruction
temporaries (`vr40..47`) the rows write, `xregs` is empty, and `stores` lists the store
rows. -/
structure WriteSet where
  vregs : List VReg
  xregs : List regidx
  stores : List StoreSlot

namespace WriteSet

variable (ws : WriteSet)

/-- A destination is allowed when it is a listed virtual register, a listed
architectural register, or `x0` (a write to `x0` changes nothing). -/
def allowsDst : Dst → Bool
  | .vreg v => ws.vregs.contains v
  | .xreg r => isX0 r || ws.xregs.any (fun w => sameXReg w r)

/-- A source operand that no allowed row writes: an unlisted virtual register or an
unlisted architectural register. -/
def keepsSrc : Src → Bool
  | .vreg v => !ws.vregs.contains v
  | .xreg r => !ws.xregs.any (fun w => sameXReg w r)

/-- Every store slot's base is an architectural register that no allowed row writes.
Requiring `.xreg` rules out bases such as `vr40`, the instruction temporary that Jolt's
`rd = x0` rewrite of secp256k1 inlines stores through: its value at entry is not an
operand of the source instruction. Jolt rejects those encodings (a16z/jolt#2414). -/
def basesKept : Bool :=
  ws.stores.all (fun slot => slot.base.isXReg && ws.keepsSrc slot.base)

/-- The byte addresses the store rows may write, with bases read in `s`:
`address .. address + 7` for each slot.
The byte addresses are natural numbers, as in `Mmu.write_ram_doubleword` and
`Mmu.store_raw?`. -/
def Footprint (s : SailJoltState) (a : Nat) : Prop :=
  ∃ slot ∈ ws.stores, (slot.address s).toNat ≤ a ∧ a < (slot.address s).toNat + 8

end WriteSet

/-- The Sail register an architectural index names, or `none` for `x0`.
It matches the register `wX` writes and `rX` reads. -/
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
architectural indices. -/
def WriteSet.WritesSailReg (ws : WriteSet) (r : Register) : Prop :=
  ∃ i ∈ ws.xregs, xRegister? i = some r

/-- One successful device byte store at a footprint address below RAM. -/
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
needs an explicit decision. -/
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

/-- The store slot of a store row, and `none` for every other row. -/
def Instr.storeSlot? : Instr → Option StoreSlot
  | .SD base _ imm => some ⟨base, imm, .dword⟩
  | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
  | .VirtualStoreW base _ imm _ => some ⟨base, imm, .floor⟩
  | _ => none

/-- The per-row check: the row is a frame row and its destination, if any, is allowed. -/
def Instr.writesWithin (ws : WriteSet) (i : Instr) : Bool :=
  i.isFrameRow &&
    match i.destination? with
    | some d => ws.allowsDst d
    | none => true

/-- The rows of a program, up to its terminal result. -/
def Program.rows : Program → List Instr
  | .done _ => []
  | .instr i rest => i :: rest.rows

@[simp] theorem Program.rows_seq (l : List Instr) : (Program.seq l).rows = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show x :: (Program.seq l).rows = x :: l
    rw [ih]

/-- The store slots of a program's store rows, in row order. -/
def Program.storeSlots (p : Program) : List StoreSlot :=
  p.rows.filterMap Instr.storeSlot?

/-- The Boolean row check of a whole program. -/
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
`Program.rowsWithin_seq_append` and `Program.storeSlots_seq_append`. -/
def Program.WritesWithin (p : Program) (ws : WriteSet) : Prop :=
  p.rowsWithin ws = true ∧ p.storeSlots ⊆ ws.stores ∧ ws.basesKept = true

/-- Chunked form of the row check, for generated programs built with `Program.seq`
from concatenated chunks. -/
theorem Program.rowsWithin_seq_append (ws : WriteSet) (l₁ l₂ : List Instr) :
    (Program.seq (l₁ ++ l₂)).rowsWithin ws =
      ((Program.seq l₁).rowsWithin ws && (Program.seq l₂).rowsWithin ws) := by
  simp [Program.rowsWithin, List.all_append]

/-- Chunked form of `Program.storeSlots`. -/
theorem Program.storeSlots_seq_append (l₁ l₂ : List Instr) :
    (Program.seq (l₁ ++ l₂)).storeSlots =
      (Program.seq l₁).storeSlots ++ (Program.seq l₂).storeSlots := by
  simp [Program.storeSlots, List.filterMap_append]

/-! ### Soundness of the Boolean check -/

/-- The meaning of an allowed destination. -/
def Inlines.WriteSet.AllowsDst (ws : WriteSet) : Dst → Prop
  | .vreg v => v ∈ ws.vregs
  | .xreg r => isX0 r = true ∨ ∃ w ∈ ws.xregs, sameXReg w r = true

theorem Inlines.WriteSet.allowsDst_iff (ws : WriteSet) (d : Dst) :
    ws.allowsDst d = true ↔ ws.AllowsDst d := by
  cases d <;> simp [WriteSet.allowsDst, WriteSet.AllowsDst]

/-- Soundness and completeness of the per-row check. -/
theorem Instr.writesWithin_iff (ws : WriteSet) (i : Instr) :
    i.writesWithin ws = true ↔
      i.isFrameRow = true ∧ ∀ d, i.destination? = some d → ws.AllowsDst d := by
  unfold Instr.writesWithin
  cases h : i.destination? with
  | none => simp
  | some d => simp [WriteSet.allowsDst_iff]

/-- Soundness and completeness of the program check. -/
theorem Program.rowsWithin_iff (ws : WriteSet) (p : Program) :
    p.rowsWithin ws = true ↔
      ∀ i ∈ p.rows, i.isFrameRow = true ∧ ∀ d, i.destination? = some d → ws.AllowsDst d := by
  simp only [Program.rowsWithin, List.all_eq_true, Instr.writesWithin_iff]

instance (p : Program) (ws : WriteSet) : Decidable (p.rowsWithin ws = true) :=
  inferInstance

end JoltISA

namespace JoltISA.Inlines

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
  touch the tape; only the excluded `VirtualAdviceLoad` and `VirtualHostIO` touch it. -/
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
Proof plan: case on the 32 values of `r`; for `r ≠ x0`, `keepsSrc` rules out every
listed index `i` with `xRegister? i = xRegister? r`, so `sailRegs` applies. -/
theorem sourceValue_xreg_eq {s s' : SailJoltState} (f : Frame ws s s') {r : regidx}
    (h : ws.keepsSrc (.xreg r) = true) :
    sourceValue (.xreg r) s' = sourceValue (.xreg r) s := by
  sorry

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
the start state. -/
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

/-- Frames compose when no allowed row writes a store base. -/
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

/-- With no listed architectural register, the whole Sail register file is unchanged. -/
theorem sailRegs_eq_of_xregs_nil {s s' : SailJoltState} (f : Frame ws s s')
    (h : ws.xregs = []) : s'.sail.regs = s.sail.regs := by
  apply Std.ExtDHashMap.ext_get?
  intro r
  apply f.sailRegs r
  rintro ⟨i, hi, _⟩
  simp [h] at hi

/-- The I/O setup of the device (layout, inputs, advice) is unchanged. -/
theorem device_same {s s' : SailJoltState} (f : Frame ws s s') :
    JoltIOSetupFrame.Same s.jolt_device s'.jolt_device := by
  have hd := f.device
  generalize s'.jolt_device = d at hd ⊢
  induction hd with
  | refl => exact JoltIOSetupFrame.Same.refl _
  | tail _ hstep ih =>
    obtain ⟨a, v, _, _, hs⟩ := hstep
    exact ih.trans (JoltIOSetupFrame.storeDeviceByte_same _ _ a v hs)

theorem store?_panic_mono {d d' : JoltDevice} {a : Nat} {v : BitVec 8}
    (h : JoltDevice.store? d a v = some d') : d.panic = true → d'.panic = true := by
  unfold JoltDevice.store? at h
  split_ifs at h <;> cases h <;> simp

/-- The panic flag never goes from `true` back to `false`. -/
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
(`new_io_geometry` in `JoltConstraints/layout_facts.lean`). -/
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

/-! ## Per-row lemmas (staged) -/

/-- The finer Sail fact the frame proof needs.
`InstructionFrame.Rules.sail` lets an instruction replace the Sail state arbitrarily,
which cannot prove `Frame.sailRegs`. For a frame row, the Sail registers change only by
`wX_bits` on an architectural destination (`wX_update_regs`), and the other Sail fields
except memory are unchanged.
Proof plan: case on the row; `readSrc` and `Mmu.load_doubleword` preserve the state,
`writeDst (.vreg _)` touches only `vregs`, `writeDst (.xreg rd)` is `wX_regs_spec`, and
`Mmu.store_doubleword` changes only `sail.mem` and `jolt_device`. -/
theorem execInstr_sail_effect {i : Instr} (hi : i.isFrameRow = true)
    {s s' : SailJoltState} {r : ExecutionResult}
    (h : (execInstr i).run s = .ok r s') :
    s'.sail.choiceState = s.sail.choiceState ∧
    s'.sail.cycleCount = s.sail.cycleCount ∧
    s'.sail.sailOutput = s.sail.sailOutput ∧
    (s'.sail.regs = s.sail.regs ∨
      ∃ rd v, i.destination? = some (.xreg rd) ∧ s'.sail.regs = wX_update_regs rd v s.sail.regs) := by
  sorry

/-- The frame of one row.
Proof plan: `execInstr_sail_effect` gives the Sail clauses; `writeDst` gives `vregs`;
for a store row, `Mmu.store_doubleword` at `slot.address s` writes RAM bytes
`address + k` (`Mmu.write_ram_doubleword`) or folds `Mmu.store_raw?` over them
(`InstructionFrame.storeFold_rule_of_step` with the relation "device changes by
`DeviceStoreAt`"), so every changed byte is in the footprint. -/
theorem execInstr_frame {ws : WriteSet} {i : Instr} (hi : i.writesWithin ws = true)
    (hslot : ∀ slot, i.storeSlot? = some slot → slot ∈ ws.stores)
    {s s' : SailJoltState} (h : (execInstr i).run s = .ok RETIRE_SUCCESS s') :
    Frame ws s s' := by
  sorry

/-! ## The frame lemma -/

/-- **Generic inline frame lemma.** Every successful run of a program that passes the
static check satisfies the frame relation. There is no precondition on the start state,
on the inputs or on the advice. -/
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
the listed pool registers hold zero. It is separate from `Frame`, which is generic. -/
def Program.ResetsPool (p : Program) (pool : List VReg) : Prop :=
  ∀ ⦃s s' : SailJoltState⦄, p.Run s s' → ∀ v ∈ pool, s'.vregs v = 0

/-- The row `ADDI (.vreg v) (.xreg x0) 0`, the reset Jolt emits for a pool register. -/
def Instr.isZeroReset (v : VReg) : Instr → Bool
  | .ADDI (.vreg d) (.xreg r) imm => d == v && isX0 r && imm == 0
  | _ => false

/-- The row writes virtual register `v`. -/
def Instr.writesVReg (v : VReg) (i : Instr) : Bool :=
  match i.destination? with
  | some (.vreg d) => d == v
  | _ => false

/-- The last row of `rows` that writes `v` exists and is a zero reset of `v`. -/
def Instr.lastWriteResets (v : VReg) (rows : List Instr) : Bool :=
  match rows.reverse.find? (Instr.writesVReg v) with
  | some i => i.isZeroReset v
  | none => false

/-- Appending rows in front keeps the last write of `v`, once `l₂` has one. -/
theorem Instr.lastWriteResets_append (v : VReg) (l₁ : List Instr) {l₂ : List Instr}
    (h : Instr.lastWriteResets v l₂ = true) : Instr.lastWriteResets v (l₁ ++ l₂) = true := by
  unfold Instr.lastWriteResets at h ⊢
  rw [List.reverse_append, List.find?_append]
  cases h₂ : l₂.reverse.find? (Instr.writesVReg v) with
  | none => simp [h₂] at h
  | some i => simpa [h₂] using h

/-- Chunked form of the pool-reset check: it suffices to check a final segment. -/
theorem Instr.lastWriteResets_all_append (l₁ : List Instr) {l₂ : List Instr}
    {pool : List VReg} (h : pool.all (fun v => Instr.lastWriteResets v l₂) = true) :
    pool.all (fun v => Instr.lastWriteResets v (l₁ ++ l₂)) = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun v hv => Instr.lastWriteResets_append v l₁ (h v hv)

/-- Static check for `Program.ResetsPool`. -/
def Program.resetsPoolCheck (p : Program) (pool : List VReg) : Bool :=
  pool.all (fun v => Instr.lastWriteResets v p.rows)

/-- Chunked form of the pool-reset check: rows in front of a segment that passes
the check do not matter. -/
theorem Program.resetsPoolCheck_seq_append (l₁ : List Instr) {l₂ : List Instr}
    {pool : List VReg} (h : (Program.seq l₂).resetsPoolCheck pool = true) :
    (Program.seq (l₁ ++ l₂)).resetsPoolCheck pool = true := by
  simp only [Program.resetsPoolCheck, Program.rows_seq] at h ⊢
  exact Instr.lastWriteResets_all_append l₁ h

/-- Variant of `Program.resetsPoolCheck_seq_append` for a final segment of two chunks, in the
left-nested form that `l₁ ++ l₂ ++ l₃` elaborates to. -/
theorem Program.resetsPoolCheck_seq_append_append (l₁ : List Instr) {l₂ l₃ : List Instr}
    {pool : List VReg} (h : (Program.seq (l₂ ++ l₃)).resetsPoolCheck pool = true) :
    (Program.seq (l₁ ++ l₂ ++ l₃)).resetsPoolCheck pool = true := by
  rw [List.append_assoc]
  exact Program.resetsPoolCheck_seq_append l₁ h

/-- Soundness of the pool-reset check.
Proof plan: split the rows at the last write of `v`; that row sets `v` to
`sourceValue (.xreg x0) + 0 = 0`, and `frame_of_run` on the remaining rows with the
write set minus `v` keeps it. Needs every row to be a frame row; the generated inlines
satisfy this through `WritesWithin`. -/
theorem Program.resetsPool_of_check {p : Program} {pool : List VReg} {ws : WriteSet}
    (hp : p.WritesWithin ws) (h : p.resetsPoolCheck pool = true) : p.ResetsPool pool := by
  sorry

end JoltISA
