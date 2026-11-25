import JoltConstraints.theorems.WholeRun.SystemBlocks
import JoltConstraints.theorems.WholeRun.PlatformStore

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace RiscvInstruction

/-- The load or store a source instruction performs on state `js`: whether it
stores, its width in bytes, and its effective address `rs1 + imm`.
For example, `LH` with `rs1 = 0x40000010` and `imm = 2` is a load of two bytes at
`0x40000012`. Other instructions have no such access. -/
def memAccess : RiscvInstruction → SailJoltState → Option (Bool × Nat × BitVec 64)
  | .LB _ rs1 imm, js | .LBU _ rs1 imm, js =>
      some (false, 1, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LH _ rs1 imm, js | .LHU _ rs1 imm, js =>
      some (false, 2, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LW _ rs1 imm, js | .LWU _ rs1 imm, js =>
      some (false, 4, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .LD _ rs1 imm, js =>
      some (false, 8, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SB _ rs1 imm, js =>
      some (true, 1, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SH _ rs1 imm, js =>
      some (true, 2, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SW _ rs1 imm, js =>
      some (true, 4, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | .SD _ rs1 imm, js =>
      some (true, 8, load_effective_address (JoltISA.sourceValue (.xreg rs1) js) imm)
  | _, _ => none

/-- Platform premise: the instruction is one of the loads LB, LH, LW, LD, LBU, LHU, LWU
or stores SB, SH, SW, SD, and its effective address `rs1 + imm` on `js` lies below
`RAM_START_ADDRESS`, in Sail's I/O window and Jolt's device.
For example, `LW` from `0x40000010` satisfies it and `LW` from `0x80000010` does not. -/
def IoAccess (i : RiscvInstruction) (js : SailJoltState) : Prop :=
  ∃ store width ea, i.memAccess js = some (store, width, ea) ∧
    ea.toNat < JoltISA.RAM_START_ADDRESS

end RiscvInstruction

namespace WholeRun

open PlatformMemory

attribute [local instance] Classical.propDecidable

local macro "bridgeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.theorems.WholeRun.Bridge
    (`WholeRun ++ n.getId)))
local macro "blockHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.theorems.WholeRun.BlockStep
    (`WholeRun ++ n.getId)))
local macro "bundleHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.theorems.WholeRun.Bundles
    (`WholeRun ++ n.getId)))
local macro "storeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
    (`StoreProgramBlocks ++ n.getId)))
/-- Allocation and checked-layout facts for a shared Sail map.
For example, the first output byte is present because it lies in the allocated interval.
No device byte buffer or separate I/O equality is part of this predicate. -/
structure MemoryReady (d : JoltDevice) (s : SailState) : Prop where
  present : ∀ a, memLow d ≤ a → a < memHigh d → ∃ b, s.mem.get? a = some b
  layout : ∃ config, MemoryLayout.new config = some d.memory_layout

/-- Allocation depends only on the memory map.
For example, changing the PC preserves `MemoryReady`. -/
theorem MemoryReady.of_mem_eq {d : JoltDevice} {s t : SailState} (h : MemoryReady d s)
    (hm : t.mem = s.mem) : MemoryReady d t :=
  ⟨fun a lower upper => hm ▸ h.present a lower upper, h.layout⟩

/-- The whole-run relation supplies allocation and layout facts.
For example, this holds at the first prelude state by memory equality. -/
theorem Related.memoryReady {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    MemoryReady jt.jolt_device s := ⟨h.present, h.layout⟩

/-- The lowest shared address lies in Sail's plain I/O region and is word aligned.
For example, flooring a legal byte address to its word cannot fall below this bound. -/
structure MemoryGeometry (d : JoltDevice) : Prop where
  low : 0x40000000 ≤ memLow d
  lowAligned : memLow d % 8 = 0

/-- Checked layout construction supplies the two region facts.
For example, all rounded advice capacities keep the lowest address eight aligned. -/
theorem MemoryGeometry.of_layout (d : JoltDevice)
    (h : ∃ config, MemoryLayout.new config = some d.memory_layout) : MemoryGeometry d := by
  obtain ⟨config, built⟩ := h
  exact ⟨new_lowest_address_ge_half_ram config _ built,
    new_lowest_address_aligned config _ built⟩

/-! ### Transport of the access premises along the prelude -/

private theorem memAccess_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s) :
    i.memAccess t = i.memAccess s := by
  cases i <;> simp only [RiscvInstruction.memAccess, h]

/-- Source-register agreement preserves the below-RAM access classification.
For example, the PC prelude leaves the address of an LB unchanged. -/
private theorem access_congr (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s) :
    i.IoAccess s → i.IoAccess t := by
  have hm := memAccess_congr i s t h
  simpa only [RiscvInstruction.IoAccess, hm] using id

/-! ### Jolt's device reads -/

/-- Cutting byte `k` out of an eight-byte append gives that byte.
For example, byte 1 of `b7 ++ ... ++ b0` is `b1`. -/
private theorem extract_append8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 0 8 = b0 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 8 8 = b1 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 16 8 = b2 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 24 8 = b3 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 32 8 = b4 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 40 8 = b5 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 48 8 = b6 ∧
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' 56 8 = b7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi_bool : (i <b 8) = true := by
      simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
    simp (disch := omega) only [hi_bool, Bool.true_and, BitVec.getLsbD_extractLsb',
      Nat.reduceAdd]
    repeat rw [BitVec.getLsbD_append]
    split_ifs <;> first | (exfalso; omega) | (congr 1; omega)

/-- A successful doubleword read gives each of the eight bytes it read.
For example, byte 2 of the result is the byte read at `address + 2`. -/
private theorem read_doubleword_bytes {f : Nat → Option (BitVec 8)} {a : Nat} {D : BitVec 64}
    (h : JoltISA.read_doubleword? f a = some D) :
    ∀ k < 8, f (a + k) = some (D.extractLsb' (8 * k) 8) := by
  unfold JoltISA.read_doubleword? at h
  split at h
  · rename_i b0 b1 b2 b3 b4 b5 b6 b7 e0 e1 e2 e3 e4 e5 e6 e7
    cases h
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := extract_append8 b0 b1 b2 b3 b4 b5 b6 b7
    intro k hk
    interval_cases k
    · simpa [x0] using e0
    · simpa [x1] using e1
    · simpa [x2] using e2
    · simpa [x3] using e3
    · simpa [x4] using e4
    · simpa [x5] using e5
    · simpa [x6] using e6
    · simpa [x7] using e7
  · simp at h

/-- A retiring `load_doubleword` below RAM is aligned and reads eight device bytes.
For example, a successful load at the aligned address `0x40000008` has read `0x40000008` to
`0x4000000f` through `load_raw?`, and leaves the state unchanged. -/
private theorem load_doubleword_inv (A : BitVec 64) (js js' : SailJoltState)
    (r : Result (BitVec 64) ExecutionResult) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.load_doubleword A js = .ok r js') :
    A.toNat % 8 = 0 ∧ ∃ D, r = .Ok D ∧ js' = js ∧
      JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D := by
  unfold JoltISA.Mmu.load_doubleword at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ A.toNat := by omega
  by_cases hal : A.toNat % 8 = 0
  · simp only [hal, ne_eq, not_true_eq_false, ite_false, hnle] at h
    split at h
    · rename_i D hD
      cases h
      exact ⟨hal, D, rfl, rfl, hD⟩
    · simp at h
  · simp [hal] at h

/-- A doubleword whose eight bytes are in Sail's memory is `loaded_dword_at`.
For example, memory holding `0x08 0x07 ... 0x01` at `a, a + 1, ..., a + 7` loads
`0x0102030405060708`. -/
private theorem loaded_dword_eq_of_bytes (s : SailState) (A : BitVec 64)
    (hb : MemBytesPresentAt s A 8) (no : A.toNat + 7 < 2 ^ 64) (D : BitVec 64)
    (h : ∀ k < 8, s.mem.get? (A.toNat + k) = some (D.extractLsb' (8 * k) 8)) :
    loaded_dword_at s A hb no = D := by
  have hbyte : ∀ (a : BitVec 64) (p : MemBytePresentAt s a.toNat) (b : BitVec 8),
      s.mem.get? a.toNat = some b → loaded_byte_at s a p = b := by
    intro a p b hab
    unfold loaded_byte_at loaded_byte_at_nat
    simp only [hab, Option.get_some]
  have hn : ∀ c : Nat, c < 8 → (A + BitVec.ofNat 64 c).toNat = A.toNat + c := by
    intro c hc
    rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  unfold loaded_dword_at
  rw [hbyte (A + 7) _ (D.extractLsb' 56 8) (by simpa [hn 7 (by omega)] using h 7 (by omega)),
    hbyte (A + 6) _ (D.extractLsb' 48 8) (by simpa [hn 6 (by omega)] using h 6 (by omega)),
    hbyte (A + 5) _ (D.extractLsb' 40 8) (by simpa [hn 5 (by omega)] using h 5 (by omega)),
    hbyte (A + 4) _ (D.extractLsb' 32 8) (by simpa [hn 4 (by omega)] using h 4 (by omega)),
    hbyte (A + 3) _ (D.extractLsb' 24 8) (by simpa [hn 3 (by omega)] using h 3 (by omega)),
    hbyte (A + 2) _ (D.extractLsb' 16 8) (by simpa [hn 2 (by omega)] using h 2 (by omega)),
    hbyte (A + 1) _ (D.extractLsb' 8 8) (by simpa [hn 1 (by omega)] using h 1 (by omega)),
    hbyte A _ (D.extractLsb' 0 8) (by simpa using h 0 (by omega))]
  exact append_bytes D

/-- Readable shared I/O bytes are no lower than the checked allocation.
For example, an output or gap byte lies after the input/advice starts. -/
private theorem readable_lower (device : JoltDevice)
    (layout : ∃ config, MemoryLayout.new config = some device.memory_layout)
    (address : Nat) (readable : device.readable address = true) : memLow device ≤ address := by
  obtain ⟨config, built⟩ := layout
  obtain ⟨inputLower, outputLower, outputEndLower, ioEnd, _⟩ := new_io_ordered config _ built
  have ioEndNat := congrArg BitVec.toNat ioEnd
  have trustedLower : memLow device ≤ device.memory_layout.trusted_advice_start.toNat := by
    unfold memLow MemoryLayout.get_lowest_address
    split <;> omega
  have untrustedLower : memLow device ≤ device.memory_layout.untrusted_advice_start.toNat := by
    unfold memLow MemoryLayout.get_lowest_address
    split <;> omega
  simp only [JoltDevice.readable, JoltDevice.is_input, JoltDevice.is_trusted_advice,
    JoltDevice.is_untrusted_advice, JoltDevice.is_output, JoltDevice.is_io_gap,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at readable
  change device.memory_layout.get_lowest_address.toNat ≤ address
  unfold memLow at trustedLower untrustedLower
  omega

/-- A successful first-byte read below RAM passed the mapped-region guard.
For example, a gap-word load starts above the lowest checked allocation address. -/
private theorem read_lower (js : SailJoltState) (A D : BitVec 64)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hread : JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D) :
    memLow js.jolt_device ≤ A.toNat := by
  have first := read_doubleword_bytes hread 0 (by omega)
  simp only [Nat.add_zero] at first
  have mapped : js.jolt_device.readable A.toNat = true := by
    by_contra absent
    have no : js.jolt_device.readable A.toNat = false := Bool.eq_false_iff.mpr absent
    simp only [Mmu.load_raw?, Mmu.effective_address_ok, hlt, ite_true, no,
      Bool.not_false, ite_true] at first
    cases first
  exact readable_lower js.jolt_device hmem.layout A.toNat mapped

/-- A checked below-RAM read is the word in the single shared map.
For example, reading an output or gap word needs no device-array agreement. -/
private theorem io_dword_eq (js : SailJoltState) (A D : BitVec 64)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hal : A.toNat % 8 = 0) (hlow : memLow js.jolt_device ≤ A.toNat)
    (hlt : A.toNat < RAM_START_ADDRESS)
    (hread : JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) A.toNat = some D) :
    ∃ (hb : MemBytesPresentAt js.sail A 8) (no : A.toNat + 7 < 2 ^ 64),
      loaded_dword_at js.sail A hb no = D := by
  have bytes := read_doubleword_bytes hread
  have upper : A.toNat + 8 ≤ RAM_START_ADDRESS := by
    simp only [RAM_START_ADDRESS] at hlt ⊢
    omega
  have high : RAM_START_ADDRESS ≤ memHigh js.jolt_device := by
    unfold memHigh Mmu.ram_backing_end
    omega
  have hget : ∀ k < 8, js.sail.mem.get? (A.toNat + k) = some (D.extractLsb' (8 * k) 8) := by
    intro k hk
    obtain ⟨b, present⟩ := hmem.present (A.toNat + k) (by omega) (by omega)
    have value := JoltConstraints.load_raw_value js _ _ (bytes k hk)
    simpa only [Mmu.ram_byte, present, Option.getD_some] using
      congrArg (fun value => some value) value.symm
  have no : A.toNat + 7 < 2 ^ 64 := by simp only [RAM_START_ADDRESS] at upper; omega
  exact ⟨fun k hk => ⟨_, hget k hk⟩, no, loaded_dword_eq_of_bytes js.sail A _ no D hget⟩

/-! ### Jolt's load rows -/

/-- A retiring first load row is aligned and read a doubleword.
For example, if `VirtualLoadW` retires, the effective address is 4-aligned and
`load_doubleword` of its containing doubleword succeeded. -/
private theorem floorLoad_inv (w : JoltISA.AccessWidth) (vd : JoltISA.VReg) (rs1 : regidx)
    (imm base : BitVec 64) (fc : JoltISA.LoadFaultClass) (f : ExceptionType)
    (js js1 : SailJoltState) (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + imm) &&& ~~~(7 : BitVec 64)).toNat < JoltISA.RAM_START_ADDRESS)
    (h : (JoltISA.execInstr (LoadFamily.floorLoadRow w (.vreg vd) (.xreg rs1) imm fc f)).run js =
      .ok RETIRE_SUCCESS js1) :
    (base + imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) js =
        .ok (.Ok D) js := by
  by_cases halign : (base + imm) &&& LoadFamily.alignmentMask w = 0
  · refine ⟨halign, ?_⟩
    cases hl : JoltISA.Mmu.load_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) js with
    | ok r s' =>
      obtain ⟨_, D, hr, hs, _⟩ := load_doubleword_inv _ js s' r hlt hl
      subst hr
      subst hs
      exact ⟨D, rfl⟩
    | error e s' =>
      exfalso
      cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
        simp only [LoadFamily.floorLoadRow, JoltISA.laneWindowOpen, JoltISA.execInstr,
          JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hread, halign,
          ↓reduceIte, hl] at h <;>
        simp at h
  · exfalso
    have := LoadFamily.floorLoad_misaligned w (.vreg vd) rs1 imm base fc f js hread halign
    rw [this] at h
    simp [RETIRE_SUCCESS] at h

/-- The second row of a narrow load, the window mask for the access width.
For example, word width is `VirtualWindowMaskW`. -/
private def maskRow : JoltISA.AccessWidth → JoltISA.Dst → JoltISA.Src → BitVec 64 →
    JoltISA.Instr
  | .byte, lane, base, offset => .VirtualWindowMaskB lane base offset
  | .halfword, lane, base, offset => .VirtualWindowMaskH lane base offset
  | .word, lane, base, offset => .VirtualWindowMaskW lane base offset

/-- The mask value the window-mask row of the given width computes.
For example, for a halfword at offset 2 it selects bits 16 to 31 of the doubleword. -/
private def maskValue : JoltISA.AccessWidth → BitVec 64 → BitVec 12 → BitVec 64
  | .byte, base, imm => jolt_virtual_window_mask_b_value base imm
  | .halfword, base, imm => jolt_virtual_window_mask_h_value base imm
  | .word, base, imm => jolt_virtual_window_mask_w_value base imm

/-- The value the extraction row computes, signed or unsigned.
For example, extracting the byte `0x80` with `signed` gives `0xFFFFFFFFFFFFFF80`. -/
private def extractValue (signed : Bool) (D M : BitVec 64) : BitVec 64 :=
  if signed then jolt_virtual_pext_signed_value D M else jolt_virtual_pext_value D M

/-- The value a narrow load leaves: the lane of the doubleword, extended.
For example, `LB` of `0x80` leaves `0xFFFFFFFFFFFFFF80`. -/
private def loadValue (w : JoltISA.AccessWidth) (signed : Bool) (D base : BitVec 64)
    (imm : BitVec 12) : BitVec 64 :=
  extractValue signed D (maskValue w base imm)

private theorem laneWindowOpen_eq (w : JoltISA.AccessWidth) (d l : JoltISA.Dst)
    (b : JoltISA.Src) (o : BitVec 64) (fc : JoltISA.LoadFaultClass) (f : ExceptionType)
    (tail : JoltISA.Program) :
    JoltISA.laneWindowOpen w d l b o fc f tail =
      .instr (LoadFamily.floorLoadRow w d b o fc f) (.instr (maskRow w l b o) tail) := by
  cases w <;> rfl

/-- The window-mask row retires and writes the mask to its scratch register.
For example, the byte mask of address 0x40000003 is written to the lane register. -/
private theorem maskRow_run (w : JoltISA.AccessWidth) (lane : JoltISA.VReg) (rs1 : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok x js.sail) (hlane : WritableVReg lane) :
    (JoltISA.execInstr (maskRow w (.vreg lane) (.xreg rs1) (sign_extend (m := 64) imm))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js lane (maskValue w x imm)) := by
  cases w
  · exact JoltISA.virtual_window_mask_b_run_vreg_xreg lane rs1 imm js x hread hlane
  · exact JoltISA.virtual_window_mask_h_run_vreg_xreg lane rs1 imm js x hread hlane
  · exact JoltISA.virtual_window_mask_w_run_vreg_xreg lane rs1 imm js x hread hlane

/-- The extraction row of a narrow load retires and writes the extended lane to a register.
For example, with `signed` it writes the sign-extended lane to `rd`. -/
private theorem pextRow_xreg_run (signed : Bool) (rd : regidx) (dw lane : JoltISA.VReg)
    (js : SailJoltState) :
    (JoltISA.execInstr (if signed then
        JoltISA.Instr.VirtualPextSigned (.xreg rd) (.vreg dw) (.vreg lane)
      else JoltISA.Instr.VirtualPext (.xreg rd) (.vreg dw) (.vreg lane))).run js =
      .ok RETIRE_SUCCESS { js with
        sail := stateAfterWrite js.sail rd (extractValue signed (js.vregs dw) (js.vregs lane)) } := by
  cases signed
  · simp only [Bool.false_eq_true, ↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_run_xreg_vreg_vreg rd dw lane js _
      (wX_bits_stateAfterWrite rd _ js.sail)
  · simp only [↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_signed_run_xreg_vreg_vreg rd dw lane js _
      (wX_bits_stateAfterWrite rd _ js.sail)

/-- The extraction row of a narrow load retires and writes the extended lane to a scratch
register. -/
private theorem pextRow_vreg_run (signed : Bool) (v dw lane : JoltISA.VReg)
    (js : SailJoltState) (hv : WritableVReg v) :
    (JoltISA.execInstr (if signed then
        JoltISA.Instr.VirtualPextSigned (.vreg v) (.vreg dw) (.vreg lane)
      else JoltISA.Instr.VirtualPext (.vreg v) (.vreg dw) (.vreg lane))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js v
        (extractValue signed (js.vregs dw) (js.vregs lane))) := by
  cases signed
  · simp only [Bool.false_eq_true, ↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_run_vreg_vreg_vreg v dw lane js hv
  · simp only [↓reduceIte, extractValue]
    exact JoltISA.virtual_pext_signed_run_vreg_vreg_vreg v dw lane js hv

/-- A retiring narrow load program reads an aligned doubleword and leaves the extended lane.
From a retiring run of the three rows, the effective address is aligned for the width, the
containing doubleword was read, the device is unchanged, and the destination holds the lane. -/
private theorem loadRows_inv (w : JoltISA.AccessWidth) (signed : Bool)
    (dw lane : JoltISA.VReg) (dst : JoltISA.Dst) (hdw : WritableVReg dw)
    (hlane : WritableVReg lane) (hne : dw ≠ lane) (hdst : ∀ v, dst = .vreg v → WritableVReg v)
    (rs1 : regidx) (imm : BitVec 12) (base : BitVec 64) (js gp : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execProgram (JoltISA.laneWindowOpen w (.vreg dw) (.vreg lane) (.xreg rs1)
        (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg dw) (.vreg lane) dst signed
          (.done RETIRE_SUCCESS)))).run js = .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)) js = .ok (.Ok D) js ∧
        gp.jolt_device = js.jolt_device ∧
        (∀ rd, dst = .xreg rd →
          gp.sail = stateAfterWrite js.sail rd (loadValue w signed D base imm)) ∧
        (∀ v, dst = .vreg v → gp.sail = js.sail) := by
  have hrun' := hrun
  rw [laneWindowOpen_eq] at hrun'
  obtain ⟨js1, h1, -⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ js gp hrun'
  obtain ⟨hal, D, hD⟩ := floorLoad_inv w dw rs1 (sign_extend (m := 64) imm) base .normal
    (ExceptionType.E_Load_Addr_Align ()) js js1 hread hlt h1
  refine ⟨hal, D, hD, ?_⟩
  have e1 := LoadFamily.floorLoad_run w dw rs1 (sign_extend (m := 64) imm) base D .normal
    (ExceptionType.E_Load_Addr_Align ()) js hread hal hD hdw
  have hread1 : rX_bits rs1 (stateAfterVRegWrite js dw D).sail =
      .ok base (stateAfterVRegWrite js dw D).sail := hread
  have e2 := maskRow_run w lane rs1 imm _ base hread1 hlane
  have hv1 : (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane
      (maskValue w base imm)).vregs dw = D := by simp [stateAfterVRegWrite, hne]
  have hv2 : (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane
      (maskValue w base imm)).vregs lane = maskValue w base imm := by simp [stateAfterVRegWrite]
  cases dst with
  | xreg rd =>
    have e3 := pextRow_xreg_run signed rd dw lane
      (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane (maskValue w base imm))
    rw [hv1, hv2] at e3
    have hprog := LoadFamily.threeRows_run e1 e2 e3
    unfold JoltISA.Program.Run at hprog
    rw [laneWindowOpen_eq] at hrun
    have hg := hrun.symm.trans hprog
    simp only [EStateM.Result.ok.injEq, true_and] at hg
    subst hg
    refine ⟨rfl, ?_, nofun⟩
    intro rd' h
    cases h
    rfl
  | vreg v =>
    have e3 := pextRow_vreg_run signed v dw lane
      (stateAfterVRegWrite (stateAfterVRegWrite js dw D) lane (maskValue w base imm))
      (hdst v rfl)
    rw [hv1, hv2] at e3
    have hprog := LoadFamily.threeRows_run e1 e2 e3
    unfold JoltISA.Program.Run at hprog
    rw [laneWindowOpen_eq] at hrun
    have hg := hrun.symm.trans hprog
    simp only [EStateM.Result.ok.injEq, true_and] at hg
    subst hg
    refine ⟨rfl, nofun, ?_⟩
    intro v' h
    rfl

/-! ### Sail's load rows -/

/-- The bytes of an access inside an aligned doubleword are present when the doubleword is.
For example, a halfword at `0x40000006` lies in the doubleword at `0x40000000`. -/
private theorem present_in_dword (s : SailState) (ea : BitVec 64)
    (hb : MemBytesPresentAt s (ea &&& (-8 : BitVec 64)) 8) (width : Nat)
    (hw : ea.toNat % 8 + width ≤ 8) : MemBytesPresentAt s ea width := by
  intro k hk
  have h := hb (ea.toNat % 8 + k) (by omega)
  have hA := toNat_and_neg8 ea
  have : (ea &&& (-8 : BitVec 64)).toNat + (ea.toNat % 8 + k) = ea.toNat + k := by omega
  rw [this] at h
  exact h

private theorem neg8_eq : ~~~(7 : BitVec 64) = (-8 : BitVec 64) := by decide

open virtaddr MemoryAccessType mem_payload in
/-- A byte load from the I/O window whose doubleword Sail holds retires with that byte.
For example, `LB x5, 3(x6)` at `0x40000010` writes the sign-extended byte `0x40000013`. -/
private theorem sail_load_b (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 1).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .byte (!u) D base imm)) := by
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 1 :=
    present_in_dword js.sail _ hb 1 (by omega)
  have hp : MemBytePresentAt js.sail (load_effective_address base imm).toNat :=
    hbytes.single_byte
  obtain ⟨hl, -⟩ := io_checks js.sail _ 1 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) (Nat.mod_one _)
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 1 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_1_eq_loaded_byte _ js.sail hbytes)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 1 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread (aligned_access_1 _) _ hmem]
  congr 2
  rw [loaded_byte_in_dword js.sail _ hb no hp, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_b_pext_signed]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_b_pext]

open virtaddr MemoryAccessType mem_payload in
/-- A halfword load from the I/O window whose doubleword Sail holds retires with that halfword.
For example, `LHU x5, 2(x6)` at `0x40000010` writes the zero-extended halfword at
`0x40000012`. -/
private theorem sail_load_h (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (1 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 2).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .halfword (!u) D base imm)) := by
  have hmod := mod_of_and1 _ hal
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 2 :=
    present_in_dword js.sail _ hb 2 (by omega)
  have hno : (load_effective_address base imm).toNat + 1 < 2 ^ 64 := by
    simp only [JoltISA.RAM_START_ADDRESS] at hhi; omega
  obtain ⟨hl, -⟩ := io_checks js.sail _ 2 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 2 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_2_eq_loaded_halfword _ js.sail hbytes hno)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 2 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread ⟨access_misaligned_2_aligned_false _ hal, split_misaligned_aligned_2 _ hal⟩ _ hmem]
  congr 2
  rw [loaded_halfword_in_dword js.sail _ hal hb no hbytes hno, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_h_pext_signed _ _ _ hal]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_h_pext _ _ _ hal]

open virtaddr MemoryAccessType mem_payload in
/-- A word load from the I/O window whose doubleword Sail holds retires with that word.
For example, `LW x5, 4(x6)` at `0x40000010` writes the sign-extended word at `0x40000014`. -/
private theorem sail_load_w (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (u : Bool) (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (3 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
    (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (D : BitVec 64)
    (hD : loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D) :
    (execute_LOAD imm rs1 rd u 4).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loadValue .word (!u) D base imm)) := by
  have hmod := mod_of_and3 _ hal
  have hbytes : MemBytesPresentAt js.sail (load_effective_address base imm) 4 :=
    present_in_dword js.sail _ hb 4 (by omega)
  have hno : (load_effective_address base imm).toNat + 3 < 2 ^ 64 := by
    simp only [JoltISA.RAM_START_ADDRESS] at hhi; omega
  obtain ⟨hl, -⟩ := io_checks js.sail _ 4 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 4 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_4_eq_loaded_word _ js.sail hbytes hno)
  rw [execute_LOAD_of_mem_read imm rs1 rd u 4 (by norm_num) (by norm_num) js.sail hpriv hmprv
    base hread ⟨access_misaligned_4_aligned_false _ hal, split_misaligned_aligned_4 _ hal⟩ _ hmem]
  congr 2
  rw [loaded_word_in_dword js.sail _ hal hb no hbytes hno, hD]
  cases u
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_w_pext_signed _ _ _ hal]
  · simp [extend_value, loadValue, extractValue, maskValue, window_mask_w_pext _ _ _ hal]

/-- Sign-extending a 64-bit value to 64 bits changes nothing.
For example, `sign_extend 0x8000000000000000` is `0x8000000000000000`. -/
private theorem sign_extend_64_eq_self' (v : BitVec 64) : sign_extend (m := 64) v = v := by
  simp [sign_extend, Sail.BitVec.signExtend]

open virtaddr MemoryAccessType mem_payload in
/-- A doubleword load from the I/O window whose bytes Sail holds retires with that doubleword.
For example, `LD x5, 8(x6)` at `0x40000010` writes the doubleword at `0x40000018`. -/
private theorem sail_load_d (js : SailJoltState) (imm : BitVec 12) (rs1 rd : regidx)
    (base : BitVec 64) (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hal : load_effective_address base imm &&& (7 : BitVec 64) = 0)
    (hlo : 0x40000000 ≤ (load_effective_address base imm).toNat)
    (hhi : (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hb : MemBytesPresentAt js.sail (load_effective_address base imm) 8)
    (no : (load_effective_address base imm).toNat + 7 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 8).run js.sail = .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd (loaded_dword_at js.sail (load_effective_address base imm) hb no)) := by
  have hmod := mod_of_and7 _ hal
  obtain ⟨hl, -⟩ := io_checks js.sail _ 8 hpma hlo (by norm_num) (by norm_num)
    (by simp only [JoltISA.RAM_START_ADDRESS] at hhi ⊢; omega) hmod
  obtain ⟨hmr, -⟩ := not_mmio_io js.sail _ 8 hlo hhtif
  have hmem := mem_read_of_plain _ js.sail hpriv hmprv _ hl hmr
    (read_ram_eq_loaded_dword _ js.sail hb no)
  rw [execute_LOAD_of_mem_read imm rs1 rd false 8 (by norm_num) (by norm_num) js.sail hpriv
    hmprv base hread (aligned_dword_access_of_align _ hal).toAlignedAccess _ hmem]
  simp only [extend_value, Bool.false_eq_true, ite_false]
  rw [sign_extend_64_eq_self']

/-! ### The effect of a narrow load -/

/-- A narrow load that retires in the I/O window leaves what Sail's load leaves.
From a retiring run of the three rows, Sail's `LOAD` retires to the same register write, and
the device is unchanged. -/
private theorem narrow_load_outcome (w : JoltISA.AccessWidth) (signed : Bool) (n : Nat)
    (dw lane : JoltISA.VReg) (dst : JoltISA.Dst) (hdw : WritableVReg dw)
    (hlane : WritableVReg lane) (hne : dw ≠ lane) (hdst : ∀ v, dst = .vreg v → WritableVReg v)
    (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hx0 : ∀ v, dst = .vreg v → JoltISA.isX0 rd = true) (hxr : ∀ r, dst = .xreg r → r = rd)
    (hinv : Step.StepInvariant js.sail) (hmem : MemoryReady js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (hsail : ∀ (base : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < RAM_START_ADDRESS →
      ∀ (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
        (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
        (D : BitVec 64),
        loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D →
        (execute_LOAD imm rs1 rd (!signed) n).run js.sail = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd (loadValue w signed D base imm)))
    (hrun : (JoltISA.execProgram (JoltISA.laneWindowOpen w (.vreg dw) (.vreg lane) (.xreg rs1)
        (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg dw) (.vreg lane) dst signed
          (.done RETIRE_SUCCESS)))).run js = .ok RETIRE_SUCCESS gp) :
    ∃ V, (execute_LOAD imm rs1 rd (!signed) n).run js.sail =
        .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device := by
  have hgeo := MemoryGeometry.of_layout _ hmem.layout
  have hread : rX_bits rs1 js.sail = .ok (sourceValue (.xreg rs1) js) js.sail :=
    (bundleHelper% source_read) js hinv rs1
  generalize hbase : sourceValue (.xreg rs1) js = base at hread hhi
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat =
      (load_effective_address base imm).toNat / 8 * 8 := by
    rw [← hea, neg8_eq, toNat_and_neg8]
  have hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    simp only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] at hhi ⊢
    omega
  obtain ⟨hal, D, hD, hdev, hxreg, hvreg⟩ :=
    loadRows_inv w signed dw lane dst hdw hlane hne hdst rs1 imm base js gp hread hlt hrun
  have hD' : JoltISA.Mmu.load_doubleword (load_effective_address base imm &&& (-8 : BitVec 64))
      js = .ok (.Ok D) js := by
    rw [hea, ← neg8_eq]
    exact hD
  have hA' := toNat_and_neg8 (load_effective_address base imm)
  have hlt' : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    simp only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] at hhi ⊢
    omega
  obtain ⟨hmod, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hlt' hD'
  cases hr
  have hlowA := read_lower js _ D hmem hlt' hrd
  have hlo40 : 0x40000000 ≤ (load_effective_address base imm).toNat := by
    have := hgeo.low
    omega
  obtain ⟨hb, no, hDeq⟩ := io_dword_eq js _ D hmem hmod hlowA
    hlt' hrd
  have hsl := hsail base hread hal hlo40 hhi hb no D hDeq
  refine ⟨_, hsl, ?_, hdev⟩
  cases dst with
  | xreg r =>
    obtain rfl := hxr r rfl
    exact hxreg r rfl
  | vreg v =>
    have hx := hx0 v rfl
    rw [hvreg v rfl, stateAfterWrite_of_isX0_eq_true hx]

/-! ### The effect of a doubleword load -/

private theorem ld_inv (rd rs1 : regidx) (imm : BitVec 12) (base : BitVec 64)
    (js gp : SailJoltState) (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0 ∧
      ∃ D, JoltISA.Mmu.load_doubleword (base + sign_extend (m := 64) imm) js = .ok (.Ok D) js ∧
        gp.jolt_device = js.jolt_device ∧ gp.sail = stateAfterWrite js.sail rd D ∧
        Projection.ProjectedVRegsPreserved js gp := by
  unfold JoltISA.ldNativeInstr at hrun
  simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind,
    EStateM.bind, EStateM.run, hread] at hrun
  by_cases halign : (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0
  · simp only [halign, ↓reduceIte] at hrun
    refine ⟨halign, ?_⟩
    cases hl : JoltISA.Mmu.load_doubleword (base + sign_extend (m := 64) imm) js with
    | ok r s' =>
      obtain ⟨-, D, hr, hs, -⟩ := load_doubleword_inv _ js s' r hlt hl
      subst hr
      subst hs
      refine ⟨D, rfl, ?_⟩
      simp only [EStateM.bind, hl] at hrun
      by_cases hx0 : JoltISA.isX0 rd = true
      · have hdst : JoltISA.sideEffectingRdZeroDst rd =
            JoltISA.Dst.vreg JoltISA.rdZeroRewriteVReg := by
          simp [JoltISA.sideEffectingRdZeroDst, hx0]
        have hnl : ¬ JoltISA.rdZeroRewriteVReg.toNat < 32 := by
          simp [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
            JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
            JoltISA.numReservedVirtualRegisters]
        rw [hdst] at hrun
        simp only [JoltISA.writeDst, writeVReg, hnl, ite_false, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure] at hrun
        simp only [EStateM.Result.ok.injEq, true_and] at hrun
        subst hrun
        refine ⟨rfl, (stateAfterWrite_of_isX0_eq_true hx0 _ _).symm, ?_⟩
        unfold Projection.ProjectedVRegsPreserved
        simp [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
          JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
          JoltISA.numReservedVirtualRegisters, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
          JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg,
          JoltISA.reservationWReg, JoltISA.reservationDReg]
      · have hdst : JoltISA.sideEffectingRdZeroDst rd = JoltISA.Dst.xreg rd := by
          simp [JoltISA.sideEffectingRdZeroDst, hx0]
        rw [hdst] at hrun
        simp only [JoltISA.writeDst, liftSail, wX_bits_stateAfterWrite, pure,
          EStateM.pure] at hrun
        simp only [EStateM.Result.ok.injEq, true_and] at hrun
        subst hrun
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | error e s' =>
      exfalso
      simp [EStateM.bind, hl] at hrun
  · exfalso
    simp only [halign, ↓reduceIte] at hrun
    simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this

/-- A doubleword load that retires in the I/O window leaves what Sail's load leaves.
From a retiring run of `LD`, Sail's `LOAD` retires to the same register write, and the
device is unchanged. -/
private theorem ld_outcome (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ V, (execute_LOAD imm rs1 rd false 8).run js.sail =
        .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device ∧
      Projection.ProjectedVRegsPreserved js gp := by
  have hgeo := MemoryGeometry.of_layout _ hmem.layout
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  have hread : rX_bits rs1 js.sail = .ok (sourceValue (.xreg rs1) js) js.sail :=
    (bundleHelper% source_read) js hinv rs1
  generalize hbase : sourceValue (.xreg rs1) js = base at hread hhi
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]
    simpa only [RAM_START_ADDRESS, JoltISA.RAM_START_ADDRESS] using hhi
  obtain ⟨hal, D, hD, hdev, hsail, hproj⟩ := ld_inv rd rs1 imm base js gp hread hlt hrun
  obtain ⟨hmod, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hlt hD
  cases hr
  have hmod' : (load_effective_address base imm).toNat % 8 = 0 := mod_of_and7 _ hal
  have hlowA := read_lower js _ D hmem hlt hrd
  have hlo40 : 0x40000000 ≤ (load_effective_address base imm).toNat := by
    have := hgeo.low
    omega
  obtain ⟨hb, no, hDeq⟩ := io_dword_eq js _ D hmem hmod hlowA hlt hrd
  have hDeq' : loaded_dword_at js.sail (load_effective_address base imm) hb no = D := hDeq
  have hsl := sail_load_d js imm rs1 rd base hpriv hmprv hpma hhtif hread hal hlo40 hhi hb no
  rw [hDeq'] at hsl
  exact ⟨D, hsl, hsail, hdev, hproj⟩

/-! ### Loads, assembled -/

/-- A load whose Sail register write matches Jolt's is a faithful step.
From Sail's retiring `LOAD` and Jolt's final state, which differ only by the write of `V`
to `rd` and by scratch registers, the conclusion of `io_core` follows. -/
private theorem load_finish (ast : instruction) (rd : regidx) (js gp : SailJoltState)
    (V : BitVec 64) (hlink : System.systemProject js = js.sail)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hexec : execute ast js.sail = .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V))
    (hgp : gp.sail = stateAfterWrite js.sail rd V) (hdev : gp.jolt_device = js.jolt_device)
    (hproj : Projection.ProjectedVRegsPreserved js gp) :
    ∃ t : SailState, execute ast js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  refine ⟨stateAfterWrite js.sail rd V, hexec, ?_, fun a => by rw [hgp], ?_⟩
  · rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved js gp rd V hgp hproj,
      hlink]
  · rw [hdev]
    exact hmem.of_mem_eq rfl

/-- A narrow load in the I/O window, from the rows of its expansion to Sail's `execute`.
The expansion has two shapes, one for `rd = x0`, which only writes scratch registers. -/
private theorem narrow_load_core (w : JoltISA.AccessWidth) (signed : Bool) (n : Nat)
    (rd rs1 : regidx) (imm : BitVec 12) (prog : JoltISA.Program) (js gp : SailJoltState)
    (hprog0 : JoltISA.isX0 rd = true → prog =
      JoltISA.laneWindowOpen w (.vreg (BitVec.ofNat 7 41)) (.vreg (BitVec.ofNat 7 42))
        (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg (BitVec.ofNat 7 41)) (.vreg (BitVec.ofNat 7 42))
          (.vreg (BitVec.ofNat 7 40)) signed (.done RETIRE_SUCCESS)))
    (hprog1 : ¬ JoltISA.isX0 rd = true → prog =
      JoltISA.laneWindowOpen w (.vreg (BitVec.ofNat 7 40)) (.vreg (BitVec.ofNat 7 41))
        (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
        (JoltISA.laneWindowExtract (.vreg (BitVec.ofNat 7 40)) (.vreg (BitVec.ofNat 7 41))
          (.xreg rd) signed (.done RETIRE_SUCCESS)))
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (hsail : ∀ (base : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < RAM_START_ADDRESS →
      ∀ (hb : MemBytesPresentAt js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) 8)
        (no : (load_effective_address base imm &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
        (D : BitVec 64),
        loaded_dword_at js.sail (load_effective_address base imm &&& (-8 : BitVec 64)) hb no = D →
        (execute_LOAD imm rs1 rd (!signed) n).run js.sail = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd (loadValue w signed D base imm)))
    (hrun : (JoltISA.execProgram prog).run js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.LOAD (imm, rs1, rd, !signed, n)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  have hw : ∀ k, WritableVReg (BitVec.ofNat 7 k) ↔ 32 ≤ k % 128 := fun k => by
    simp [WritableVReg, BitVec.toNat_ofNat]
  obtain ⟨V, hexec, hgp, hdev⟩ : ∃ V, (execute_LOAD imm rs1 rd (!signed) n).run js.sail =
      .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd V) ∧
      gp.sail = stateAfterWrite js.sail rd V ∧ gp.jolt_device = js.jolt_device := by
    by_cases hx : JoltISA.isX0 rd = true
    · rw [hprog0 hx] at hrun
      exact narrow_load_outcome w signed n _ _ _ (by rw [hw]; decide) (by rw [hw]; decide)
        (by decide) (by intro v h; cases h; rw [hw]; decide) rd rs1 imm js gp
        (by intro v _; exact hx) (by intro r h; cases h) hinv hmem hhi hsail hrun
    · rw [hprog1 hx] at hrun
      exact narrow_load_outcome w signed n _ _ _ (by rw [hw]; decide) (by rw [hw]; decide)
        (by decide) (by intro v h; cases h) rd rs1 imm js gp
        (by intro v h; cases h) (by intro r h; cases h; rfl) hinv hmem hhi hsail hrun
  exact load_finish _ rd js gp V hlink hmem hexec hgp hdev hproj

/-- A doubleword load in the I/O window, from the native `LD` row to Sail's `execute`. -/
private theorem ld_core (rd rs1 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.LOAD (imm, rs1, rd, false, 8)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  obtain ⟨V, hexec, hgp, hdev, hproj⟩ := ld_outcome rd rs1 imm js gp hinv hlink hmstatus hmem hpma hhtif
    hhi hrun
  exact load_finish _ rd js gp V hlink hmem hexec hgp hdev hproj

/-- A classified ordinary load supplies its below-RAM address.
For example, the LB classification gives the upper bound for its containing word. -/
private theorem load_access (i : RiscvInstruction) (js : SailJoltState) (rs1 : regidx)
    (imm : BitVec 12) (n : Nat) (_hn : 0 < n)
    (hacc : i.memAccess js = some (false, n, load_effective_address (sourceValue (.xreg rs1) js) imm))
    (hio : i.IoAccess js) :
    (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < RAM_START_ADDRESS := by
  obtain ⟨store, width, ea, same, upper⟩ := hio
  rw [hacc] at same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨_, _, rfl⟩ := same
  exact upper

/-! ### Jolt's device writes -/

/-- A fold of failing-on-`none` steps that starts failing stays failing.
For example, folding `Option.bind` steps from `none` gives `none`. -/
private theorem foldl_bind_none (g : Nat → SailJoltState → Option SailJoltState) (l : List Nat) :
    l.foldl (fun cur k => cur.bind (g k)) none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldl_cons, Option.bind_none] using ih

/-- A fold over eight steps that succeeds has a successful first step.
For example, if the first byte store fails, so does the doubleword store. -/
private theorem foldl_range_first (g : Nat → SailJoltState → Option SailJoltState)
    (s s' : SailJoltState) (n : Nat)
    (h : (List.range (n + 1)).foldl (fun cur k => cur.bind (g k)) (some s) = some s') :
    ∃ s1, g 0 s = some s1 := by
  rw [List.range_succ_eq_map, List.foldl_cons] at h
  cases hg : g 0 s with
  | none =>
    simp only [Option.bind_some, hg] at h
    rw [foldl_bind_none] at h
    cases h
  | some s1 => exact ⟨s1, rfl⟩

/-- A successful byte store below RAM passed the address check.
For example, a store at `0x40000010` that succeeds had `effective_address_ok` true there. -/
private theorem store_raw_below_ok (s s1 : SailJoltState) (a : Nat) (x : BitVec 8)
    (_hlt : a < JoltISA.RAM_START_ADDRESS) (h : JoltISA.Mmu.store_raw? s a x = some s1) :
    JoltISA.Mmu.effective_address_ok s.jolt_device a true = true := by
  by_contra failed
  have no : Mmu.effective_address_ok s.jolt_device a true = false := Bool.eq_false_iff.mpr failed
  simp only [Mmu.store_raw?, no, Bool.not_false, ite_true] at h
  cases h

/-- A retiring doubleword store below RAM is aligned and passed the first byte's check.
For example, a store at `0x40000008` that retires has `effective_address_ok` true there. -/
private theorem store_doubleword_below_inv (A V : BitVec 64) (js js' : SailJoltState)
    (r : Result Bool ExecutionResult) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (h : JoltISA.Mmu.store_doubleword A V js = .ok r js') :
    A.toNat % 8 = 0 ∧ r = .Ok true ∧
      JoltISA.Mmu.effective_address_ok js.jolt_device A.toNat true = true := by
  unfold JoltISA.Mmu.store_doubleword at h
  have hnle : ¬ JoltISA.RAM_START_ADDRESS ≤ A.toNat := by omega
  by_cases hal : A.toNat % 8 = 0
  · simp only [hal, ne_eq, not_true_eq_false, ite_false, hnle] at h
    split at h
    · rename_i s' hs
      cases h
      refine ⟨hal, rfl, ?_⟩
      obtain ⟨s1, hs1⟩ := foldl_range_first
        (fun k s => JoltISA.Mmu.store_raw? s (A.toNat + k) (V.extractLsb' (8 * k) 8)) js _ 7 hs
      exact store_raw_below_ok js s1 _ _ (by simpa using hlt) hs1
    · simp at h
  · simp [hal] at h

/-- A retiring floor store row is the doubleword store of its scratch register.
For example, if `VirtualStoreW` retires, `store_doubleword` of the containing doubleword
retired, with the register's value. -/
private theorem floorStore_inv (w : JoltISA.AccessWidth) (rs1 : regidx) (vv : JoltISA.VReg)
    (imm base : BitVec 64) (f : ExceptionType) (js js' : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok base js.sail)
    (hlt : ((base + imm) &&& ~~~(7 : BitVec 64)).toNat < JoltISA.RAM_START_ADDRESS)
    (halign : (base + imm) &&& LoadFamily.alignmentMask w = 0)
    (h : (JoltISA.execInstr ((storeHelper% floorStoreRow) w (.xreg rs1) vv imm f)).run js =
      .ok RETIRE_SUCCESS js') :
    JoltISA.Mmu.store_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) (js.vregs vv) js =
      .ok (.Ok true) js' := by
  have hrow : (storeHelper% floorStoreRow) w (.xreg rs1) vv imm f =
      match w with
      | .byte => .VirtualStoreB (.xreg rs1) (.vreg vv) imm f
      | .halfword => .VirtualStoreH (.xreg rs1) (.vreg vv) imm f
      | .word => .VirtualStoreW (.xreg rs1) (.vreg vv) imm f := by
    cases w <;> rfl
  rw [hrow] at h
  cases hs : JoltISA.Mmu.store_doubleword ((base + imm) &&& ~~~(7 : BitVec 64)) (js.vregs vv) js with
  | ok r s' =>
    obtain ⟨-, hr, -⟩ := store_doubleword_below_inv _ _ js s' r hlt hs
    subst hr
    cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
      simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
        hread, halign, ↓reduceIte, readVReg, get, getThe, MonadStateOf.get, EStateM.get, pure,
        EStateM.pure, hs] at h <;>
      simp only [EStateM.Result.ok.injEq, true_and] at h <;>
      rw [h]
  | error e s' =>
    exfalso
    cases w <;> simp only [LoadFamily.alignmentMask] at halign <;>
      simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
        hread, halign, ↓reduceIte, readVReg, get, getThe, MonadStateOf.get, EStateM.get, pure,
        EStateM.pure, hs] at h <;>
      simp at h

/-- A retiring narrow store program loads, splices and stores a doubleword.
From a retiring run of the six rows, the effective address is aligned for the width, the
containing doubleword was read as `D`, and the doubleword with the stored bytes spliced in
was stored from a state with the same Sail state and device. -/
private theorem storeRows_inv (w : JoltISA.AccessWidth) (rs1 rs2 : regidx) (imm : BitVec 12)
    (base val : BitVec 64) (js gp : SailJoltState)
    (hr1 : rX_bits rs1 js.sail = .ok base js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hlt : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execProgram (StoreProgramBlocks.laneStoreProgram w rs1 rs2
        (sign_extend (m := 64) imm))).run js = .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& LoadFamily.alignmentMask w = 0 ∧
      ∃ (D : BitVec 64) (js_s : SailJoltState),
        JoltISA.Mmu.load_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)) js = .ok (.Ok D) js ∧
        js_s.sail = js.sail ∧ js_s.jolt_device = js.jolt_device ∧
        JoltISA.Mmu.store_doubleword
          ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64))
          (StoreProgramBlocks.fusedSpliceValue w D val (base + sign_extend (m := 64) imm)) js_s =
          .ok (.Ok true) gp := by
  rw [(storeHelper% laneStoreProgram_rows)] at hrun
  have hrun' : (JoltISA.execProgram (.instr
      (LoadFamily.floorLoadRow w (.vreg 40) (.xreg rs1) (sign_extend (m := 64) imm) .normal
        (ExceptionType.E_SAMO_Addr_Align ()))
      (((storeHelper% fusedSpliceProgram) w 40 41 rs1 rs2 (sign_extend (m := 64) imm)).append
        (.instr ((storeHelper% floorStoreRow) w (.xreg rs1) 40 (sign_extend (m := 64) imm)
          (ExceptionType.E_SAMO_Addr_Align ())) (.done RETIRE_SUCCESS))))).run js =
      .ok RETIRE_SUCCESS gp := hrun
  obtain ⟨js1, h1, hrest⟩ := execProgram_instr_run_retire_inv _ _ js gp hrun'
  obtain ⟨hal, D, hD⟩ := floorLoad_inv w 40 rs1 (sign_extend (m := 64) imm) base .normal
    (ExceptionType.E_SAMO_Addr_Align ()) js js1 hr1 hlt h1
  have e1 := LoadFamily.floorLoad_run w 40 rs1 (sign_extend (m := 64) imm) base D .normal
    (ExceptionType.E_SAMO_Addr_Align ()) js hr1 hal hD (by unfold WritableVReg; decide)
  have hj1 : js1 = stateAfterVRegWrite js 40 D := by
    have := h1.symm.trans e1
    simpa only [EStateM.Result.ok.injEq, true_and] using this
  subst hj1
  obtain ⟨js_s, hsplice, hsail, hdword, hdev⟩ := (storeHelper% fusedSpliceBlock) w 40 41
    (by decide) (by unfold WritableVReg; decide) (by unfold WritableVReg; decide) rs1 rs2
    (sign_extend (m := 64) imm) base val (stateAfterVRegWrite js 40 D) hr1 hr2
  obtain ⟨js2, hs2, hlast⟩ := JoltISA.execProgram_append_succeeds_inv _ _ _ gp hrest
  have hj2 : js2 = js_s := by
    unfold JoltISA.Program.Run at hsplice
    have := hs2.symm.trans hsplice
    simpa only [EStateM.Result.ok.injEq, true_and] using this
  subst hj2
  obtain ⟨js3, h3, hdone⟩ := execProgram_instr_run_retire_inv _ _ _ gp hlast
  have hj3 : js3 = gp := by
    simpa [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] using hdone
  subst hj3
  have hsd := floorStore_inv w rs1 40 (sign_extend (m := 64) imm) base _ js2 js3 (by rw [hsail]; exact hr1)
    hlt hal h3
  have hv40 : js2.vregs 40 = StoreProgramBlocks.fusedSpliceValue w D val
      (base + sign_extend (m := 64) imm) := by
    rw [hdword]
    simp [stateAfterVRegWrite]
  rw [hv40] at hsd
  exact ⟨hal, D, js2, hD, by simpa [stateAfterVRegWrite] using hsail,
    by simpa [stateAfterVRegWrite] using hdev, hsd⟩

/-- A retiring `SD` is an aligned doubleword store of the source register.
For example, `SD` at an aligned I/O address retires only if `store_doubleword` does. -/
private theorem sd_inv (rs1 rs2 : regidx) (imm : BitVec 12) (base val : BitVec 64)
    (js gp : SailJoltState) (hr1 : rX_bits rs1 js.sail = .ok base js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok val js.sail)
    (hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0 ∧
      JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val js =
        .ok (.Ok true) gp := by
  unfold JoltISA.Encoded.SD at hrun
  simp only [JoltISA.execInstr, JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run,
    hr1, hr2] at hrun
  by_cases halign : (base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0
  · refine ⟨halign, ?_⟩
    simp only [halign, ↓reduceIte] at hrun
    change EStateM.bind (JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val)
      _ js = _ at hrun
    cases hs : JoltISA.Mmu.store_doubleword (base + sign_extend (m := 64) imm) val js with
    | ok r s' =>
      obtain ⟨-, hr, -⟩ := store_doubleword_below_inv _ _ js s' r hlt hs
      subst hr
      simp only [EStateM.bind, hs, pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at hrun
      rw [hrun]
    | error e s' =>
      exfalso
      simp [EStateM.bind, hs] at hrun
  · exfalso
    simp only [halign, ↓reduceIte, pure, EStateM.pure, EStateM.Result.ok.injEq] at hrun
    have := hrun.1
    simp [RETIRE_SUCCESS] at this

/-- The shared containing-word store has Sail's narrow-store bytes and retains
allocation and the device; for example, SB preserves its other seven word bytes. -/
private theorem store_finish (js js_s gp : SailJoltState) (t : SailState)
    (A W ea val D : BitVec 64) (n : Nat)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hs1 : js_s.sail = js.sail) (hs2 : js_s.jolt_device = js.jolt_device)
    (_hn : 0 < n) (hA : A.toNat = ea.toNat / 8 * 8) (hwin : ea.toNat % 8 + n ≤ 8)
    (hDb : ∀ k < 8, ¬ (ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n) →
      D.extractLsb' (8 * k) 8 = Mmu.ram_byte js.sail.mem (A.toNat + k))
    (hWb : ∀ k < 8, W.extractLsb' (8 * k) 8 =
      if ea.toNat % 8 ≤ k ∧ k < ea.toNat % 8 + n then
        val.extractLsb' (8 * (k - ea.toNat % 8)) 8 else D.extractLsb' (8 * k) 8)
    (_hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (hst : JoltISA.Mmu.store_doubleword A W js_s = .ok (.Ok true) gp)
    (hsail : SailStore js.sail t ea n val) :
    gp.sail.regs = js.sail.regs ∧ gp.jolt_device = js.jolt_device ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  have lane : SailStore js_s.sail t ea n val := by rwa [hs1]
  obtain ⟨device, registers, bytes, present⟩ := shared_store_finish js_s gp t A W ea val D n
    hst lane hA hwin (by simpa only [hs1] using hDb) hWb
  have sameDevice := device.trans hs2
  refine ⟨registers.symm.trans hsail.1, sameDevice, bytes, ?_⟩
  rw [sameDevice]
  exact ⟨fun a lower upper => hsail.preserves_present a (hmem.present a lower upper), hmem.layout⟩

/-- An admitted below-RAM word lies wholly in Sail's plain I/O region.
For example, an aligned gap word is bounded by RAM and above the lowest address. -/
private theorem store_bounds (js gp : SailJoltState) (A V : BitVec 64)
    (hmem : MemoryReady js.jolt_device js.sail) (hlt : A.toNat < JoltISA.RAM_START_ADDRESS)
    (stored : Mmu.store_doubleword A V js = .ok (.Ok true) gp) :
    0x40000000 ≤ A.toNat ∧ A.toNat + 8 ≤ JoltISA.RAM_START_ADDRESS := by
  obtain ⟨aligned, _, checked⟩ := store_doubleword_below_inv A V js gp (.Ok true) hlt stored
  have mapped : js.jolt_device.readable A.toNat = true := by
    simpa only [Mmu.effective_address_ok, hlt, ite_true] using checked
  have lower := readable_lower js.jolt_device hmem.layout A.toNat mapped
  have geometry := MemoryGeometry.of_layout js.jolt_device hmem.layout
  have platformLower := geometry.low
  simp only [JoltISA.RAM_START_ADDRESS] at hlt ⊢
  omega

/-- A transition that preserves architectural registers and projected virtual registers
preserves the projected register map; for example, a shared-memory store. -/
private theorem systemProject_of_store (js gp : SailJoltState) (registers : gp.sail.regs = js.sail.regs)
    (hproj : Projection.ProjectedVRegsPreserved js gp) :
    (System.systemProject gp).regs = (System.systemProject js).regs := by
  rcases hproj with ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus, hresW, hresD⟩
  simp only [System.systemProject, Step.setReg, registers, hmtvec, hmscratch, hmepc,
    hmcause, hmtval, hmstatus, hresW, hresD]

/-- Classification of an ordinary store supplies its below-RAM address.
For example, SD retains the source address computed by `memAccess`. -/
private theorem store_access (i : RiscvInstruction) (js : SailJoltState) (rs1 : regidx)
    (imm : BitVec 12) (n : Nat)
    (hacc : i.memAccess js = some (true, n, load_effective_address (sourceValue (.xreg rs1) js) imm))
    (hio : i.IoAccess js) :
    (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat < JoltISA.RAM_START_ADDRESS := by
  obtain ⟨store, width, ea, same, upper⟩ := hio
  rw [hacc] at same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨_, _, rfl⟩ := same
  exact upper

/-! ### Stores, assembled -/

/-- A narrow store in the I/O window, from the rows of its expansion to Sail's `execute`.
Jolt loads the doubleword around the access, splices the stored bytes in and stores it;
Sail stores the bytes alone. -/
private theorem narrow_store_core (w : JoltISA.AccessWidth) (n : Nat) (hn : 0 < n)
    (hfit : ∀ x : BitVec 64, x &&& LoadFamily.alignmentMask w = 0 → x.toNat % 8 + n ≤ 8)
    (rs1 rs2 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hproj : Projection.ProjectedVRegsPreserved js gp)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hsplice : ∀ (b D V : BitVec 64), load_effective_address b imm &&&
        LoadFamily.alignmentMask w = 0 → ∀ k < 8,
      (StoreProgramBlocks.fusedSpliceValue w D V
          (load_effective_address b imm)).extractLsb' (8 * k) 8 =
        if (load_effective_address b imm).toNat % 8 ≤ k ∧
            k < (load_effective_address b imm).toNat % 8 + n then
          V.extractLsb' (8 * (k - (load_effective_address b imm).toNat % 8)) 8
        else D.extractLsb' (8 * k) 8)
    (hsail : ∀ (base val : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      rX_bits rs2 js.sail = .ok val js.sail →
      load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS →
      ∃ t : SailState, (execute_STORE imm rs2 rs1 n).run js.sail = .ok RETIRE_SUCCESS t ∧
        SailStore js.sail t (load_effective_address base imm) n val)
    (hrun : (JoltISA.execProgram (StoreProgramBlocks.laneStoreProgram w rs1 rs2
        (sign_extend (m := 64) imm))).run js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.STORE (imm, rs2, rs1, n)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  generalize sourceValue (.xreg rs1) js = base at hr1 hhi
  generalize sourceValue (.xreg rs2) js = val at hr2
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]; exact hhi
  have hltA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat <
      JoltISA.RAM_START_ADDRESS := by
    rw [neg8_eq, toNat_and_neg8]
    omega
  obtain ⟨hal, D, js_s, hD, hs1, hs2, hst⟩ :=
    storeRows_inv w rs1 rs2 imm base val js gp hr1 hr2 hltA hrun
  have hmem_s : MemoryReady js_s.jolt_device js_s.sail := by rw [hs1, hs2]; exact hmem
  obtain ⟨hlo40, hhi8⟩ := store_bounds js_s gp _ _ hmem_s hltA hst
  have hal' : load_effective_address base imm &&& LoadFamily.alignmentMask w = 0 := hal
  have hfit' := hfit _ hal'
  have hA : ((base + sign_extend (m := 64) imm) &&& ~~~(7 : BitVec 64)).toNat =
      (load_effective_address base imm).toNat / 8 * 8 := by
    rw [neg8_eq, toNat_and_neg8]
  obtain ⟨-, D', hr, -, hrd⟩ := load_doubleword_inv _ js js _ hltA hD
  cases hr
  have hDb : ∀ k < 8, ¬ ((load_effective_address base imm).toNat % 8 ≤ k ∧
      k < (load_effective_address base imm).toNat % 8 + n) →
      D.extractLsb' (8 * k) 8 =
        Mmu.ram_byte js.sail.mem (((base + sign_extend (m := 64) imm) &&&
          ~~~(7 : BitVec 64)).toNat + k) := by
    intro k hk _
    exact (JoltConstraints.load_raw_value js _ _ (read_doubleword_bytes hrd k hk)).symm
  obtain ⟨t, hex, hst'⟩ := hsail base val hr1 hr2 hal' (by omega) hhi
  obtain ⟨hgp, hdevice, hbytes, hmemT⟩ := store_finish js js_s gp t _ _ (load_effective_address base imm) val D
    n hmem hs1 hs2 hn hA hfit' hDb (hsplice base D val hal') hltA hst hst'
  refine ⟨t, hex, ?_, ?_, hmemT⟩
  · rw [systemProject_of_store js gp hgp hproj, hlink]
    exact hst'.1
  · exact hbytes

/-- A doubleword store in the I/O window, from the native `SD` row to Sail's `execute`. -/
private theorem sd_core (rs1 rs2 : regidx) (imm : BitVec 12) (js gp : SailJoltState)
    (hinv : Step.StepInvariant js.sail) (hlink : System.systemProject js = js.sail)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hhi : (load_effective_address (sourceValue (.xreg rs1) js) imm).toNat <
      JoltISA.RAM_START_ADDRESS)
    (hsail : ∀ (base val : BitVec 64), rX_bits rs1 js.sail = .ok base js.sail →
      rX_bits rs2 js.sail = .ok val js.sail →
      load_effective_address base imm &&& (7 : BitVec 64) = 0 →
      0x40000000 ≤ (load_effective_address base imm).toNat →
      (load_effective_address base imm).toNat < JoltISA.RAM_START_ADDRESS →
      ∃ t : SailState, (execute_STORE imm rs2 rs1 8).run js.sail = .ok RETIRE_SUCCESS t ∧
        SailStore js.sail t (load_effective_address base imm) 8 val)
    (hrun : (JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js =
      .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute (.STORE (imm, rs2, rs1, 8)) js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  have hr1 := (bundleHelper% source_read) js hinv rs1
  have hr2 := (bundleHelper% source_read) js hinv rs2
  generalize sourceValue (.xreg rs1) js = base at hr1 hhi
  generalize sourceValue (.xreg rs2) js = val at hr2
  have hea : load_effective_address base imm = base + sign_extend (m := 64) imm := rfl
  have hlt : (base + sign_extend (m := 64) imm).toNat < JoltISA.RAM_START_ADDRESS := by
    rw [← hea]; exact hhi
  obtain ⟨hal, hst⟩ := sd_inv rs1 rs2 imm base val js gp hr1 hr2 hlt hrun
  obtain ⟨hlo40, hhi8⟩ := store_bounds js gp _ _ hmem hlt hst
  rw [← hea] at hlo40 hhi8
  have hal' : load_effective_address base imm &&& (7 : BitVec 64) = 0 := hal
  have hmod := mod_of_and7 _ hal'
  have hproj : Projection.ProjectedVRegsPreserved js gp := by
    have shape := JoltConstraints.store_doubleword_shape js gp _ _ (.Ok true) hst
    rw [shape]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨t, hex, hst'⟩ := hsail base val hr1 hr2 hal' (by omega) hhi
  obtain ⟨hgp, hdevice, hbytes, hmemT⟩ := store_finish js js gp t (load_effective_address base imm) val
    (load_effective_address base imm) val val 8 hmem rfl rfl (by omega) (by omega) (by omega)
    (fun k hk h => by exfalso; apply h; omega)
    (fun k hk => by rw [ite_eq_left (by omega), hmod, Nat.sub_zero]) hlt hst hst'
  refine ⟨t, hex, ?_, ?_, hmemT⟩
  · rw [systemProject_of_store js gp hgp hproj, hlink]
    exact hst'.1
  · exact hbytes
/-! ### The effect of one I/O access -/

/-- One load or store in Sail's I/O window agrees with Jolt's rows.
From Jolt's retiring run of the instruction's rows, Sail's `execute` retires to a state
whose registers are the projection of Jolt's, whose RAM is Jolt's and whose memory
satisfies the memory relation with Jolt's device. -/
private theorem io_core (i : RiscvInstruction) (ast : instruction)
    (hm : RiscvInstruction.Matches i ast) (js gp : SailJoltState)
    (hio : i.IoAccess js)
    (hlink : System.systemProject js = js.sail) (hinv : Step.StepInvariant js.sail)
    (hmstatus : js.vregs mstatusVReg &&& ~~~(0x88 : BitVec 64) = 0)
    (hmem : MemoryReady js.jolt_device js.sail)
    (hpma : js.sail.regs.get? Register.pma_regions = some platformPma)
    (hhtif : js.sail.regs.get? Register.htif_tohost_base = some none)
    (hrun : RiscvInstruction.joltRun (honestInstr i js) js = .ok RETIRE_SUCCESS gp) :
    ∃ t : SailState, execute ast js.sail = .ok RETIRE_SUCCESS t ∧
      t.regs = (System.systemProject gp).regs ∧
      (∀ a, Mmu.ram_byte t.mem a = Mmu.ram_byte gp.sail.mem a) ∧
      MemoryReady gp.jolt_device t := by
  have hpriv : Assumptions.CurPrivilegeMachine js.sail := ⟨hinv.machine⟩
  have hmprv := (bundleHelper% mprv_zero) js hlink hmstatus
  cases i with
  | LB rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 1) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 1 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .byte true 1 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lbProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lbProgramAuto, hx]; rfl)
      (LB_main.lbProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_b js imm rs1 rd false base hpriv hmprv hpma hhtif hr hlo' hhi' hb no D hD)
      hrun
  | LH rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 2) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 2 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .halfword true 2 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lhProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lhProgramAuto, hx]; rfl)
      (LH_main.lhProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_h js imm rs1 rd false base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LW rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 4) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 4 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .word true 4 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lwProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lwProgramAuto, hx]; rfl)
      (LW_main.lwProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_w js imm rs1 rd false base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LBU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 1) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 1 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lbuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .byte false 1 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lbuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lbuProgramAuto, hx]; rfl)
      (LBU_main.lbuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_b js imm rs1 rd true base hpriv hmprv hpma hhtif hr hlo' hhi' hb no D hD)
      hrun
  | LHU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 2) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 2 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .halfword false 2 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lhuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lhuProgramAuto, hx]; rfl)
      (LHU_main.lhuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_h js imm rs1 rd true base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LWU rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, true, 4) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 4 (by norm_num) rfl hio
    change (JoltISA.execProgram (JoltISA.lwuProgramAuto rd rs1 imm)).run js = _ at hrun
    exact narrow_load_core .word false 4 rd rs1 imm _ js gp
      (fun hx => by simp only [JoltISA.lwuProgramAuto, hx]; rfl)
      (fun hx => by simp only [JoltISA.lwuProgramAuto, hx]; rfl)
      (LWU_main.lwuProgramAuto_preserves_projected_vregs imm rs1 rd hrun) hinv hlink hmem hhi
      (fun base hr hal hlo' hhi' hb no D hD =>
        sail_load_w js imm rs1 rd true base hpriv hmprv hpma hhtif hr hal hlo' hhi' hb no D hD)
      hrun
  | LD rd rs1 imm =>
    have hm' : ast = .LOAD (imm, rs1, rd, false, 8) := hm
    subst hm'
    have hhi := load_access _ js rs1 imm 8 (by norm_num) rfl hio
    change (JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)).run js = _ at hrun
    exact ld_core rd rs1 imm js gp hinv hlink hmstatus hmem hpma hhtif hhi hrun
  | SB rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 1) := hm
    subst hm'
    have hhi := store_access _ js rs1 imm 1 rfl hio
    change (JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .byte 1 (by norm_num)
      (fun x _ => by omega)
      rs1 rs2 imm js gp (SB_main.sbProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi
      (fun b D V _ k hk => fusedSplice_byte_b D V b imm k hk)
      (fun base val hr1 hr2 _ hlo hhi' =>
        ⟨_, sail_store_b js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hlo hhi',
          sailStore_byte js.sail _ val⟩) hrun
  | SH rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 2) := hm
    subst hm'
    have hhi := store_access _ js rs1 imm 2 rfl hio
    change (JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .halfword 2 (by norm_num)
      (fun x hx => by
        have := mod_of_and1 x (by simpa [LoadFamily.alignmentMask] using hx)
        omega)
      rs1 rs2 imm js gp (SH_main.shProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi
      (fun b D V hal k hk => fusedSplice_byte_h D V b imm hal k hk)
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_h js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_halfword js.sail _ val⟩) hrun
  | SW rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 4) := hm
    subst hm'
    have hhi := store_access _ js rs1 imm 4 rfl hio
    change (JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)).run js = _ at hrun
    exact narrow_store_core .word 4 (by norm_num)
      (fun x hx => by
        have := mod_of_and3 x (by simpa [LoadFamily.alignmentMask] using hx)
        omega)
      rs1 rs2 imm js gp (SW_main.swProgramAuto_preserves_projected_vregs imm rs2 rs1 hrun)
      hinv hlink hmem hhi
      (fun b D V hal k hk => fusedSplice_byte_w D V b imm hal k hk)
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_w js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_word js.sail _ val⟩) hrun
  | SD rs2 rs1 imm =>
    have hm' : ast = .STORE (imm, rs2, rs1, 8) := hm
    subst hm'
    have hhi := store_access _ js rs1 imm 8 rfl hio
    change (JoltISA.execInstr (Encoded.SD (.xreg rs1) (.xreg rs2) imm)).run js = _ at hrun
    exact sd_core rs1 rs2 imm js gp hinv hlink hmem hhi
      (fun base val hr1 hr2 hal hlo hhi' =>
        ⟨_, sail_store_d js imm rs2 rs1 base val hpriv hmprv hpma hhtif hr1 hr2 hal hlo hhi',
          sailStore_dword js.sail _ val⟩) hrun
  | _ =>
    obtain ⟨_, _, _, h, _⟩ := hio
    simp [RiscvInstruction.memAccess] at h

/-- A retiring ordinary load or store below RAM simulates one Sail step and preserves
`Related`, including shared bytes at every address.
The mapped-region guards follow from the retiring row run.
For example, SB in the output region changes its byte in both shared maps.
The `via` variant permits an equivalent compressed instruction after decoding. -/
theorem block_simulates_io_via (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hsys : SystemInv b.pre) (hio : i.IoAccess b.start)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        ∃ (ast cast : instruction), RiscvInstruction.Matches i ast ∧
        (∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok cast (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  intro s hrel
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  obtain ⟨inc, hinc, hfetch, ast, cast, hm, hbridge, hdecode⟩ :=
    hinputs s hrel pc m oldInc hnext hregs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  let Gs := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  have hshadow : Shadow ((blockHelper% overlayRows) b.pre.vregs m inc b.start) Gs :=
    (blockHelper% prelude_shadow) b s pc m oldInc inc hp hregs hrel.ram
  have hlift : i.Lifted := by
    clear hinputs hdecode hfetch
    obtain ⟨store, width, ea, hacc, _⟩ := hio
    cases i <;> simp_all [RiscvInstruction.memAccess, RiscvInstruction.Lifted]
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes
  have hadvice : blockInstrs b.row Gs = blockInstrs b.row b.start := by
    have he := ((blockHelper% advice_shadow) i _ _ hshadow).trans
      ((blockHelper% advice_overlayRows) i b.pre.vregs m inc b.start)
    simp only [blockInstrs, hrow, he]
  have hpatched := (blockHelper% execProgram_overlayRows) (Program.seq instrs)
    b.pre.vregs m inc b.start b.post hrun
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hpatched] at hsync
  obtain ⟨ghostPost, hghost, hpost, _, _⟩ := hsync.ok_exists
  have hrawG := blockInstrs_run i b.row.address b.row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hhonest : RiscvInstruction.joltRun (honestInstr i Gs) Gs = .ok RETIRE_SUCCESS ghostPost :=
    hrawG.symm.trans hghost
  have hGp : System.systemProject Gs = Step.preludeState s inc pc
      (if b.row.is_compressed then 2 else 4) := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, (blockHelper% ghost_projects) hrel]
  have hlink : System.systemProject Gs = Gs.sail := hGp
  have hinvG : Step.StepInvariant Gs.sail := hrel.inv.preludeState inc pc _
  have hsources : ∀ r, sourceValue (.xreg r) Gs = sourceValue (.xreg r) b.start := fun r =>
    ((blockHelper% sourceValue_shadow) hshadow r).trans
      ((blockHelper% sourceValue_overlayRows) b.pre.vregs m inc b.start r)
  have hio' := access_congr i b.start Gs hsources
  have hmemG : MemoryReady Gs.jolt_device Gs.sail := hrel.memoryReady.of_mem_eq rfl
  have hpmaG : Gs.sail.regs.get? Register.pma_regions = some platformPma := by
    simp [Gs, Step.preludeJolt, Step.preludeState, Step.setReg, hregs,
      sailRegs, Std.ExtDHashMap.get?_insert]
  have hhtifG : Gs.sail.regs.get? Register.htif_tohost_base = some none := by
    simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg,
      Std.ExtDHashMap.get?_insert] using hrel.htif
  obtain ⟨t, hexec, htregs, htram, htmem⟩ := io_core i ast hm Gs ghostPost
    (hio' hio) hlink hinvG hsys.mstatus_bits
    hmemG hpmaG hhtifG hhonest
  have hexec' : execute ast (System.systemProject Gs) = .ok RETIRE_SUCCESS t := by
    rw [hlink]; exact hexec
  have hinvPre : Step.StepInvariant (System.systemProject Gs) := by
    rw [hGp]
    exact hrel.inv.preludeState inc pc _
  have hframe := Step.execProgram_regFrame (Program.seq instrs) Gs
  rw [hghost] at hframe
  change Step.RegFrame Gs ghostPost at hframe
  have hinvPost := hinvPre.systemProject_regFrame hframe
  obtain ⟨next, hnextGhost⟩ := (hinvPost.present Register.nextPC).exists_value
  obtain ⟨hn, hcount, hcountInc⟩ :=
    (blockHelper% projected_reads) b.pre b.post ghostPost m inc hpost
  have hnextPost : b.post.sail.regs.get? Register.nextPC = some next := hn.symm.trans hnextGhost
  have hinvT : Step.StepInvariant t :=
    hinvPost.of_agree (fun r _ => by rw [htregs]) (fun r => by
      obtain ⟨v, hv⟩ := (hinvPost.present r).exists_value
      exact ⟨v, by rw [htregs]; exact hv⟩)
  let s' := (blockHelper% finishState) t next m inc
  have hfinish := (blockHelper% finish_run) t hinvT encoding.bits next m inc
    (by rw [htregs]; exact hnextGhost) (by rw [htregs]; exact hcount)
    (by rw [htregs]; exact hcountInc)
  have hfs : ∀ (s : SailState) (pc m : BitVec 64) (inc : Bool),
      (blockHelper% finishState) s pc m inc =
        if inc then Step.setReg (Step.setReg s .PC pc) .minstret (BitVec.addInt m 1)
        else Step.setReg s .PC pc := fun _ _ _ _ => rfl
  have hft : s'.regs = ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs := by
    cases inc <;> simp [s', hfs, Step.setReg, htregs]
  have hpcS : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have htry := (blockHelper% encoding_try_step) encoding s hrel.inv inc hinc pc hpcS cast
    hfetch hdecode
  have hstep : try_step 0 false s = .ok false s' := by
    rw [htry]
    simp only [← hwidth]
    rw [← hGp, executeAndFinish_congr cast ast _ _ hinvPre hbridge]
    unfold Step.executeAndFinish Step.executeFull
    simp only [bind, EStateM.bind, hexec', RETIRE_SUCCESS, pure, EStateM.pure]
    exact hfinish
  refine ⟨false, s', hstep, ?_⟩
  have hmem' : s'.mem = t.mem := (blockHelper% finish_mem) t next m inc
  have hdev : ghostPost.jolt_device = b.post.jolt_device := hpost.device
  have hmemT : MemoryReady b.post.jolt_device s' := by
    rw [← hdev]
    exact htmem.of_mem_eq hmem'
  have hhtifT : (System.systemProject ghostPost).regs.get? Register.htif_tohost_base =
      some none := by
    rw [Step.systemProject_get?_of_not_overlaid _ (by simp [Step.Overlaid]),
      hframe.keep Register.htif_tohost_base (by simp [Step.JoltWritable])]
    change (Step.preludeState s inc pc _).regs.get? Register.htif_tohost_base = some none
    simpa [Step.preludeState, Step.setReg, Std.ExtDHashMap.get?_insert] using hrel.htif
  exact
    { regs := ⟨next, (if inc then BitVec.addInt m 1 else m), inc, hnextPost,
        hft.trans ((blockHelper% finish_regs) b.pre b.post ghostPost m next inc hpost)⟩
      inv := hinvT.stepFinish_retire encoding.bits hfinish
      htif := by
        change ((blockHelper% finishState) t next m inc).regs.get? Register.htif_tohost_base =
          some none
        rw [show ((blockHelper% finishState) t next m inc).regs =
          ((blockHelper% finishState) (System.systemProject ghostPost) next m inc).regs from hft]
        cases inc <;> simpa [hfs, Step.setReg,
          Std.ExtDHashMap.get?_insert] using hhtifT
      ram := fun a => by
        rw [hmem']
        exact (htram a).trans (hpost.ram a)
      present := hmemT.present
      layout := hmemT.layout }

/-- A retiring ordinary load or store below RAM simulates one Sail step and preserves
`Related`, including shared bytes at every address.
The mapped-region guards follow from the retiring row run.
For example, SB in the output region changes its byte in both shared maps.
The `via` variant permits an equivalent compressed instruction after decoding. -/
theorem block_simulates_io (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hsys : SystemInv b.pre) (hio : i.IoAccess b.start)
    (ast : instruction) (hm : RiscvInstruction.Matches i ast)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok ast (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  refine block_simulates_io_via program b hruns i hrow hsys hio encoding hwidth
    ?_
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hinc, hf, hd⟩ := hinputs s hrel pc m oldInc hn hr
  exact ⟨inc, hinc, hf, ast, ast, hm, fun _ _ => rfl, hd⟩

end WholeRun
