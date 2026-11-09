import JoltConstraints.WholeRun.Io
import JoltConstraints.WholeRun.IoAmo
import JoltConstraints.WholeRun.RunInv
import JoltConstraints.WholeRun.Fetch
import JoltConstraints.WholeRun.Init
import JoltConstraints.memory_presence
import JoltBytecode.Decode.Compressed

/-!
# Fetch and decode of a block from the program image

A RISC-V block of the whole-run theorem needs Sail's `fetch` and decode at the block's PC to
give the instruction Jolt decoded. This file derives both from the program image.

* `ImageDecoded` (platform premise): each RISC-V row of the image is what Jolt's decoder makes
  of the bytes `memory_init` loads at its address.
* `CodeIntact`: Sail's memory still holds those bytes at every row. It holds at `sailInit`
  (`codeIntact_sailInit`); keeping it through the run is a run invariant.
* `NotReservedParcel`: the documented deviation for the parcel `0x6001`.
* `block_simulates_decoded`: every non-EBREAK RISC-V block, in RAM or in the I/O window, is one
  Sail `try_step` that keeps `Related`, with no premise on Sail's fetch or decode.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

-- Reuse the established implementation lemmas without changing their modules.
local macro "bundlesHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Bundles
    (`WholeRun ++ n.getId)))

namespace WholeRun

/-- The last byte `memory_init` writes at address `a`; later entries override earlier ones, as
`initialRam` folds them in order.
For example, `[(0x80000000, 1), (0x80000000, 2)]` gives 2 at `0x80000000`. -/
def lastByte : List (BitVec 64 × BitVec 8) → Nat → Option (BitVec 8)
  | [], _ => none
  | e :: t, a =>
    match lastByte t a with
    | some b => some b
    | none => if e.1.toNat = a then some e.2 else none

/-- The byte of the program image at address `a`: the byte Jolt loads there at initialization,
or none where the ELF has no byte. -/
def imageByte? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 8) :=
  lastByte program.memory_init a

/-- The 16-bit parcel of the image at `a`, low byte first.
For example, bytes `0x13` and `0x01` give `0x0113`. -/
def imageParcel? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 16) := do
  let lo ← imageByte? program a
  let hi ← imageByte? program (a + 1)
  pure (hi ++ lo)

/-- The 32-bit word of the image at `a`, low parcel first.
For example, parcels `0x0113` then `0x0000` give `0x00000113`. -/
def imageWord? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 32) := do
  let lo ← imageParcel? program a
  let hi ← imageParcel? program (a + 2)
  pure (hi ++ lo)

theorem lastByte_some {l : List (BitVec 64 × BitVec 8)} {a : Nat} {b : BitVec 8}
    (h : lastByte l a = some b) : ∃ e ∈ l, e.1.toNat = a := by
  induction l generalizing b with
  | nil => simp [lastByte] at h
  | cons e t ih =>
    simp only [lastByte] at h
    split at h
    · rename_i hb
      obtain ⟨e', he', h'⟩ := ih hb
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · split at h
      · rename_i heq
        exact ⟨e, List.mem_cons_self .., heq⟩
      · cases h

/-- Every image byte lies in `[RAM_START_ADDRESS, program_end)`. -/
theorem imageByte?_bounds (program : Rv64ProgramImage SourceInstruction) {a : Nat}
    {b : BitVec 8} (h : imageByte? program a = some b) :
    JoltISA.RAM_START_ADDRESS ≤ a ∧ a < program.program_end.toNat := by
  obtain ⟨e, he, heq⟩ := lastByte_some h
  have := program.memory_init_in_program e he
  omega

theorem imageParcel?_eq_some {program : Rv64ProgramImage SourceInstruction} {a : Nat}
    {h : BitVec 16} : imageParcel? program a = some h ↔
      ∃ lo hi, imageByte? program a = some lo ∧ imageByte? program (a + 1) = some hi ∧
        h = hi ++ lo := by
  cases h1 : imageByte? program a <;> cases h2 : imageByte? program (a + 1) <;>
    simp [imageParcel?, h1, h2, eq_comm]

theorem imageWord?_eq_some {program : Rv64ProgramImage SourceInstruction} {a : Nat}
    {w : BitVec 32} : imageWord? program a = some w ↔
      ∃ lo hi, imageParcel? program a = some lo ∧ imageParcel? program (a + 2) = some hi ∧
        w = hi ++ lo := by
  cases h1 : imageParcel? program a <;> cases h2 : imageParcel? program (a + 2) <;>
    simp [imageWord?, h1, h2, eq_comm]

/-- Folding `memory_init` into the zero array, as `initialRam` does: the byte at offset `o`
is the last image byte for `RAM_START_ADDRESS + o`, or the array's own byte if none. -/
theorem initialRam_fold_getElem? (l : List (BitVec 64 × BitVec 8)) (ram : Array (BitVec 8))
    (o : Nat) (ho : o < ram.size) :
    (l.foldl (fun ram (x : BitVec 64 × BitVec 8) =>
      if JoltISA.RAM_START_ADDRESS ≤ x.1.toNat then
        ram.setIfInBounds (x.1.toNat - JoltISA.RAM_START_ADDRESS) x.2 else ram) ram)[o]? =
      some ((lastByte l (JoltISA.RAM_START_ADDRESS + o)).getD ram[o]) := by
  induction l generalizing ram with
  | nil => simp [lastByte, ho]
  | cons e t ih =>
    rcases e with ⟨address, byte⟩
    rw [List.foldl_cons]
    dsimp only
    have hsz : (if JoltISA.RAM_START_ADDRESS ≤ address.toNat then
        ram.setIfInBounds (address.toNat - JoltISA.RAM_START_ADDRESS) byte else ram).size =
        ram.size := by
      split <;> simp
    rw [ih _ (by rw [hsz]; exact ho)]
    refine congrArg some ?_
    simp only [lastByte]
    cases hl : lastByte t (JoltISA.RAM_START_ADDRESS + o) with
    | some b => simp
    | none =>
      simp only [Option.getD_none]
      by_cases hr : JoltISA.RAM_START_ADDRESS ≤ address.toNat
      · simp only [hr, ite_true]
        by_cases hao : address.toNat - JoltISA.RAM_START_ADDRESS = o
        · have : address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
          simp [this, Array.getElem_setIfInBounds_self]
        · have : ¬ address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
          simp [this, Array.getElem_setIfInBounds_ne, hao, ho]
      · have : ¬ address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
        simp [hr, this]


theorem initial_state_ram {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    ∃ (device : JoltDevice) (tape : JoltAdviceTape),
      joltInstance.memory_layout = some device.memory_layout ∧
      jt = init_state joltInstance.program.entry_address
        (initialRam device.memory_layout joltInstance.program.memory_init) device tape := by
  unfold JoltInstance.initial_state at built
  cases layoutResult : joltInstance.memory_layout with
  | none =>
    simp only [layoutResult, bind, Option.bind] at built
    cases built
  | some layout =>
    simp only [layoutResult, bind, Option.bind] at built
    repeat' split at built
    all_goals first
      | (cases built
         exact ⟨{ inputs := joltInstance.inputs, trusted_advice := joltInstance.trusted_advice,
                    untrusted_advice := privateInputs.untrusted_advice, outputs := #[],
                    panic := false, memory_layout := layout },
                  { bytes := privateInputs.advice_tape, readPosition := 0 }, rfl, rfl⟩)
      | cases built

/-- Jolt's memory map after inserting the bytes of an array from index `n`: the byte at
`RAM_START_ADDRESS + o` is `l[o - n]` for `o` in range, else unchanged. -/
theorem zipIdx_fold_get? (l : List (BitVec 8)) (n o : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    ((l.zipIdx n).foldl
      (fun mem (x : BitVec 8 × Nat) => mem.insert (JoltISA.RAM_START_ADDRESS + x.2) x.1) mem).get?
        (JoltISA.RAM_START_ADDRESS + o) =
      if n ≤ o ∧ o < n + l.length then l[o - n]? else mem.get? (JoltISA.RAM_START_ADDRESS + o) := by
  induction l generalizing n mem with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    dsimp only
    rw [ih]
    by_cases h : n = o
    · subst h
      simp
    · simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      have : ¬ (JoltISA.RAM_START_ADDRESS + n == JoltISA.RAM_START_ADDRESS + o) = true := by
        simp only [beq_iff_eq]; omega
      simp only [this]
      simp only [List.length_cons]
      rcases Nat.lt_or_gt_of_ne h with hlt | hgt
      · obtain ⟨k, rfl⟩ : ∃ k, o = n + 1 + k := ⟨o - n - 1, by omega⟩
        by_cases hk : k < t.length
        · have h1 : n + 1 ≤ n + 1 + k ∧ n + 1 + k < n + 1 + t.length := by omega
          have h2 : n ≤ n + 1 + k ∧ n + 1 + k < n + (t.length + 1) := by omega
          simp only [h1, h2, and_self, ↓reduceIte]
          have : n + 1 + k - n = k + 1 := by omega
          have h3 : n + 1 + k - (n + 1) = k := by omega
          rw [this, h3]
          rfl
        · have h1 : ¬ (n + 1 ≤ n + 1 + k ∧ n + 1 + k < n + 1 + t.length) := by omega
          have h2 : ¬ (n ≤ n + 1 + k ∧ n + 1 + k < n + (t.length + 1)) := by omega
          rw [ite_eq_right h1, ite_eq_right h2]
          simp only [Bool.false_eq_true, ↓reduceIte]
      · have h1 : ¬ (n + 1 ≤ o ∧ o < n + 1 + t.length) := by omega
        have h2 : ¬ (n ≤ o ∧ o < n + (t.length + 1)) := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
        simp only [Bool.false_eq_true, ↓reduceIte]


/-- Jolt's initial RAM byte map holds the array's byte at each in-range offset. -/
theorem init_state_mem_get? (entry : BitVec 64) (ram : Array (BitVec 8)) (io : JoltDevice)
    (tape : JoltAdviceTape) (o : Nat) :
    (init_state entry ram io tape).sail.mem.get? (JoltISA.RAM_START_ADDRESS + o) = ram[o]? := by
  have h := zipIdx_fold_get? ram.toList 0 o {}
  rw [show (init_state entry ram io tape).sail.mem = (ram.toList.zipIdx.foldl
    (fun mem (x : BitVec 8 × Nat) => mem.insert (JoltISA.RAM_START_ADDRESS + x.2) x.1) {}) from rfl]
  by_cases ho : o < ram.size
  · simpa [ho] using h
  · have : ¬ (0 ≤ o ∧ o < 0 + ram.toList.length) := by simp; omega
    rw [ite_eq_right this] at h
    simpa [ho] using h

/-- **Every image byte is in Sail's initial memory.** At `sailInit` of Jolt's initial state,
Sail's memory holds each byte of the program image at its address. -/
theorem sailInit_get?_image (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) (a : Nat) (b : BitVec 8)
    (h : imageByte? joltInstance.program a = some b) :
    (sailInit jt).mem.get? a = some b := by
  obtain ⟨device, tape, hlayout, hjt⟩ := initial_state_ram joltInstance privateInputs jt built
  obtain ⟨hR, hend⟩ := imageByte?_bounds joltInstance.program h
  unfold JoltInstance.memory_layout at hlayout
  obtain ⟨hlow, hpw, hio, hram⟩ := layout_facts hlayout
  obtain ⟨psize, hpsize, hheap⟩ := new_heap_end_ge _ _ hlayout
  have hpsize' : psize = joltInstance.program.program_size := by
    simpa using hpsize.symm
  subst hpsize'
  have hend_le := joltInstance.program.program_end.isLt
  have hpsize_nat : joltInstance.program.program_size.toNat =
      joltInstance.program.program_end.toNat - JoltISA.RAM_START_ADDRESS := by
    have hR64 : (BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS).toNat = JoltISA.RAM_START_ADDRESS := by
      simp [JoltISA.RAM_START_ADDRESS]
    unfold Rv64ProgramImage.program_size
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, hR64]; exact joltInstance.program.program_end_ge_ram_start), hR64]
  have hbacking := heap_end_le_ram_backing_end device
  unfold JoltISA.Mmu.ram_backing_end at hbacking
  have hsize := initialRam_size device.memory_layout joltInstance.program.memory_init
  have hmem : (sailInit jt).mem = sailInitMem jt := rfl
  have hdev : jt.jolt_device.memory_layout = device.memory_layout := by subst hjt; rfl
  rw [hmem, sailInitMem_get?]
  have hin : memLow jt.jolt_device ≤ a ∧ a < memHigh jt.jolt_device := by
    unfold memLow memHigh
    rw [hdev]
    simp only [JoltISA.STACK_CANARY_SIZE] at hheap
    omega
  rw [ite_eq_left hin]
  have hflag : IsFlagWord jt.jolt_device a = false := by
    unfold IsFlagWord
    rw [hdev]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega
  rw [hflag]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sailByte
  rw [ite_eq_left hR]
  unfold JoltISA.Mmu.ram_byte
  have ho : a - JoltISA.RAM_START_ADDRESS < (initialRam device.memory_layout
      joltInstance.program.memory_init).size := by
    rw [hsize]
    omega
  have hget : jt.sail.mem.get? a = some b := by
    have := init_state_mem_get? joltInstance.program.entry_address
      (initialRam device.memory_layout joltInstance.program.memory_init) device tape
      (a - JoltISA.RAM_START_ADDRESS)
    rw [← hjt, Nat.add_sub_cancel' hR] at this
    rw [this]
    have ho' : a - JoltISA.RAM_START_ADDRESS < (Array.replicate
        (8 * ((device.memory_layout.get_total_memory_size.toNat + 7) / 8)) (0 : BitVec 8)).size := by
      rw [Array.size_replicate]
      rw [hsize] at ho
      exact ho
    have key := initialRam_fold_getElem? joltInstance.program.memory_init
      (Array.replicate (8 * ((device.memory_layout.get_total_memory_size.toNat + 7) / 8)) 0)
      (a - JoltISA.RAM_START_ADDRESS) ho'
    unfold initialRam
    rw [Nat.add_sub_cancel' hR] at key
    have h' : lastByte joltInstance.program.memory_init a = some b := h
    refine key.trans ?_
    rw [h']
    rfl
  rw [hget]
  rfl


/-! ## The program image and the code in memory -/

/-- The image's bytes for one RISC-V row, and what Jolt's decoder makes of them.
For example, the compressed NOP row at `0x80000000` with parcel `0x0001` decodes through
`joltUncompress` to ADDI x0,x0,0, and `RowDecodes … (.compressed 0x0001)` records exactly that;
a base row records the four-byte word and `joltDecode` of it. -/
def RowDecodes (program : Rv64ProgramImage SourceInstruction)
    (row : SourceInstructionRow SourceInstruction) (i : RiscvInstruction) :
    BlockEncoding → Prop
  | .base w => row.is_compressed = false ∧
      imageWord? program row.address.toNat = some w ∧ w.extractLsb 1 0 = 0b11#2 ∧
      ∃ advice, Decode.joltDecode w advice = some i
  | .compressed h => row.is_compressed = true ∧
      imageParcel? program row.address.toNat = some h ∧ h.extractLsb 1 0 ≠ 0b11#2 ∧
      ∃ advice, Decode.joltDecode (Decode.joltUncompress h) advice = some i

/-- **Platform premise: the committed bytecode is what Jolt's decoder makes of the image.**
Every RISC-V row of the program image is what Jolt's decoder (`joltDecode`, and
`joltUncompress` for a compressed row) gives for the bytes the image loads at its address.
Its `is_compressed` flag agrees with the low two bits of the first parcel, and the advice
operand of the decoder, which the encoding does not carry, is whatever Jolt used.

The bytes are those of `memory_init`, the initial memory (`initialRam`), where a later entry
overrides an earlier one at the same address (`imageByte?`). This is a premise on the
off-chain decoder that produced the bytecode, not something the proof system checks. -/
def ImageDecoded (program : Rv64ProgramImage SourceInstruction) : Prop :=
  ∀ row ∈ program.instructions, ∀ i : RiscvInstruction, row.instruction = .riscv i →
    ∃ e : BlockEncoding, RowDecodes program row i e

/-- **The code in memory is still the image.** Sail's memory `s` holds, at every byte of every
row of the program, the byte the image loads there.
For example, in Sail's initial state the four bytes of an ADDI row at `0x80000000` are the
image's four bytes. A store into the code, or a write that changes a row's bytes, falsifies it;
the run must keep it (it is a run invariant, not proved by this file). -/
def CodeIntact (program : Rv64ProgramImage SourceInstruction) (s : SailState) : Prop :=
  ∀ row ∈ program.instructions, ∀ k, k < (if row.is_compressed then 2 else 4) →
    ∀ b, imageByte? program (row.address.toNat + k) = some b →
      s.mem.get? (row.address.toNat + k) = some b

/-- **Documented deviation: the block's parcel is not `0x6001`.** Jolt accepts the reserved
compressed parcel `0x6001` (C.LUI x0, 0) and runs it as a no-op, while Sail rejects it as
illegal, so a block at such a parcel is not simulated. See `docs/riscv-alignment.md`,
section 5 ("What step e proves"). This premise is discharged once the Jolt pin includes
a16z/jolt#2381, which makes Jolt reject `0x6001`. -/
def NotReservedParcel (program : Rv64ProgramImage SourceInstruction) (b : Block) : Prop :=
  imageParcel? program b.row.address.toNat ≠ some 0x6001#16

/-- **The code starts intact.** At `sailInit` of Jolt's initial state, Sail's memory holds
every byte the image loads, so `CodeIntact` holds for the start of a run. -/
theorem codeIntact_sailInit (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    CodeIntact joltInstance.program (sailInit jt) :=
  fun _ _ _ _ b hb => sailInit_get?_image joltInstance privateInputs jt built _ b hb

/-! ## Decoded offsets and ECALL -/

theorem getLsbD_append_zero {n : Nat} (x : BitVec n) : (x ++ 0#1).getLsbD 0 = false := by
  simp only [BitVec.getLsbD_append]
  simp

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- Every instruction Jolt decodes has even branch and jump offsets. -/
theorem joltDecode_evenOffsets (w : BitVec 32) (advice : BitVec 64) (i : RiscvInstruction)
    (h : Decode.joltDecode w advice = some i) : i.EvenOffsets := by
  unfold Decode.joltDecode at h
  repeat' split at h
  all_goals first
    | (cases h; simp [RiscvInstruction.EvenOffsets]; done)
    | (cases h; simp only [RiscvInstruction.EvenOffsets, Decode.immJ, Decode.immB]
       exact getLsbD_append_zero _)
    | (exfalso; simp at h; done)
    | (cases hc : Decode.csr w <;> simp only [hc, Option.map] at h <;> cases h <;>
        simp [RiscvInstruction.EvenOffsets])

/-- Jolt decodes ECALL only from the word `0x73`. -/
theorem joltDecode_ecall_eq (w : BitVec 32) (advice : BitVec 64)
    (h : Decode.joltDecode w advice = some .ECALL) : w = 0x73#32 := by
  unfold Decode.joltDecode at h
  repeat' split at h
  all_goals first
    | assumption
    | (exfalso; simp at h)


private theorem getLsbD_ite' {c : Prop} [Decidable c] (a b : BitVec 32) (i : Nat) :
    (if c then a else b).getLsbD i = if c then a.getLsbD i else b.getLsbD i := by
  split <;> rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- Jolt's compressed expansion is never the ECALL word, so no compressed row is ECALL. -/
theorem joltUncompress_ne_ecall (h : BitVec 16) : Decode.joltUncompress h ≠ 0x73#32 := by
  intro heq
  unfold Decode.joltUncompress at heq
  dsimp only at heq
  repeat' split at heq
  all_goals
    have h6 := congrArg (fun x => x.getLsbD 6) heq
    have h4 := congrArg (fun x => x.getLsbD 4) heq
    have h2 := congrArg (fun x => x.getLsbD 2) heq
    have h20 := congrArg (fun x => x.getLsbD 20) heq
    clear heq
    first
    | (simp (config := {decide := true}) only [Decode.signBitMask, getLsbD_ite', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ofNat, Nat.reduceLT, Nat.reduceSub, Nat.reduceShiftLeft, Bool.and_false,
        Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.not_true,
        Bool.not_false, Nat.testBit, Nat.reduceAnd, Nat.reduceShiftRight, Nat.reduceMod,
        Nat.one_and_eq_mod_two, Nat.reduceBEq, decide_true, decide_false, ite_self, ite_true, ite_false] at h6; done)
    | (simp (config := {decide := true}) only [Decode.signBitMask, getLsbD_ite', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ofNat, Nat.reduceLT, Nat.reduceSub, Nat.reduceShiftLeft, Bool.and_false,
        Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.not_true,
        Bool.not_false, Nat.testBit, Nat.reduceAnd, Nat.reduceShiftRight, Nat.reduceMod,
        Nat.one_and_eq_mod_two, Nat.reduceBEq, decide_true, decide_false, ite_self, ite_true, ite_false] at h4; done)
    | (simp (config := {decide := true}) only [Decode.signBitMask, getLsbD_ite', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ofNat, Nat.reduceLT, Nat.reduceSub, Nat.reduceShiftLeft, Bool.and_false,
        Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.not_true,
        Bool.not_false, Nat.testBit, Nat.reduceAnd, Nat.reduceShiftRight, Nat.reduceMod,
        Nat.one_and_eq_mod_two, Nat.reduceBEq, decide_true, decide_false, ite_self, ite_true, ite_false] at h2; done)
    | (simp (config := {decide := true}) only [Decode.signBitMask, getLsbD_ite', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ofNat, Nat.reduceLT, Nat.reduceSub, Nat.reduceShiftLeft, Bool.and_false,
        Bool.false_and, Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or, Bool.not_true,
        Bool.not_false, Nat.testBit, Nat.reduceAnd, Nat.reduceShiftRight, Nat.reduceMod,
        Nat.one_and_eq_mod_two, Nat.reduceBEq, decide_true, decide_false, ite_self, ite_true, ite_false] at h20; done)
    | skip
  all_goals
    simp (config := {decide := true}) [Decode.signBitMask, getLsbD_ite', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft] at h6
  all_goals (split at h6 <;> simp at h6)

/-- An ECALL row of a decoded image is a four-byte row. -/
theorem rowDecodes_ecall {program : Rv64ProgramImage SourceInstruction}
    {row : SourceInstructionRow SourceInstruction} {e : BlockEncoding}
    (hd : RowDecodes program row .ECALL e) : ∃ w, e = .base w := by
  cases e with
  | base w => exact ⟨w, rfl⟩
  | compressed h =>
    obtain ⟨_, _, _, adv, hdec⟩ := hd
    exact absurd (joltDecode_ecall_eq _ adv hdec) (joltUncompress_ne_ecall h)

theorem exists_should_inc (s : SailState) (hinv : Step.StepInvariant s) :
    ∃ inc : Bool, should_inc_minstret .Machine s = .ok inc s := by
  obtain ⟨a, ha⟩ := Step.readReg_present Register.mcountinhibit s (hinv.present _)
  obtain ⟨c, hc⟩ := Step.readReg_present Register.minstretcfg s (hinv.present _)
  unfold should_inc_minstret
  simp only [andM, bind, EStateM.bind, pure, EStateM.pure, ha]
  cases toBool (_get_Counterin_IR a == 0#1)
  · exact ⟨_, rfl⟩
  · simp only [EStateM.bind, hc, EStateM.pure]
    exact ⟨_, rfl⟩


/-! ## Fetch and decode of one row from the code in memory -/

theorem memParcel_eq_of_bytes (t : SailState) (a : Nat) (lo hi : BitVec 8)
    (h0 : t.mem.get? a = some lo) (h1 : t.mem.get? (a + 1) = some hi) :
    memParcel t a = hi ++ lo := by
  simp only [memParcel, memByte, h0, h1, Option.getD_some]

theorem extractLsb_append_low (hi lo : BitVec 16) :
    (hi ++ lo : BitVec 32).extractLsb 1 0 = lo.extractLsb 1 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_append]
  by_cases h : i ≤ 1
  · simp [h, show i < 16 by omega]
  · simp [h]


/-- **Sail fetches and decodes a decoded row from the code in memory.** For a row of a decoded
image whose bytes are intact in `t`, Sail's `fetch` at the row's PC returns its encoding, and
Sail's decoder returns an AST `cast` that executes like an AST `ast` matching Jolt's
instruction. For a base word `cast = ast`; for a compressed parcel, `cast` is the compressed
AST and the bridge is the decoder's expansion agreement. -/
theorem rowDecodes_fetch_decode (program : Rv64ProgramImage SourceInstruction)
    (row : SourceInstructionRow SourceInstruction) (hrowmem : row ∈ program.instructions)
    (i : RiscvInstruction) (e : BlockEncoding) (hd : RowDecodes program row i e)
    (hnot : imageParcel? program row.address.toNat ≠ some 0x6001#16)
    (t : SailState) (hinv : Step.StepInvariant t)
    (hmisa : t.regs.get? Register.misa = some Decode.resetMisa)
    (hpc : t.regs.get? Register.PC = some row.address) (heven : row.address.getLsbD 0 = false)
    (hpma : t.regs.get? Register.pma_regions = some platformPma)
    (hhtif : t.regs.get? Register.htif_tohost_base = some none)
    (hcode : CodeIntact program t) :
    fetch () t = .ok e.fetched t ∧ ∃ ast cast : instruction,
      RiscvInstruction.Matches i ast ∧
      (∀ u, Step.StepInvariant u → Step.executeFull cast u = Step.executeFull ast u) ∧
      e.decode t = .ok cast t ∧ (∀ w, e = .base w → cast = ast) := by
  have hw64 := row.address.isLt
  have hpe := program.program_end.isLt
  cases e with
  | base w =>
    obtain ⟨hc, hw, hlow, adv, hdec⟩ := hd
    obtain ⟨lo, hi, hlo, hhi, rfl⟩ := imageWord?_eq_some.mp hw
    obtain ⟨b0, b1, hb0, hb1, rfl⟩ := imageParcel?_eq_some.mp hlo
    obtain ⟨b2, b3, hb2, hb3, rfl⟩ := imageParcel?_eq_some.mp hhi
    have hk : ∀ k, k < 4 → ∀ b, imageByte? program (row.address.toNat + k) = some b →
        t.mem.get? (row.address.toNat + k) = some b := fun k hk b hb =>
      hcode row hrowmem k (by simp [hc, hk]) b hb
    have m0 := hk 0 (by omega) b0 hb0
    have m1 := hk 1 (by omega) b1 hb1
    have m2 := hk 2 (by omega) b2 hb2
    have m3 := hk 3 (by omega) b3 hb3
    obtain ⟨hR, hend⟩ := imageByte?_bounds program hb0
    obtain ⟨_, hend3⟩ := imageByte?_bounds program hb3
    have hhi2 : (row.address + 2#64).toNat = row.address.toNat + 2 := by
      apply BitVec.toNat_add_of_lt
      change row.address.toNat + 2 < 2 ^ 64
      omega
    have hlowp : (b1 ++ b0 : BitVec 16).extractLsb 1 0 = 0b11#2 := by
      have := hlow
      rwa [extractLsb_append_low] at this
    have hp0 := memParcel_eq_of_bytes t row.address.toNat b0 b1 m0 m1
    have hp2 := memParcel_eq_of_bytes t (row.address.toNat + 2) b2 b3 m2 m3
    have hfetch := fetch_regions t hinv row.address hpc heven platformPma ramRegion hpma rfl rfl
      hR (by omega)
      ((bundlesHelper% matching_platform_ram) row.address 2 hR (by omega) (by omega) (by omega))
      hhtif (by
        intro j hj
        interval_cases j
        · exact ⟨b0, by simpa using m0⟩
        · exact ⟨b1, m1⟩)
      (by
        intro _
        refine ⟨?_, by omega, ?_⟩
        · exact (bundlesHelper% matching_platform_ram) (row.address + 2#64) 2
            (by rw [hhi2]; omega) (by omega) (by omega) (by rw [hhi2]; omega)
        · intro j hj
          interval_cases j
          · exact ⟨b2, by simpa using m2⟩
          · exact ⟨b3, by simpa using m3⟩)
    refine ⟨?_, ?_⟩
    · rw [hfetch]
      simp only [fetchedAt, hp0, hlowp, hp2, ↓reduceIte, BlockEncoding.fetched]
    · obtain ⟨ast, hast, hm⟩ := Decode.joltDecode_agrees _ adv i hdec t hinv hmisa
      exact ⟨ast, ast, hm, fun _ _ => rfl, hast, fun _ _ => rfl⟩
  | compressed h =>
    obtain ⟨hc, hp, hlow, adv, hdec⟩ := hd
    obtain ⟨b0, b1, hb0, hb1, rfl⟩ := imageParcel?_eq_some.mp hp
    have hk : ∀ k, k < 2 → ∀ b, imageByte? program (row.address.toNat + k) = some b →
        t.mem.get? (row.address.toNat + k) = some b := fun k hk b hb =>
      hcode row hrowmem k (by simp [hc, hk]) b hb
    have m0 := hk 0 (by omega) b0 hb0
    have m1 := hk 1 (by omega) b1 hb1
    obtain ⟨hR, hend⟩ := imageByte?_bounds program hb0
    obtain ⟨_, hend1⟩ := imageByte?_bounds program hb1
    have hp0 := memParcel_eq_of_bytes t row.address.toNat b0 b1 m0 m1
    have hfetch := fetch_regions t hinv row.address hpc heven platformPma ramRegion hpma rfl rfl
      hR (by omega)
      ((bundlesHelper% matching_platform_ram) row.address 2 hR (by omega) (by omega) (by omega))
      hhtif (by
        intro j hj
        interval_cases j
        · exact ⟨b0, by simpa using m0⟩
        · exact ⟨b1, m1⟩)
      (by
        intro hbits
        rw [hp0] at hbits
        exact absurd hbits hlow)
    have hres : ¬ Decode.ReservedAccepted (b1 ++ b0) := by
      rw [Decode.reservedAccepted_iff]
      intro heq
      exact hnot (hp.trans (congrArg some heq))
    refine ⟨?_, ?_⟩
    · rw [hfetch]
      simp only [fetchedAt, hp0, hlow, ↓reduceIte, BlockEncoding.fetched]
    · obtain ⟨cast, base, hcast, hm, hbridge⟩ :=
        Decode.joltDecode_compressed_agrees _ hlow hres adv i hdec t hinv hmisa
      exact ⟨base, cast, hm, hbridge, hcast, fun w hw => by cases hw⟩


/-- The row of a block is one of the program's rows. -/
theorem Block.Runs.row_mem {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (h : b.Runs program) : b.row ∈ program.instructions := by
  have := h.at_row
  unfold rowAt at this
  exact Array.mem_of_find?_eq_some this

/-- **The decode inputs of a block, state by state.** On every Sail state related to the
block's entry state, with the code intact and `misa` at its reset value, Sail's fetch and decode
of the block's row give the encoding `e` and an AST `cast` that executes like an AST matching
the block's instruction. This is the `hinputs` of `block_simulates_via` for non-ECALL rows. -/
theorem decoded_inputs (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (e : BlockEncoding)
    (hd : RowDecodes program b.row i e) (hnot : NotReservedParcel program b)
    (hpc : b.row.address.getLsbD 0 = false)
    (hmisa : ∀ s, Related b.pre s → s.regs.get? Register.misa = some Decode.resetMisa)
    (hcode : ∀ s, Related b.pre s → CodeIntact program s) :
    ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool, should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok e.fetched (Step.setReg s .minstret_increment inc) ∧
        ∃ (ast cast : instruction), RiscvInstruction.Matches i ast ∧
        (∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) ∧
        e.decode (Step.setReg s .minstret_increment inc) =
          .ok cast (Step.setReg s .minstret_increment inc) ∧
        (∀ w, e = .base w → cast = ast) := by
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hinc⟩ := exists_should_inc s hrel.inv
  have hp : pc = b.row.address := Option.some.inj (hn.symm.trans hruns.continues)
  have hpc_s : s.regs.get? Register.PC = some pc := by
    simp [hr, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have hpma_s : s.regs.get? Register.pma_regions = some platformPma := by
    simp [hr, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  refine ⟨inc, hinc, ?_⟩
  have := rowDecodes_fetch_decode program b.row hruns.row_mem i e hd hnot
    (Step.setReg s .minstret_increment inc)
    (hrel.inv.setReg _ _ (by simp [Step.invariantReg]))
    (by rw [Step.setReg_get?_ne _ _ (by decide)]; exact hmisa s hrel)
    (by rw [Step.setReg_get?_ne _ _ (by decide), hpc_s, hp])
    hpc
    (by rw [Step.setReg_get?_ne _ _ (by decide)]; exact hpma_s)
    (by rw [Step.setReg_get?_ne _ _ (by decide)]; exact hrel.htif)
    (hcode s hrel)
  obtain ⟨hf, ast, cast, hm, hb, hdc, hw⟩ := this
  exact ⟨hf, ast, cast, hm, hb, hdc, hw⟩


/-- The decoded instruction of a row has even offsets. -/
theorem rowDecodes_evenOffsets {program : Rv64ProgramImage SourceInstruction}
    {row : SourceInstructionRow SourceInstruction} {i : RiscvInstruction} {e : BlockEncoding}
    (hd : RowDecodes program row i e) : i.EvenOffsets := by
  cases e with
  | base w =>
    obtain ⟨_, _, _, adv, hdec⟩ := hd
    exact joltDecode_evenOffsets _ adv i hdec
  | compressed h =>
    obtain ⟨_, _, _, adv, hdec⟩ := hd
    exact joltDecode_evenOffsets _ adv i hdec

/-- **Every non-EBREAK RISC-V block of a decoded program simulates.** The block's instruction
`i` is a RISC-V row of the image, run as one Sail `try_step` that keeps the whole-run relation:
`block_simulates` for a block whose access, if any, is in RAM and `block_simulates_io` for a
block whose access is in the I/O window. Sail's fetch and decode come from the program image
and the bytes still in memory, not from a premise on them: the instruction word, its width, the
matching Sail AST (for a compressed parcel, the compressed AST that executes like it), and the
even branch and jump offsets all follow from `ImageDecoded` and `CodeIntact`.

Premises, by class:
* invariant (the run keeps these; the whole-run theorem proves them): `hsys`, the system
  invariant on the block's entry state; `hpc`, the row's address is even; `hmisa`, Sail's `misa`
  is `Decode.resetMisa` on every state related to the entry state; `hcode`, the code is intact
  on every such state (`CodeIntact`, which holds at `sailInit` by `codeIntact_sailInit`).
* platform: `himage`, the committed bytecode is what Jolt's decoder makes of the image
  (`ImageDecoded`); `hheap`, the heap ends eight bytes below `2^64`; `hclass`, the block's
  memory access is in RAM or in the I/O window.
* from decoding: none; `encoding`, width, offsets, instruction matching, fetch and decode are
  derived.
* documented deviation (`docs/riscv-alignment.md`, section 5, "What step e proves"): `hnot`
  (`NotReservedParcel`), the parcel is not `0x6001`; and, for an I/O block, `hflag`
  (`NoFlagWordLoad`), `hlow` (`NoLowLoad`) and `hpanic` (`PanicStoreNonzero`).

For example, a block whose row is the compressed C.ADDI parcel `0x0505` at an even address in
RAM simulates, with Sail decoding the parcel to `C_ADDI` and Jolt running ADDI. -/
theorem block_simulates_decoded (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (himage : ImageDecoded program)
    (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i) (hbreak : i ≠ .EBREAK)
    (hsys : SystemInv b.pre) (hpc : b.row.address.getLsbD 0 = false)
    (hmisa : ∀ s, Related b.pre s → s.regs.get? Register.misa = some Decode.resetMisa)
    (hcode : ∀ s, Related b.pre s → CodeIntact program s)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hnot : NotReservedParcel program b)
    (hclass : RamAccess i b.start ∨ i.IoAccess b.start)
    (hflag : i.IoAccess b.start → i.NoFlagWordLoad b.start)
    (hlow : i.IoAccess b.start → i.NoLowLoad b.start)
    (hpanic : i.IoAccess b.start → i.PanicStoreNonzero b.start) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  obtain ⟨e, hd⟩ := himage b.row hruns.row_mem i hrow
  have hwidth : b.row.is_compressed = e.isCompressed := by
    cases e with
    | base w => exact hd.1
    | compressed h => exact hd.1
  have hin := decoded_inputs program b hruns i e hd hnot hpc hmisa hcode
  rcases hclass with hram | hio
  · refine block_simulates_via program b hruns i hrow hbreak hsys hpc
      (rowDecodes_evenOffsets hd) hheap hram e hwidth ?_
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hinc, hf, ast, cast, hm, hb, hdc, hw⟩ := hin s hrel pc m oldInc hn hr
    refine ⟨inc, hinc, ?_⟩
    by_cases hecall : i = .ECALL
    · subst hecall
      rw [ite_eq_left rfl]
      obtain ⟨w, rfl⟩ := rowDecodes_ecall hd
      have hast : ast = .ECALL () := hm
      have hcast := hw w rfl
      subst hcast
      subst hast
      exact ⟨w, hf, hdc⟩
    · rw [ite_eq_right hecall]
      exact ⟨hf, ast, cast, hm, hb, hdc⟩
  · refine block_simulates_io_via program b hruns i hrow hsys hio (hflag hio) (hlow hio)
      (hpanic hio) e hwidth ?_
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hinc, hf, ast, cast, hm, hb, hdc, _⟩ := hin s hrel pc m oldInc hn hr
    exact ⟨inc, hinc, hf, ast, cast, hm, hb, hdc⟩

/-- **Every non-EBREAK RISC-V block of a decoded program simulates, atomics on the I/O window
included.** This is `block_simulates_decoded` with two premises discharged. Its `hmisa` is
`Related.misa`: the whole-run relation sets Sail's `misa` to `Decode.resetMisa`. Its `hclass` is
derived: `access_classified` shows the block accesses RAM, accesses the I/O window with a load or
store, or is an atomic on the I/O window; an atomic on the I/O window takes the deviation premise
`hamoflag` (`AmoNoFlagWord`).

Premises, by class:
* invariant: `hsys`, the system invariant on the block's entry state.
* platform: `hpc` (`RowsAligned`), `hheap` (`HeapNoWrap`), `hcode` (the image is intact in
  Sail's memory) and `himage` (the image decodes).
* documented deviation (`docs/riscv-alignment.md`, section 2): `hnot` (`NotReservedParcel`);
  for a load or store on the I/O window, `hflag` (`NoFlagWordLoad`), `hlow` (`NoLowLoad`) and
  `hpanic` (`PanicStoreNonzero`); for an atomic on the I/O window, `hamoflag`
  (`AmoNoFlagWord`).

For example, a block whose row is `AMOADD.D` through a register holding `0x40000010`
simulates, when no byte of the doubleword at `0x40000010` is a panic or termination byte. -/
theorem block_simulates_image (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (himage : ImageDecoded program)
    (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i) (hbreak : i ≠ .EBREAK)
    (hsys : SystemInv b.pre) (hpc : b.row.address.getLsbD 0 = false)
    (hcode : ∀ s, Related b.pre s → CodeIntact program s)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hnot : NotReservedParcel program b)
    (hflag : i.IoAccess b.start → i.NoFlagWordLoad b.start)
    (hlow : i.IoAccess b.start → i.NoLowLoad b.start)
    (hpanic : i.IoAccess b.start → i.PanicStoreNonzero b.start)
    (hamoflag : IoAmoAccess i b.start → i.AmoNoFlagWord b.start) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  rcases access_classified program b hruns i hrow with hram | hio | hamo
  · exact block_simulates_decoded program b hruns himage i hrow hbreak hsys hpc
      (fun _ hrel => hrel.misa) hcode hheap hnot (Or.inl hram) hflag hlow hpanic
  · exact block_simulates_decoded program b hruns himage i hrow hbreak hsys hpc
      (fun _ hrel => hrel.misa) hcode hheap hnot (Or.inr hio) hflag hlow hpanic
  · obtain ⟨e, hd⟩ := himage b.row hruns.row_mem i hrow
    have hwidth : b.row.is_compressed = e.isCompressed := by
      cases e with
      | base w => exact hd.1
      | compressed h => exact hd.1
    have hin := decoded_inputs program b hruns i e hd hnot hpc (fun s hrel => hrel.misa) hcode
    refine block_simulates_io_amo_via program b hruns i hrow hsys hamo (hamoflag hamo) e hwidth ?_
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hinc, hf, ast, cast, hm, hb, hdc, _⟩ := hin s hrel pc m oldInc hn hr
    exact ⟨inc, hinc, hf, ast, cast, hm, hb, hdc⟩

end WholeRun
