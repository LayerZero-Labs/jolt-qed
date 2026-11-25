import JoltConstraints.theorems.WholeRun.ImageMemory
import JoltConstraints.theorems.WholeRun.RunInv
import JoltConstraints.theorems.WholeRun.Fetch
import JoltBytecode.Decode.Compressed

/-!
# Fetch and decode of a block from the program image

A RISC-V block of the whole-run theorem needs Sail's `fetch` and decode at the block's PC to
give the instruction Jolt decoded. This file derives both from the program image.

* `ImageDecoded`: each RISC-V row of the image is what Jolt's decoder makes of the bytes
  `memory_init` loads at its address. `Rv64ProgramImage.DecodedFrom.imageDecoded`
  (`WholeRun/Elf.lean`) proves it for every program built from the ELF's sections.
* `CodeIntact`: Sail's memory still holds those bytes at every row. It holds at `sailInit`
  (`codeIntact_sailInit`); keeping it through the run is a run invariant.
* `block_simulates_decoded`: every non-EBREAK RISC-V block, in RAM or in the I/O window, is one
  Sail `try_step` that keeps `Related`, with no premise on Sail's fetch or decode.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltConstraints

set_option autoImplicit false

noncomputable section

-- Reuse the established implementation lemmas without changing their modules.
local macro "bundlesHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.theorems.WholeRun.Bundles
    (`WholeRun ++ n.getId)))

namespace WholeRun

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

/-- **The committed bytecode is what Jolt's decoder makes of the image.**
Every RISC-V row of the program image is what Jolt's decoder (`joltDecode`, and
`joltUncompress` for a compressed row) gives for the bytes the image loads at its address.
Its `is_compressed` flag agrees with the low two bits of the first parcel, and the advice
operand of the decoder, which the encoding does not carry, is whatever Jolt used.

The bytes are those of `memory_init`, the initial memory (`initialRam`), where a later entry
overrides an earlier one at the same address (`imageByte?`). No constraint checks this: it
describes how the bytecode was produced. The whole-run theorems take instead the premise
`Rv64ProgramImage.DecodedFrom` (the program agrees with what Jolt's `decode_elf` builds from
the ELF's sections), and `DecodedFrom.imageDecoded` (`WholeRun/Elf.lean`) derives this property
from it.
For example, take an image with the single row ADDI x1,x0,1 at `0x80000000`, not compressed,
whose `memory_init` holds the bytes `0x93 0x00 0x10 0x00` at `0x80000000` to `0x80000003`.
The image satisfies `ImageDecoded` with the encoding `.base 0x00100093`: the word's low two bits
are `0b11`, and `joltDecode 0x00100093` gives ADDI x1,x0,1. -/
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
    refine ⟨?_, ?_⟩
    · rw [hfetch]
      simp only [fetchedAt, hp0, hlow, ↓reduceIte, BlockEncoding.fetched]
    · obtain ⟨cast, base, hcast, hm, hbridge⟩ :=
        Decode.joltDecode_compressed_agrees _ hlow adv i hdec t hinv hmisa
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
    (hd : RowDecodes program b.row i e)
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
  have := rowDecodes_fetch_decode program b.row hruns.row_mem i e hd
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

/-- A decoded non-EBREAK block classified as an ordinary RAM or below-RAM access
simulates one Sail step and preserves the shared-memory relation.
For example, a compressed ADDI parcel executes its equivalent base instruction. -/
theorem block_simulates_decoded (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (himage : ImageDecoded program)
    (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i) (hbreak : i ≠ .EBREAK)
    (hsys : SystemInv b.pre) (hpc : b.row.address.getLsbD 0 = false)
    (hmisa : ∀ s, Related b.pre s → s.regs.get? Register.misa = some Decode.resetMisa)
    (hcode : ∀ s, Related b.pre s → CodeIntact program s)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hclass : RamAccess i b.start ∨ i.IoAccess b.start) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  obtain ⟨e, hd⟩ := himage b.row hruns.row_mem i hrow
  have hwidth : b.row.is_compressed = e.isCompressed := by
    cases e with
    | base w => exact hd.1
    | compressed h => exact hd.1
  have hin := decoded_inputs program b hruns i e hd hpc hmisa hcode
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
  · refine block_simulates_io_via program b hruns i hrow hsys hio e hwidth ?_
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hinc, hf, ast, cast, hm, hb, hdc, _⟩ := hin s hrel pc m oldInc hn hr
    exact ⟨inc, hinc, hf, ast, cast, hm, hb, hdc⟩

/-- Every decoded non-EBREAK RISC-V block simulates one Sail step, including below-RAM
word and doubleword atomics.
For example, AMOADD.D in the output region stores the same shared bytes in both models. -/
theorem block_simulates_image (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (himage : ImageDecoded program)
    (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i) (hbreak : i ≠ .EBREAK)
    (hsys : SystemInv b.pre) (hpc : b.row.address.getLsbD 0 = false)
    (hcode : ∀ s, Related b.pre s → CodeIntact program s)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  rcases access_classified program b hruns i hrow with hram | hio | hamo
  · exact block_simulates_decoded program b hruns himage i hrow hbreak hsys hpc
      (fun _ hrel => hrel.misa) hcode hheap (Or.inl hram)
  · exact block_simulates_decoded program b hruns himage i hrow hbreak hsys hpc
      (fun _ hrel => hrel.misa) hcode hheap (Or.inr hio)
  · obtain ⟨e, hd⟩ := himage b.row hruns.row_mem i hrow
    have hwidth : b.row.is_compressed = e.isCompressed := by
      cases e with
      | base w => exact hd.1
      | compressed h => exact hd.1
    have hin := decoded_inputs program b hruns i e hd hpc (fun s hrel => hrel.misa) hcode
    refine block_simulates_io_amo_via program b hruns i hrow hsys hamo e hwidth ?_
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hinc, hf, ast, cast, hm, hb, hdc, _⟩ := hin s hrel pc m oldInc hn hr
    exact ⟨inc, hinc, hf, ast, cast, hm, hb, hdc⟩

end WholeRun
