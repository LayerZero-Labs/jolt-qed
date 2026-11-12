import JoltBytecode.Inlines.Keccak256.Sound

/-!
# `KECCAK256` and `KECCAK256_ABSORB_PERMUTE`: known-answer instances

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input, to show that its hypotheses can hold. This module builds one concrete machine
state and applies the headline theorems of `Keccak256/Sound.lean` to it:

* the zero Keccak state lies in RAM at `0x8002_0000`, and `x10` points to it;
* the block of the empty message after Keccak-256 padding (byte 0 is `0x01`, byte 135 is `0x80`)
  lies at `0x8002_00c8`, right after the state, and `x11` points to it;
* the stack ends at `0x8000_1000` and the heap at `0x8010_0000`, so the state buffer is
  writable.

`keccak256_kat` says the `KECCAK256` rows run, the run meets `Keccak256Spec`, and the state
buffer then holds `keccakF State.zero`. The first `#guard` checks that this is the Keccak team's
`KeccakKAT-3` answer for the zero state, whose first lane is `0xf1258f7940e1dde7`.

`absorbPermute_kat` says the `KECCAK256_ABSORB_PERMUTE` rows run, the run meets
`AbsorbPermuteSpec`, and the state buffer then holds EthLib's absorb-and-permute of the padded
block. The second `#guard` checks that its first four lanes are Keccak-256(""), that is
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Keccak256
  JoltISA.Inlines.Generated JoltSpec.Keccak JoltSpec.Keccak.Internal

set_option autoImplicit false

noncomputable section

namespace JoltTests.KeccakInstance

/-- The block of the empty message after Keccak-256 padding, as 17 little-endian lanes. -/
def katBlock : List (BitVec 64) :=
  [0x01#64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000#64]

/-- Keccak-f[1600] of the zero state, `KeccakKAT-3` (`keccakFZero` in
`JoltTests.InlineKat.Manifest`), as 25 lanes. -/
def katZeroF : List (BitVec 64) :=
  [0xf1258f7940e1dde7#64, 0x84d5ccf933c0478a#64, 0xd598261ea65aa9ee#64,
    0xbd1547306f80494d#64, 0x8b284e056253d057#64, 0xff97a42d7f8e6fd4#64,
    0x90fee5a0a44647c4#64, 0x8c5bda0cd6192e76#64, 0xad30a6f71b19059c#64,
    0x30935ab7d08ffc64#64, 0xeb5aa93f2317d635#64, 0xa9a6e6260d712103#64,
    0x81a57c16dbcf555f#64, 0x43b831cd0347c826#64, 0x01f22f1a11a5569f#64,
    0x05e5635a21d9ae61#64, 0x64befef28cc970f2#64, 0x613670957bc46611#64,
    0xb87c5a554fd00ecb#64, 0x8c3ee88a1ccf32c8#64, 0x940c7922ae3a2614#64,
    0x1841f924a2c509e4#64, 0x16f53526e70465c2#64, 0x75f644e97f30a13b#64,
    0xeaf1ff7b5ceca249#64]

/-- Keccak-256(""), as four little-endian lanes. -/
def katDigest : List (BitVec 64) :=
  [0x3c23f7860146d2c5#64, 0xc003c7dcb27d7e92#64, 0x3b2782ca53b600e5#64,
    0x70a4855d04d8fa7b#64]

#guard wordsOf (keccakF State.zero) == katZeroF

#guard (wordsOf (keccakF (absorbBlock 136 State.zero (blockBytes katBlock) 0))).take 4 ==
  katDigest

/-- The 42 doublewords in RAM from `0x8002_0000`: the zero state, then the block. -/
def katWords : List (BitVec 64) := List.replicate 25 0 ++ katBlock

/-- The address of the state buffer, `0x8002_0000`; `x10` holds it. -/
def katA : BitVec 64 := 0x80020000#64

/-- The address of the block buffer, `0x8002_00c8`; `x11` holds it. -/
def katB : BitVec 64 := 0x800200c8#64

/-- A memory layout whose stack ends at `0x8000_1000` and whose heap ends at `0x8010_0000`;
the I/O fields are zero because the instance touches only RAM. -/
def katLayout : MemoryLayout where
  program_size := 0
  max_trusted_advice_size := 0
  trusted_advice_start := 0
  trusted_advice_end := 0
  max_untrusted_advice_size := 0
  untrusted_advice_start := 0
  untrusted_advice_end := 0
  max_input_size := 0
  max_output_size := 0
  input_start := 0
  input_end := 0
  output_start := 0
  output_end := 0
  stack_size := 0x1000
  stack_end := 0x80001000
  heap_size := 0xff000
  heap_end := 0x80100000
  panic := 0
  termination := 0
  io_end := 0

/-- The device: no I/O, the layout above. -/
def katDevice : JoltDevice where
  inputs := #[]
  trusted_advice := #[]
  untrusted_advice := #[]
  outputs := #[]
  panic := false
  memory_layout := katLayout

/-- The Sail state: `x10 = katA`, `x11 = katB`, and `katWords` in RAM from `katA`. -/
def katSail : SailState :=
  stateAfterWrite
    (stateAfterWrite
      { regs := ∅, choiceState := (), mem := writeDwords ∅ katA.toNat katWords, tags := (),
        cycleCount := 0, sailOutput := #[] }
      (regidx.Regidx 10) katA)
    (regidx.Regidx 11) katB

/-- The machine state of the instance. -/
def katState : SailJoltState where
  sail := katSail
  jolt_device := katDevice
  adviceTape := ⟨#[], 0⟩

private theorem regidx_ne {a b : BitVec 5} (h : a ≠ b) : regidx.Regidx a ≠ regidx.Regidx b :=
  fun e => h (by cases e; rfl)

private theorem kat_reads_x11 : XReads katState (regidx.Regidx 11) katB :=
  rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide))

private theorem kat_reads_x10 : XReads katState (regidx.Regidx 10) katA :=
  rX_bits_stateAfterWrite_of_ne _ _ _ _ _ (regidx_ne (by decide))
    (rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide)))

private theorem kat_hA : keccakA (regidx.Regidx 10) katState = katA :=
  (XReads.eq_sourceValue kat_reads_x10).symm

private theorem kat_hB : keccakB (regidx.Regidx 11) katState = katB :=
  (XReads.eq_sourceValue kat_reads_x11).symm

private theorem kat_writable (ea : Nat) (h1 : katA.toNat ≤ ea) (h2 : ea + 8 ≤ katA.toNat + 336)
    (h8 : ea % 8 = 0) : DwordWritable katDevice ea := by
  refine ⟨h8, ?_⟩
  simp only [katA, BitVec.toNat_ofNat] at h1 h2
  norm_num at h1 h2
  have hn : ¬ ea < RAM_START_ADDRESS := by unfold RAM_START_ADDRESS; omega
  simp only [Mmu.effective_address_ok, hn, ite_false, katDevice, katLayout, STACK_CANARY_SIZE]
  have e1 : (2147487744 : BitVec 64).toNat = 2147487744 := rfl
  have e2 : (2148532224 : BitVec 64).toNat = 2148532224 := rfl
  simp only [ite_true, e1, e2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

private theorem kat_load (k : Nat) (hk : k < 42) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * k)) = katWords[k]? :=
  loadDword?_of_mem_writeDwords (t := katState) (m := ∅) rfl (by decide)
    (by simp [katA, katWords, katBlock])
    (fun j hj => kat_writable _ (by simp) (by simp [katA, katWords, katBlock] at hj ⊢; omega)
      (by simp [katA]))
    (by simpa [katWords, katBlock] using hk)

private theorem katB_add (n : Nat) :
    katB + BitVec.ofNat 64 n = katA + BitVec.ofNat 64 (200 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [katA, katB, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem kat_lane (i : Nat) (hi : i < 25) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * i)) = some 0 := by
  rw [kat_load i (by omega)]
  interval_cases i <;> rfl

private theorem kat_block_lane (j : Nat) (hj : j < 17) :
    loadDword? katState (katB + BitVec.ofNat 64 (8 * j)) = some (katBlock.getD j 0) := by
  rw [katB_add _, show 200 + 8 * j = 8 * (25 + j) by omega, kat_load _ (by omega)]
  interval_cases j <;> rfl

/-- The loads of a call read the zero state. -/
theorem kat_state : stateAt katState katA = State.zero := by
  rw [stateAt, ofLanes_congr (g' := fun _ => 0) fun i hi => by
    rw [loadLane, kat_lane i hi, Option.getD_some]]
  rfl

/-- The block loads of a call read `katBlock`. -/
theorem kat_block : blockAt katState katB = katBlock := by
  apply List.ext_getElem (by simp [blockAt, katBlock])
  intro j h1 h2
  have hj : j < 17 := by simpa [blockAt] using h1
  simp only [blockAt, List.getElem_map, List.getElem_range]
  rw [loadLane, kat_block_lane j hj, Option.getD_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- The hypotheses of the `KECCAK256` completeness theorem hold for the instance: for example,
the 25 doublewords at `0x8002_0000..0x8002_00c8` lie below the heap end `0x8010_0000`. -/
theorem kat_pre : Keccak256Pre (regidx.Regidx 10) katState where
  ram := by rw [kat_hA]; decide
  no_wrap := by rw [kat_hA]; decide
  reads1 := by rw [kat_hA]; exact kat_reads_x10
  readable i hi := by rw [kat_hA, kat_lane i hi]; rfl
  writable k hk := by
    rw [kat_hA]
    exact kat_writable _ (by omega) (by omega) (by simp [katA])

/-- The hypotheses of the `KECCAK256_ABSORB_PERMUTE` completeness theorem hold for the
instance. -/
theorem kat_absorb_pre : AbsorbPermutePre (regidx.Regidx 10) (regidx.Regidx 11) katState where
  toKeccak256Pre := kat_pre
  reads2 := by rw [kat_hB]; exact kat_reads_x11
  readable2 j hj := by rw [kat_hB, kat_block_lane j hj]; rfl

/-- **The `KECCAK256` instance.** From `katState`, the `KECCAK256` rows (with `rs1 = x10`,
`rs2 = x11`, `rs3 = x12`) run; by `keccak256_rows_sound` the run meets `Keccak256Spec`; and the
state buffer then holds `keccakF State.zero`, which the first `#guard` above checks is
`katZeroF`. -/
theorem keccak256_kat :
    ∃ s', (keccak256RowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)).Run
        katState s' ∧
      Keccak256Spec (regidx.Regidx 10) katState s' ∧
      ∀ i < 25, loadDword? s' (katA + BitVec.ofNat 64 (8 * i)) =
        (wordsOf (keccakF State.zero))[i]? := by
  obtain ⟨s', run, -⟩ := keccak256_rows_complete (rs2 := regidx.Regidx 11)
    (rs3 := regidx.Regidx 12) kat_pre
  have spec := keccak256_rows_sound kat_pre.toKeccakBuffer run
  refine ⟨s', run, spec, fun i hi => ?_⟩
  have h := spec.2.2 i hi
  rw [kat_hA, kat_state] at h
  exact h

/-- **The `KECCAK256_ABSORB_PERMUTE` instance.** From `katState`, the rows (with `rs1 = x10`,
`rs2 = x11`, `rs3 = x12`) run; by `absorbPermute_rows_sound` the run meets `AbsorbPermuteSpec`;
and the state buffer then holds EthLib's absorb-and-permute of the padded empty message, whose
first four lanes the second `#guard` above checks are Keccak-256(""). -/
theorem absorbPermute_kat :
    ∃ s', (keccak256AbsorbPermuteRowsAuto (regidx.Regidx 10) (regidx.Regidx 11)
        (regidx.Regidx 12)).Run katState s' ∧
      AbsorbPermuteSpec (regidx.Regidx 10) (regidx.Regidx 11) katState s' ∧
      ∀ i < 25, loadDword? s' (katA + BitVec.ofNat 64 (8 * i)) =
        (wordsOf (keccakF (absorbBlock 136 State.zero (blockBytes katBlock) 0)))[i]? := by
  obtain ⟨s', run, -⟩ := absorbPermute_rows_complete (rs3 := regidx.Regidx 12) kat_absorb_pre
  have spec := absorbPermute_rows_sound kat_absorb_pre.toKeccakBuffer run
  refine ⟨s', run, spec, fun i hi => ?_⟩
  have h := spec.2.2.2 i hi
  rw [kat_hA, kat_hB, absorbOut, kat_state, kat_block] at h
  rw [h, absorbBlock_blockBytes _ _ rfl]

end JoltTests.KeccakInstance
