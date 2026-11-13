import JoltBytecode.Inlines.Sha256.Sound

/-!
# `SHA256` and `SHA256_INIT`: a known-answer instance of the soundness and completeness theorems

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input, to show that its hypotheses can hold. This module builds one concrete machine
state and applies the headline theorems of `Sha256/Sound.lean` to it:

* the initial hash value of SHA-256 lies in RAM at `0x8002_0000`, two words per doubleword with
  the even word in the low half, and `x10` points to it;
* the padded one-block message "abc" (the bytes `61 62 63 80`, zeros, and the bit length `0x18`
  in the last byte) lies at `0x8002_0020`, and `x11` points to it. The loads read it as
  `katBlock`, and a `#guard` checks that `katBlock` is the 16 big-endian words of that block;
* the stack ends at `0x8000_1000` and the heap at `0x8010_0000`, so the state buffer is
  writable.

`sha256_kat` (for `SHA256`, which loads the state) and `sha256Init_kat` (for `SHA256_INIT`,
which starts from `Spec.initial`) say the rows run, the run meets `Sha256Spec`, and the state
buffer then holds `Spec.compression katBlock Spec.initial`. The `#guard` below checks that this
compression is SHA-256("abc") = `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c
b410ff61 f20015ad` (FIPS 180-4 example, NIST CSRC).

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Sha256
  JoltISA.Inlines.Generated JoltSpec.Sha256 JoltSpec.Sha256.Spec

set_option autoImplicit false

noncomputable section

namespace JoltTests.Sha256Instance

/-- The initial hash value as four doublewords: word `2i` in the low half of doubleword `i`. -/
def katH : Vector (BitVec 64) 4 :=
  #v[0xbb67ae856a09e667#64, 0xa54ff53a3c6ef372#64, 0x9b05688c510e527f#64, 0x5be0cd191f83d9ab#64]

/-- The padded block of "abc" as eight little-endian doublewords. -/
def katM : Vector (BitVec 64) 8 :=
  #v[0x0000000080636261#64, 0, 0, 0, 0, 0, 0, 0x1800000000000000#64]

/-- The block that the loads read from `katM`: word `j` is the byte swap of half `j mod 2` of
doubleword `j / 2`. -/
def katBlock : Vector Word 16 :=
  Vector.ofFn fun j => byteSwap (halfWord katM[j.val / 2] j.val)

#guard katBlock == #v[0x61626380#32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x18#32]

/-- SHA-256("abc") as four doublewords, word `2i` in the low half of doubleword `i`. -/
def katOut : Vector (BitVec 64) 4 :=
  #v[0x8f01cfeaba7816bf#64, 0x5dae2223414140de#64, 0x96177a9cb00361a3#64, 0xf20015adb410ff61#64]

#guard (Vector.ofFn fun i : Fin 4 => (compression katBlock initial).get (2 * i.val + 1) ++
  (compression katBlock initial).get (2 * i.val)) == katOut

/-- The 12 doublewords in RAM from `0x8002_0000`: the state, then the block. -/
def katWords : List (BitVec 64) := katH.toList ++ katM.toList

/-- The address of the state buffer, `0x8002_0000`; `x10` holds it. -/
def katA : BitVec 64 := 0x80020000#64

/-- The address of the block buffer, `0x8002_0020`; `x11` holds it. -/
def katB : BitVec 64 := 0x80020020#64

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

private theorem kat_hA : sha256H (regidx.Regidx 10) katState = katA :=
  (XReads.eq_sourceValue kat_reads_x10).symm

private theorem kat_hB : sha256M (regidx.Regidx 11) katState = katB :=
  (XReads.eq_sourceValue kat_reads_x11).symm

private theorem kat_writable (ea : Nat) (h1 : katA.toNat ≤ ea) (h2 : ea + 8 ≤ katA.toNat + 96)
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

private theorem kat_load (k : Nat) (hk : k < 12) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * k)) = katWords[k]? :=
  loadDword?_of_mem_writeDwords (t := katState) (m := ∅) rfl (by decide)
    (by simp [katA, katWords])
    (fun j hj => kat_writable _ (by simp) (by simp [katA, katWords] at hj ⊢; omega)
      (by simp [katA]))
    (by simpa [katWords] using hk)

private theorem katB_add (n : Nat) :
    katB + BitVec.ofNat 64 n = katA + BitVec.ofNat 64 (32 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [katA, katB, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem kat_h (i : Nat) (hi : i < 4) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * i)) = some katH[i] := by
  rw [kat_load i (by omega)]
  interval_cases i <;> rfl

private theorem kat_m (j : Nat) (hj : j < 8) :
    loadDword? katState (katB + BitVec.ofNat 64 (8 * j)) = some katM[j] := by
  rw [katB_add _, show 32 + 8 * j = 8 * (4 + j) by omega, kat_load _ (by omega)]
  interval_cases j <;> rfl

private theorem kat_block (b : Bool) :
    (sha256Input b (regidx.Regidx 10) (regidx.Regidx 11) katState).block = katBlock := by
  unfold sha256Input
  rw [kat_hA, kat_hB]
  apply Vector.ext
  intro j hj
  simp only [input, katBlock, Vector.getElem_ofFn, dword, kat_m (j / 2) (by omega),
    Option.getD_some]

private theorem kat_dwordA (i : Nat) (hi : i < 4) : dword katState katA i = katH[i] := by
  rw [dword, kat_h i hi, Option.getD_some]

private theorem kat_state (b : Bool) :
    (sha256Input b (regidx.Regidx 10) (regidx.Regidx 11) katState).state = initial := by
  unfold sha256Input
  rw [kat_hA]
  cases b with
  | true => rfl
  | false =>
    simp only [input, Bool.false_eq_true, ↓reduceIte]
    unfold stateOf
    rw [kat_dwordA 0 (by decide), kat_dwordA 1 (by decide), kat_dwordA 2 (by decide),
      kat_dwordA 3 (by decide)]
    decide

/-- The hypotheses of the completeness theorems hold for the instance: for example, the four
doublewords at `0x8002_0000..0x8002_0020` lie below the heap end `0x8010_0000`. -/
theorem kat_pre (b : Bool) : Sha256Pre b (regidx.Regidx 10) (regidx.Regidx 11) katState where
  ram := by rw [kat_hA]; decide
  no_wrap := by rw [kat_hA]; decide
  reads1 := by rw [kat_hA]; exact kat_reads_x10
  reads2 := by rw [kat_hB]; exact kat_reads_x11
  readable := by
    rw [kat_hA, kat_hB]
    refine ⟨fun _ i hi => ?_, fun j hj => ?_⟩
    · rw [kat_h i hi]; rfl
    · rw [kat_m j hj]; rfl
  writable k hk := by
    rw [kat_hA]
    exact kat_writable _ (by omega) (by omega) (by simp [katA])

/-- **The `SHA256` instance.** From `katState`, the `SHA256` rows (with `rs1 = x10`,
`rs2 = x11`, `rs3 = x12`) run; by `sha256_rows_sound` the run meets `Sha256Spec`; and the state
buffer then holds `Spec.compression katBlock Spec.initial`, which the `#guard` above checks is
`katOut`. -/
theorem sha256_kat :
    ∃ s', (sha256RowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)).Run
        katState s' ∧
      Sha256Spec false (regidx.Regidx 10) (regidx.Regidx 11) katState s' ∧
      ∀ i < 4, loadDword? s' (katA + BitVec.ofNat 64 (8 * i)) =
        some ((compression katBlock initial).get (2 * i + 1) ++
          (compression katBlock initial).get (2 * i)) := by
  obtain ⟨s', run, -⟩ := sha256_rows_complete (rs3 := regidx.Regidx 12) (kat_pre false)
  refine ⟨s', run, sha256_rows_sound (kat_pre false).toSha256Buffer run, fun i hi => ?_⟩
  have h := sha256_rows_sound_compression (kat_pre false).toSha256Buffer run i hi
  rw [kat_hA, kat_block, kat_state] at h
  exact h

/-- **The `SHA256_INIT` instance.** From `katState`, the `SHA256_INIT` rows run; by
`sha256Init_rows_sound` the run meets `Sha256Spec`; and the state buffer then holds
`Spec.compression katBlock Spec.initial`, which the `#guard` above checks is `katOut`. -/
theorem sha256Init_kat :
    ∃ s', (sha256InitRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)).Run
        katState s' ∧
      Sha256Spec true (regidx.Regidx 10) (regidx.Regidx 11) katState s' ∧
      ∀ i < 4, loadDword? s' (katA + BitVec.ofNat 64 (8 * i)) =
        some ((compression katBlock initial).get (2 * i + 1) ++
          (compression katBlock initial).get (2 * i)) := by
  obtain ⟨s', run, -⟩ := sha256Init_rows_complete (rs3 := regidx.Regidx 12) (kat_pre true)
  refine ⟨s', run, sha256Init_rows_sound (kat_pre true).toSha256Buffer run, fun i hi => ?_⟩
  have h := sha256Init_rows_sound_compression (kat_pre true).toSha256Buffer run i hi
  rw [kat_hA, kat_block] at h
  exact h

end JoltTests.Sha256Instance
