import JoltBytecode.Inlines.Blake2b.Sound

/-!
# `BLAKE2`: a known-answer instance of the soundness and completeness theorems

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input, to show that its hypotheses can hold. This module builds one concrete machine
state and applies the headline theorems of `Blake2b/Sound.lean` to it:

* the state `h` of BLAKE2b-512 (the IV with the parameter block `0x01010040` XORed into word 0)
  lies in RAM at `0x8002_0000`, and `x10` points to it;
* the message block "abc" (then 125 zero bytes), the counter 3 and the final-block flag 1 lie
  at `0x8002_0040`, and `x11` points to it;
* the stack ends at `0x8000_1000` and the heap at `0x8010_0000`, so the state buffer is
  writable.

These are the inputs of RFC 7693 appendix A and EIP-152 vector 5. `blake2_kat` says the rows
run, the run meets `Blake2Spec`, and the state buffer then holds `Spec.compress 12` of these
inputs. The `#guard` below checks that this compression is the RFC's BLAKE2b-512("abc"),
whose first word is `0x0d4d1c983fa580ba`.

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Blake2b
  JoltISA.Inlines.Generated JoltSpec.Blake2b

set_option autoImplicit false

noncomputable section

namespace JoltTests.Blake2Instance

/-- The state `h` of BLAKE2b-512: the IV, with `0x01010040` XORed into word 0. -/
def katH : Vector (BitVec 64) 8 :=
  #v[0x6a09e667f2bdc948#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
    0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-- The message block: "abc" as little-endian bytes, then zeros. -/
def katM : Vector (BitVec 64) 16 :=
  #v[0x636261#64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- BLAKE2b-512("abc") as eight little-endian words, RFC 7693 appendix A. -/
def katOut : Vector (BitVec 64) 8 :=
  #v[0x0d4d1c983fa580ba#64, 0xe9f6129fb697276a#64, 0xb7c45a68142f214c#64, 0xd1a2ffdb6fbb124b#64,
    0x2d79ab2a39c5877d#64, 0x95cc3345ded552c2#64, 0x5a92f1dba88ad318#64, 0x239900d4ed8623b9#64]

#guard Spec.compress 12 katH katM 3 true == katOut

/-- The 26 doublewords in RAM from `0x8002_0000`: `h`, the block, the counter 3 and the flag 1.
-/
def katWords : List (BitVec 64) := katH.toList ++ katM.toList ++ [3, 1]

/-- The address of the state buffer, `0x8002_0000`; `x10` holds it. -/
def katA : BitVec 64 := 0x80020000#64

/-- The address of the message buffer, `0x8002_0040`; `x11` holds it. -/
def katB : BitVec 64 := 0x80020040#64

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

private theorem kat_hA : blake2H (regidx.Regidx 10) katState = katA :=
  (XReads.eq_sourceValue kat_reads_x10).symm

private theorem kat_hB : blake2M (regidx.Regidx 11) katState = katB :=
  (XReads.eq_sourceValue kat_reads_x11).symm

private theorem kat_writable (ea : Nat) (h1 : katA.toNat ≤ ea) (h2 : ea + 8 ≤ katA.toNat + 208)
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

private theorem kat_load (k : Nat) (hk : k < 26) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * k)) = katWords[k]? :=
  loadDword?_of_mem_writeDwords (t := katState) (m := ∅) rfl (by decide)
    (by simp [katA, katWords])
    (fun j hj => kat_writable _ (by simp) (by simp [katA, katWords] at hj ⊢; omega)
      (by simp [katA]))
    (by simpa [katWords] using hk)

private theorem katB_add (n : Nat) :
    katB + BitVec.ofNat 64 n = katA + BitVec.ofNat 64 (64 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [katA, katB, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem kat_h (i : Nat) (hi : i < 8) :
    loadDword? katState (katA + BitVec.ofNat 64 (8 * i)) = some katH[i] := by
  rw [kat_load i (by omega)]
  interval_cases i <;> rfl

private theorem kat_m (j : Nat) (hj : j < 16) :
    loadDword? katState (katB + BitVec.ofNat 64 (8 * j)) = some katM[j] := by
  rw [katB_add _, show 64 + 8 * j = 8 * (8 + j) by omega, kat_load _ (by omega)]
  interval_cases j <;> rfl

private theorem kat_t : loadDword? katState (katB + 128) = some 3 := by
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, katB_add _,
    show 64 + 128 = 8 * 24 from rfl, kat_load _ (by decide)]
  rfl

private theorem kat_flag : loadDword? katState (katB + 136) = some 1 := by
  rw [show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl, katB_add _,
    show 64 + 136 = 8 * 25 from rfl, kat_load _ (by decide)]
  rfl

/-- The loads of a call read `katH`, `katM`, the counter 3 and the flag 1. -/
theorem kat_input :
    blake2Input (regidx.Regidx 10) (regidx.Regidx 11) katState = ⟨katH, katM, 3, 1⟩ := by
  unfold blake2Input
  rw [kat_hA, kat_hB]
  simp only [input, kat_t, kat_flag, Option.getD_some, Input.mk.injEq, and_true]
  constructor
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, kat_h i hi, Option.getD_some]
  · apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, kat_m j hj, Option.getD_some]

/-- The hypotheses of the completeness theorem hold for the instance: for example, the eight
doublewords at `0x8002_0000..0x8002_0040` lie below the heap end `0x8010_0000`, and the flag
is 1. -/
theorem kat_pre : Blake2Pre (regidx.Regidx 10) (regidx.Regidx 11) katState where
  ram := by rw [kat_hA]; decide
  no_wrap := by rw [kat_hA]; decide
  reads1 := by rw [kat_hA]; exact kat_reads_x10
  reads2 := by rw [kat_hB]; exact kat_reads_x11
  readable := by
    rw [kat_hA, kat_hB]
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_, ?_⟩
    · rw [kat_h i hi]; rfl
    · rw [kat_m j hj]; rfl
    · rw [kat_t]; rfl
    · rw [kat_flag]; rfl
  writable k hk := by
    rw [kat_hA]
    exact kat_writable _ (by omega) (by omega) (by simp [katA])
  flag := by rw [kat_input]; exact Or.inr rfl

/-- **The instance.** From `katState`, the `BLAKE2` rows (with `rs1 = x10`, `rs2 = x11`,
`rs3 = x12`) run; by `blake2_rows_sound` the run meets `Blake2Spec`; and the state buffer then
holds `Spec.compress 12 katH katM 3 true`, which the `#guard` above checks is `katOut`. -/
theorem blake2_kat :
    ∃ s', (blake2RowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)).Run
        katState s' ∧
      Blake2Spec (regidx.Regidx 10) (regidx.Regidx 11) katState s' ∧
      ∀ i (hi : i < 8), loadDword? s' (katA + BitVec.ofNat 64 (8 * i)) =
        some (Spec.compress 12 katH katM 3 true)[i] := by
  obtain ⟨s', run, -⟩ := blake2_rows_complete (rs3 := regidx.Regidx 12) kat_pre
  refine ⟨s', run, blake2_rows_sound kat_pre.toBlake2Buffer run, fun i hi => ?_⟩
  have h := blake2_rows_sound_compress kat_pre.toBlake2Buffer run kat_pre.flag i hi
  rw [kat_hA, kat_input] at h
  rw [h]
  rfl

end JoltTests.Blake2Instance
