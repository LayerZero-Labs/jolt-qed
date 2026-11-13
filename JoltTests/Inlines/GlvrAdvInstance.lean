import JoltBytecode.Inlines.Secp256k1.GlvrAdv

/-!
# `GLVR_ADV`: a known-answer instance of the soundness and completeness theorems

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input, to show that its hypotheses can hold. This module builds one concrete machine
state and applies both headline theorems of `GlvrAdv.lean` to it:

* the scalar `k` (four limbs below) lies in RAM at `0x8001_0000`, and `x10` points to it;
* the output buffer is at `0x8002_0000`, and `x12` points to it;
* the stack ends at `0x8000_1000` and the heap at `0x8010_0000`, so both buffers are writable.

`glvrAdv_kat` says the rows run with Jolt's advice for `k`, the run meets `GlvrAdvSpec`, and the
buffer then holds the six words below. The words are Jolt's split
`k ≡ -k₁ + λ·k₂ (mod n)` with `k₁ = 0x213c3de8a76e3bd1_2e4cbe1fe695c34d` (126 bits) and
`k₂ = 0x08fc4249719076b4_b2eae28114375049` (124 bits); a Python check of the identity with the
standard secp256k1 `λ` gave `0`.

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1
  JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltTests.GlvrAdvInstance

/-- The scalar: four little-endian limbs, the lowest `0x0123456789abcdef`. Its value is
`0x1122334455667788_0f1e2d3c4b5a6978_fedcba9876543210_0123456789abcdef`. -/
def katK : Limbs :=
  #v[0x0123456789abcdef#64, 0xfedcba9876543210#64, 0x0f1e2d3c4b5a6978#64, 0x1122334455667788#64]

/-- Jolt's six advice words for `katK`: `[sign₁, k₁ low, k₁ high, sign₂, k₂ low, k₂ high]`.
For example, `sign₁ = 1` (`k₁` enters negated) and `sign₂ = 0`. -/
def katWords : List (BitVec 64) :=
  [0x1#64, 0x2e4cbe1fe695c34d#64, 0x213c3de8a76e3bd1#64,
    0x0#64, 0xb2eae28114375049#64, 0x08fc4249719076b4#64]

/-- The address of the scalar, `0x8001_0000`; `x10` holds it. -/
def katIn : BitVec 64 := 0x80010000#64

/-- The address of the output buffer, `0x8002_0000`; `x12` holds it. -/
def katOut : BitVec 64 := 0x80020000#64

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

/-- The Sail state: `x10 = katIn`, `x12 = katOut`, and the scalar's limbs in RAM at `katIn`. -/
def katSail : SailState :=
  stateAfterWrite
    (stateAfterWrite
      { regs := ∅, choiceState := (), mem := writeDwords ∅ katIn.toNat katK.toList, tags := (),
        cycleCount := 0, sailOutput := #[] }
      (regidx.Regidx 10) katIn)
    (regidx.Regidx 12) katOut

/-- The machine state of the instance: `x10 = 0x8001_0000`, `x12 = 0x8002_0000`, and `katK` in
RAM at `0x8001_0000..0x8001_0020`. -/
def katState : SailJoltState where
  sail := katSail
  jolt_device := katDevice
  adviceTape := ⟨#[], 0⟩

private theorem regidx_ne {a b : BitVec 5} (h : a ≠ b) : regidx.Regidx a ≠ regidx.Regidx b :=
  fun e => h (by cases e; rfl)

private theorem kat_reads_x12 : XReads katState (regidx.Regidx 12) katOut :=
  rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide))

private theorem kat_reads_x10 : XReads katState (regidx.Regidx 10) katIn :=
  rX_bits_stateAfterWrite_of_ne _ _ _ _ _ (regidx_ne (by decide))
    (rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide)))

private theorem kat_out : glvrOut (regidx.Regidx 12) katState = katOut :=
  (XReads.eq_sourceValue kat_reads_x12).symm

private theorem kat_in : sourceValue (.xreg (regidx.Regidx 10)) katState = katIn :=
  (XReads.eq_sourceValue kat_reads_x10).symm

private theorem kat_writable (ea : Nat) (h1 : katIn.toNat ≤ ea) (h2 : ea + 8 ≤ katOut.toNat + 48)
    (h8 : ea % 8 = 0) : DwordWritable katDevice ea := by
  refine ⟨h8, ?_⟩
  simp only [katIn, katOut, BitVec.toNat_ofNat] at h1 h2
  norm_num at h1 h2
  have hn : ¬ ea < RAM_START_ADDRESS := by unfold RAM_START_ADDRESS; omega
  simp only [Mmu.effective_address_ok, hn, ite_false, katDevice, katLayout, STACK_CANARY_SIZE]
  have e1 : (2147487744 : BitVec 64).toNat = 2147487744 := rfl
  have e2 : (2148532224 : BitVec 64).toNat = 2148532224 := rfl
  simp only [ite_true, e1, e2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The hypotheses of the completeness theorem hold for the instance: for example, the six
doublewords at `0x8002_0000..0x8002_0030` lie below the heap end `0x8010_0000`. -/
theorem kat_pre : GlvrAdvPre (regidx.Regidx 12) katState where
  ram := by rw [kat_out]; decide
  no_wrap := by rw [kat_out]; decide
  reads := by rw [kat_out]; exact kat_reads_x12
  writable k hk := by
    rw [kat_out]
    exact kat_writable _ (by simp [katIn, katOut]; omega) (by simp [katOut]; omega)
      (by simp [katOut])

/-- The scalar reads back from RAM: the doubleword at `0x8001_0000` is `0x0123456789abcdef`,
and so on. -/
theorem kat_limbs : readLimbs? katState katIn = some katK := by
  have load : ∀ i, i < 4 → loadDword? katState (katIn + BitVec.ofNat 64 (8 * i)) =
      katK.toList[i]? := fun i hi =>
    loadDword?_of_mem_writeDwords (t := katState) (m := ∅) rfl (by decide) (by simp [katIn])
      (fun j hj => kat_writable _ (by simp) (by simp [katIn, katOut] at hj ⊢; omega)
        (by simp [katIn]))
      (by simpa using hi)
  have l0 := load 0 (by decide)
  have l1 := load 1 (by decide)
  have l2 := load 2 (by decide)
  have l3 := load 3 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at l0
  unfold readLimbs?
  rw [l0, show katIn + 8 = katIn + BitVec.ofNat 64 (8 * 1) from rfl, l1,
    show katIn + 16 = katIn + BitVec.ofNat 64 (8 * 2) from rfl, l2,
    show katIn + 24 = katIn + BitVec.ofNat 64 (8 * 3) from rfl, l3]
  rfl

/-- Jolt's advice for `katK` is `katWords`: for example, word 1 is `0x2e4cbe1fe695c34d`, the
low limb of `k₁`. -/
theorem kat_advice : (glvrAdvice katK).toList = katWords := by decide

/-- **The instance.** From `katState`, the `GLVR_ADV` rows (with `rs1 = x10`, `rs2 = x11`,
`rs3 = x12`) run with Jolt's advice for `katK`; by `glvrAdv_rows_sound` the run meets
`GlvrAdvSpec`; and the output buffer then holds `katWords`. -/
theorem glvrAdv_kat :
    ∃ s', (secp256k1GlvrAdvRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (glvrAdvAdvice katK)).Run katState s' ∧
      GlvrAdvSpec (regidx.Regidx 12) katState s' ∧
      ∀ i, i < 6 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) = katWords[i]? := by
  obtain ⟨s', run, -, canon⟩ := glvrAdv_rows_jolt_advice_complete (rs1 := regidx.Regidx 10)
    (rs2 := regidx.Regidx 11) kat_pre (by rw [kat_in]; exact kat_limbs)
  refine ⟨s', run, glvrAdv_rows_sound kat_pre.toGlvrAdvBuffer run, fun i hi => ?_⟩
  have h := canon i hi
  rw [kat_out] at h
  rw [h, ← kat_advice, Vector.getElem?_toList, Vector.getElem?_eq_getElem hi]

end JoltTests.GlvrAdvInstance
