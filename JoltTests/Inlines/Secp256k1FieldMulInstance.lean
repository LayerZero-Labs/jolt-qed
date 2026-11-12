import JoltBytecode.Inlines.Secp256k1.FieldMul

/-!
# secp256k1 `MUL` and `SQUARE`: known-answer instances of the soundness and completeness theorems

Section 5.4 of `docs/inline-precompiles.md` asks for each `rows_sound` theorem to be applied to a
concrete input, to show that its hypotheses can hold. This module builds one concrete machine
state per inline and applies both headline theorems of `FieldMul.lean` to it:

* the operands `a` and `b` (four limbs each) lie in RAM at `0x8001_0000` and `0x8001_0020`, and
  `x10` and `x11` point to them;
* the output buffer is at `0x8002_0000`, and `x12` points to it;
* the stack ends at `0x8000_1000` and the heap at `0x8010_0000`, so all three buffers are
  writable.

The four instances, with Jolt's quotient advice `w = 1` in each:

* `MULQ`: `a = 2`, `b = (p + 1) / 2`, so `a·b = p + 1` and the result is `1`;
* `MULR`: `a = 2`, `b = (n + 1) / 2`, so the result is `1`;
* `SQUAREQ`: `a = 2^128`, so `a² = 2^256` and the result is `2^256 - p = 0x1000003d1`;
* `SQUARER`: `a = 2^128`, and the result is `2^256 - n = 0x14551231950b75fc4402da1732fc9bebf`.

Each instance says the rows run with Jolt's advice, the run meets `FieldMulSpec` (through the
inline's `rows_sound` theorem), and the output buffer then holds the result above.

This module is a test: nothing in the headline import closure imports it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1
  JoltISA.Inlines.Generated

set_option autoImplicit false

noncomputable section

namespace JoltTests.Secp256k1FieldMulInstance

/-! ## The machine state -/

/-- The address of the operands: `a` at `katIn`, `b` at `katIn + 32`.
Example: `katIn = 0x8001_0000`, so `b` starts at `0x8001_0020`. -/
def katIn : BitVec 64 := 0x80010000#64

/-- The address of the output buffer.
Example: `katOut = 0x8002_0000`; the four result words end at `0x8002_0020`. -/
def katOut : BitVec 64 := 0x80020000#64

/-- A memory layout whose stack ends at `0x8000_1000` and whose heap ends at `0x8010_0000`;
the I/O fields are zero because the instances touch only RAM.
Example: the stack canary `0x8000_1000..0x8000_1080` lies below `katIn = 0x8001_0000`. -/
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

/-- The device: no I/O, the layout above.
Example: `katDevice.memory_layout.heap_end = 0x8010_0000`. -/
def katDevice : JoltDevice where
  inputs := #[]
  trusted_advice := #[]
  untrusted_advice := #[]
  outputs := #[]
  panic := false
  memory_layout := katLayout

/-- The Sail state for operands `a` and `b`: `x10 = katIn`, `x11 = katIn + 32`,
`x12 = katOut`, and the limbs of `a` and then `b` in RAM at `katIn`.
Example: `katSail (natToLimbs 2) (natToLimbs 3)` has `x11 = 0x8001_0020` and the doubleword `3`
at `0x8001_0020`. -/
def katSail (a b : Limbs) : SailState :=
  stateAfterWrite
    (stateAfterWrite
      (stateAfterWrite
        { regs := ∅, choiceState := (), mem := writeDwords ∅ katIn.toNat (a.toList ++ b.toList),
          tags := (), cycleCount := 0, sailOutput := #[] }
        (regidx.Regidx 10) katIn)
      (regidx.Regidx 11) (katIn + 32))
    (regidx.Regidx 12) katOut

/-- The machine state of an instance with operands `a` and `b`.
Example: `katState (natToLimbs 2) (natToLimbs 3)` holds `2` at `0x8001_0000` and `3` at
`0x8001_0020`. -/
def katState (a b : Limbs) : SailJoltState where
  sail := katSail a b
  jolt_device := katDevice
  adviceTape := ⟨#[], 0⟩

private theorem regidx_ne {a b : BitVec 5} (h : a ≠ b) : regidx.Regidx a ≠ regidx.Regidx b :=
  fun e => h (by cases e; rfl)

/-- `x12` reads `katOut`.
Example: in `katState (natToLimbs 2) (natToLimbs 3)`, `x12 = 0x8002_0000`. -/
theorem kat_reads_x12 (a b : Limbs) :
    XReads (katState a b) (regidx.Regidx 12) katOut :=
  rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide))

/-- `x11` reads `katIn + 32`.
Example: in `katState (natToLimbs 2) (natToLimbs 3)`, `x11 = 0x8001_0020`. -/
theorem kat_reads_x11 (a b : Limbs) :
    XReads (katState a b) (regidx.Regidx 11) (katIn + 32) :=
  rX_bits_stateAfterWrite_of_ne _ _ _ _ _ (regidx_ne (by decide))
    (rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide)))

/-- `x10` reads `katIn`.
Example: in `katState (natToLimbs 2) (natToLimbs 3)`, `x10 = 0x8001_0000`. -/
theorem kat_reads_x10 (a b : Limbs) : XReads (katState a b) (regidx.Regidx 10) katIn :=
  rX_bits_stateAfterWrite_of_ne _ _ _ _ _ (regidx_ne (by decide))
    (rX_bits_stateAfterWrite_of_ne _ _ _ _ _ (regidx_ne (by decide))
      (rX_after_stateAfterWrite _ _ _ (regidx_ne (by decide))))

/-- The output buffer of an instance, through `x12`, is `katOut`.
Example: `fieldOut x12 (katState (natToLimbs 2) (natToLimbs 3)) = 0x8002_0000`. -/
theorem kat_out (a b : Limbs) : fieldOut (regidx.Regidx 12) (katState a b) = katOut :=
  (XReads.eq_sourceValue (kat_reads_x12 a b)).symm

/-- The source value of `x11` is `katIn + 32`.
Example: `0x8001_0020` in every instance state. -/
theorem kat_x11 (a b : Limbs) :
    sourceValue (.xreg (regidx.Regidx 11)) (katState a b) = katIn + 32 :=
  (XReads.eq_sourceValue (kat_reads_x11 a b)).symm

/-- The source value of `x10` is `katIn`.
Example: `0x8001_0000` in every instance state. -/
theorem kat_x10 (a b : Limbs) :
    sourceValue (.xreg (regidx.Regidx 10)) (katState a b) = katIn :=
  (XReads.eq_sourceValue (kat_reads_x10 a b)).symm

/-- Jolt may store a doubleword at every aligned address from `katIn` to the end of the
output buffer.
Example: `0x8001_0018` and `0x8002_0018` are writable. -/
theorem kat_writable (ea : Nat) (h1 : katIn.toNat ≤ ea) (h2 : ea + 8 ≤ katOut.toNat + 32)
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

/-- The hypotheses of the completeness theorems hold for every instance state.
Example: for `MULQ`, `x10` and `x11` read `0x8001_0000` and `0x8001_0020`, and Jolt may store
at `0x8002_0000..0x8002_0020`. -/
theorem kat_pre (op : FieldOp) (a b : Limbs) :
    FieldMulPre op (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12) (katState a b) where
  ram := by rw [kat_out]; decide
  no_wrap := by rw [kat_out]; decide
  reads1 := by rw [kat_x10]; exact kat_reads_x10 a b
  reads2 _ := by rw [kat_x11]; exact kat_reads_x11 a b
  reads3 := by rw [kat_out]; exact kat_reads_x12 a b
  writable k hk := by
    rw [kat_out]
    exact kat_writable _ (by simp [katIn, katOut]; omega) (by simp [katOut]; omega)
      (by simp [katOut])

/-- The eight operand words read back from RAM.
Example: in `katState (natToLimbs 2) (natToLimbs 3)`, word `4` at `0x8001_0020` is `3`. -/
theorem kat_load (a b : Limbs) (i : Nat) (hi : i < 8) :
    loadDword? (katState a b) (katIn + BitVec.ofNat 64 (8 * i)) = (a.toList ++ b.toList)[i]? :=
  loadDword?_of_mem_writeDwords (t := katState a b) (m := ∅) rfl (by decide) (by simp [katIn])
    (fun j hj => kat_writable _ (by simp) (by simp [katIn, katOut] at hj ⊢; omega)
      (by simp [katIn]))
    (by simpa using hi)

private theorem limbs_eta (a : Limbs) : (#v[a[0], a[1], a[2], a[3]] : Limbs) = a := by
  refine Vector.ext fun i hi => ?_
  interval_cases i <;> rfl

/-- The first operand reads back from RAM at `katIn`.
Example: `readLimbs? (katState (natToLimbs 2) (natToLimbs 3)) 0x8001_0000 = some (natToLimbs 2)`.
-/
theorem kat_limbs_a (a b : Limbs) : readLimbs? (katState a b) katIn = some a := by
  have l : ∀ i (hi : i < 4), loadDword? (katState a b) (katIn + BitVec.ofNat 64 (8 * i)) =
      some a[i] := fun i hi => by
    rw [kat_load a b i (by omega), List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  have l0 := l 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at l0
  unfold readLimbs?
  rw [l0, show katIn + 8 = katIn + BitVec.ofNat 64 (8 * 1) from rfl, l 1 (by decide),
    show katIn + 16 = katIn + BitVec.ofNat 64 (8 * 2) from rfl, l 2 (by decide),
    show katIn + 24 = katIn + BitVec.ofNat 64 (8 * 3) from rfl, l 3 (by decide)]
  exact congrArg some (limbs_eta a)

/-- The second operand reads back from RAM at `katIn + 32`.
Example: `readLimbs? (katState (natToLimbs 2) (natToLimbs 3)) 0x8001_0020 = some (natToLimbs 3)`.
-/
theorem kat_limbs_b (a b : Limbs) : readLimbs? (katState a b) (katIn + 32) = some b := by
  have l : ∀ i (hi : i < 4),
      loadDword? (katState a b) (katIn + BitVec.ofNat 64 (8 * (i + 4))) = some b[i] :=
    fun i hi => by
      rw [kat_load a b (i + 4) (by omega), List.getElem?_append_right (by simp)]
      simp [hi]
  unfold readLimbs?
  rw [show katIn + 32 = katIn + BitVec.ofNat 64 (8 * (0 + 4)) from rfl, l 0 (by decide),
    show katIn + BitVec.ofNat 64 (8 * (0 + 4)) + 8 = katIn + BitVec.ofNat 64 (8 * (1 + 4))
      from rfl, l 1 (by decide),
    show katIn + BitVec.ofNat 64 (8 * (0 + 4)) + 16 = katIn + BitVec.ofNat 64 (8 * (2 + 4))
      from rfl, l 2 (by decide),
    show katIn + BitVec.ofNat 64 (8 * (0 + 4)) + 24 = katIn + BitVec.ofNat 64 (8 * (3 + 4))
      from rfl, l 3 (by decide)]
  exact congrArg some (limbs_eta b)

/-- Four limbs are the limbs of their value. -/
private theorem natToLimbs_limbsToNat (c : Limbs) : natToLimbs (limbsToNat c) = c := by
  have h0 := c[0].isLt
  have h1 := c[1].isLt
  have h2 := c[2].isLt
  have h3 := c[3].isLt
  refine Vector.ext fun i hi => ?_
  apply BitVec.eq_of_toNat_eq
  interval_cases i <;>
    simp only [natToLimbs, limbsToNat, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat] <;> omega

/-- A run that meets the specification and leaves a canonical result stores `a·b mod q`.
Example: for `MULQ` with `a = 2` and `b = (p+1)/2`, the buffer at `0x8002_0000` holds `1`. -/
theorem kat_result {q : Nat} {op : FieldOp} {a b : Limbs} {s' : SailJoltState}
    (hsq : op = .square → b = a)
    (spec : FieldMulSpec q op (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
      (katState a b) s')
    (can : FieldMulCanonical q (regidx.Regidx 12) (katState a b) s') (i : Nat) (hi : i < 4) :
    loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
      (natToLimbs (limbsToNat a * limbsToNat b % q)).toList[i]? := by
  obtain ⟨a', b', w, c, ha', hsq', hb', ⟨rel, -, -⟩, -, hload⟩ := spec
  obtain ⟨c', hc', hload'⟩ := can
  rw [kat_x10, kat_limbs_a] at ha'
  have ea : a' = a := (Option.some.inj ha').symm
  have eb : b' = b := by
    by_cases h : op = .square
    · rw [hsq' h, hsq h, ea]
    · have := hb' h
      rw [kat_x11, kat_limbs_b] at this
      exact (Option.some.inj this).symm
  have ec : c = c' := Vector.ext fun j hj => by
    have e := (hload j hj).symm.trans (hload' j hj)
    simpa [Vector.getElem?_toList, hj] using e
  have hc : limbsToNat a * limbsToNat b % q = limbsToNat c := by
    rw [← ea, ← eb, rel, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by rw [ec]; exact hc')]
  rw [hc, natToLimbs_limbsToNat, ← hload i hi, kat_out]

/-! ## The four instances -/

/-- The first operand of the `MULQ` instance.
Example: `mulqA = #v[2, 0, 0, 0]`. -/
def mulqA : Limbs := natToLimbs 2

/-- The second operand of the `MULQ` instance, `(p + 1) / 2`.
Example: its low limb is `0xffffffff7ffffe18`. -/
def mulqB : Limbs := natToLimbs ((p + 1) / 2)

/-- The first operand of the `MULR` instance.
Example: `mulrA = #v[2, 0, 0, 0]`. -/
def mulrA : Limbs := natToLimbs 2

/-- The second operand of the `MULR` instance, `(n + 1) / 2`.
Example: its low limb is `0xdfe92f46681b20a1`. -/
def mulrB : Limbs := natToLimbs ((n + 1) / 2)

/-- The operand of both `SQUARE` instances, `2^128`.
Example: `squareA = #v[0, 0, 1, 0]`. -/
def squareA : Limbs := natToLimbs (2 ^ 128)

/-- **The `MULQ` instance.** From the instance state, the `SECP256K1_MULQ` rows (with
`rs1 = x10`, `rs2 = x11`, `rs3 = x12`) run with Jolt's quotient advice `w = 1`; by
`secp256k1Mulq_rows_sound` the run meets `FieldMulSpec`; and the output buffer then holds `1`.
Example: the doublewords at `0x8002_0000..0x8002_0018` end as `1, 0, 0, 0`. -/
theorem secp256k1Mulq_kat :
    joltAdvice .mulq mulqA mulqB = some (quotientWords (natToLimbs 1)) ∧
    ∃ s', (secp256k1MulqRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (quotientWords (natToLimbs 1)).getD i 0)).Run (katState mulqA mulqB) s' ∧
      FieldMulSpec p .mul (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState mulqA mulqB) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 1).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Mulq_rows_jolt_advice_complete
    (kat_pre .mul mulqA mulqB) (by rw [kat_x10]; exact kat_limbs_a _ _)
    (by rw [kat_x11]; exact kat_limbs_b _ _) (by decide) (by decide)
  have hadv : joltAdvice .mulq mulqA mulqB = some (quotientWords (natToLimbs 1)) := by decide
  rw [hadv] at hws
  cases Option.some.inj hws
  have spec := secp256k1Mulq_rows_sound (kat_pre .mul mulqA mulqB).toFieldMulBuffer run
  refine ⟨hadv, s', run, spec, fun i hi => ?_⟩
  rw [kat_result (fun h => absurd h (by decide)) spec can i hi]
  rfl

/-- **The `MULR` instance.** As `secp256k1Mulq_kat`, modulo `n`: the output buffer holds `1`.
Example: the doublewords at `0x8002_0000..0x8002_0018` end as `1, 0, 0, 0`. -/
theorem secp256k1Mulr_kat :
    joltAdvice .mulr mulrA mulrB = some (quotientWords (natToLimbs 1)) ∧
    ∃ s', (secp256k1MulrRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (quotientWords (natToLimbs 1)).getD i 0)).Run (katState mulrA mulrB) s' ∧
      FieldMulSpec n .mul (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState mulrA mulrB) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 1).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Mulr_rows_jolt_advice_complete
    (kat_pre .mul mulrA mulrB) (by rw [kat_x10]; exact kat_limbs_a _ _)
    (by rw [kat_x11]; exact kat_limbs_b _ _) (by decide) (by decide)
  have hadv : joltAdvice .mulr mulrA mulrB = some (quotientWords (natToLimbs 1)) := by decide
  rw [hadv] at hws
  cases Option.some.inj hws
  have spec := secp256k1Mulr_rows_sound (kat_pre .mul mulrA mulrB).toFieldMulBuffer run
  refine ⟨hadv, s', run, spec, fun i hi => ?_⟩
  rw [kat_result (fun h => absurd h (by decide)) spec can i hi]
  rfl

/-- **The `SQUAREQ` instance.** From the instance state with `a = 2^128` at both operand
addresses, the `SECP256K1_SQUAREQ` rows run with Jolt's quotient advice `w = 1`; the run meets
`FieldMulSpec`; and the output buffer then holds `2^256 - p = 0x1000003d1`.
Example: the doublewords at `0x8002_0000..0x8002_0018` end as `0x1000003d1, 0, 0, 0`. -/
theorem secp256k1Squareq_kat :
    joltAdvice .squareq squareA squareA = some (quotientWords (natToLimbs 1)) ∧
    ∃ s', (secp256k1SquareqRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (quotientWords (natToLimbs 1)).getD i 0)).Run (katState squareA squareA) s' ∧
      FieldMulSpec p .square (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState squareA squareA) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 0x1000003d1).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Squareq_rows_jolt_advice_complete
    (kat_pre .square squareA squareA) (by rw [kat_x10]; exact kat_limbs_a _ _) (by decide)
  have hadv : joltAdvice .squareq squareA squareA = some (quotientWords (natToLimbs 1)) := by
    decide
  rw [hadv] at hws
  cases Option.some.inj hws
  have spec :=
    secp256k1Squareq_rows_sound (kat_pre .square squareA squareA).toFieldMulBuffer run
  refine ⟨hadv, s', run, spec, fun i hi => ?_⟩
  rw [kat_result (fun _ => rfl) spec can i hi]
  rfl

/-- **The `SQUARER` instance.** As `secp256k1Squareq_kat`, modulo `n`: the output buffer holds
`2^256 - n = 0x14551231950b75fc4402da1732fc9bebf`.
Example: the doublewords at `0x8002_0000..0x8002_0018` end as `0x402da1732fc9bebf`,
`0x4551231950b75fc4`, `1`, `0`. -/
theorem secp256k1Squarer_kat :
    joltAdvice .squarer squareA squareA = some (quotientWords (natToLimbs 1)) ∧
    ∃ s', (secp256k1SquarerRowsAuto (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (fun i => (quotientWords (natToLimbs 1)).getD i 0)).Run (katState squareA squareA) s' ∧
      FieldMulSpec n .square (regidx.Regidx 10) (regidx.Regidx 11) (regidx.Regidx 12)
        (katState squareA squareA) s' ∧
      ∀ i, i < 4 → loadDword? s' (katOut + BitVec.ofNat 64 (8 * i)) =
        (natToLimbs 0x14551231950b75fc4402da1732fc9bebf).toList[i]? := by
  obtain ⟨ws, hws, s', run, -, can⟩ := secp256k1Squarer_rows_jolt_advice_complete
    (kat_pre .square squareA squareA) (by rw [kat_x10]; exact kat_limbs_a _ _) (by decide)
  have hadv : joltAdvice .squarer squareA squareA = some (quotientWords (natToLimbs 1)) := by
    decide
  rw [hadv] at hws
  cases Option.some.inj hws
  have spec :=
    secp256k1Squarer_rows_sound (kat_pre .square squareA squareA).toFieldMulBuffer run
  refine ⟨hadv, s', run, spec, fun i hi => ?_⟩
  rw [kat_result (fun _ => rfl) spec can i hi]
  rfl

end JoltTests.Secp256k1FieldMulInstance
