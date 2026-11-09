import JoltBytecode.Decode.Agreement

/-!
Agreement of Jolt’s compressed expander at `b65455e6d` with Sail’s RV64IMAC decoder.
Cases follow `crates/jolt-riscv/src/uncompress.rs` (`uncompress_rv64_instruction`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

namespace Decode

/-- A concatenation is zero only when both halves are; for example, `0#1 ++ 0#5 = 0`. -/
private theorem append_eq_zero_aux {m n : Nat} (x : BitVec m) (y : BitVec n) (hz : x ++ y = 0) :
    x = 0 ∧ y = 0 := by
  have h : (x ++ y).toNat = 0 := by simp [hz]
  rw [BitVec.toNat_append, Nat.or_eq_zero_iff] at h
  have hx : x.toNat <<< n = 0 → x.toNat = 0 := by
    intro h0
    rw [Nat.shiftLeft_eq] at h0
    have : 0 < 2 ^ n := Nat.two_pow_pos n
    exact (Nat.mul_eq_zero.mp h0).resolve_right (by omega)
  exact ⟨BitVec.eq_of_toNat_eq (hx h.1), BitVec.eq_of_toNat_eq h.2⟩

/-- The six immediate bits of a parcel are clear when their concatenation is zero;
for example, C.ADDI x1,0 has bit 12 and bits 6:2 clear. -/
private theorem compressed_zero_bits (h : BitVec 16)
    (hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) :
    h.getLsbD 12 = false ∧ h.getLsbD 2 = false ∧ h.getLsbD 3 = false ∧
      h.getLsbD 4 = false ∧ h.getLsbD 5 = false ∧ h.getLsbD 6 = false := by
  obtain ⟨a, b⟩ := append_eq_zero_aux _ _ hz
  have h12 : h.getLsbD 12 = false := by
    have := congrArg (fun x : BitVec 1 => x.getLsbD 0) a
    simpa [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb] using this
  have hb : ∀ i, i < 5 → h.getLsbD (2 + i) = false := by
    intro i hi
    have hi' : i ≤ 4 := by omega
    have := congrArg (fun x : BitVec 5 => x.getLsbD i) b
    simpa [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb, hi, hi'] using this
  exact ⟨h12, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega)⟩

/-- Selector fields of a parcel whose immediate bits are zero; for example, C.ADD's bit 12 is
clear and its bits 6:5 are clear. -/
private theorem compressed_zero_fields (h : BitVec 16)
    (hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) :
    (h.setWidth 32 >>> 12 &&& 1).toNat = 0 ∧ (h.setWidth 32 >>> 5 &&& 3).toNat = 0 := by
  obtain ⟨h12, h2, h3, h4, h5, h6⟩ := compressed_zero_bits h hz
  constructor
  · have e : (h.setWidth 32 >>> 12 &&& 1) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      interval_cases i <;>
      simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit, h12]
    rw [e]; rfl
  · have e : (h.setWidth 32 >>> 5 &&& 3) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      interval_cases i <;>
      simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit, h5, h6]
    rw [e]; rfl

/-- A parcel's six immediate bits are zero exactly when each is clear. -/
private theorem compressed_zero_iff_bits (h : BitVec 16) :
    (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) ↔
      (h.getLsbD 12 = false ∧ h.getLsbD 2 = false ∧ h.getLsbD 3 = false ∧
        h.getLsbD 4 = false ∧ h.getLsbD 5 = false ∧ h.getLsbD 6 = false) := by
  constructor
  · exact compressed_zero_bits h
  · rintro ⟨h12, h2, h3, h4, h5, h6⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;>
    simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, h2, h3, h4, h5, h6, h12]

/-- C.ADDI16SP's immediate guard is the same six bits in a different order, so it vanishes
exactly when the parcel's immediate bits do. -/
private theorem addi16sp_guard_iff (h : BitVec 16) :
    (BitVec.extractLsb' 12 1 h ++ BitVec.extractLsb' 3 2 h ++ BitVec.extractLsb' 5 1 h ++
        BitVec.extractLsb' 2 1 h ++ BitVec.extractLsb' 6 1 h = 0#6) ↔
      (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) := by
  rw [compressed_zero_iff_bits]
  constructor
  · intro e
    have b : ∀ i, i < 6 → (BitVec.extractLsb' 12 1 h ++ BitVec.extractLsb' 3 2 h ++ BitVec.extractLsb' 5 1 h ++
        BitVec.extractLsb' 2 1 h ++ BitVec.extractLsb' 6 1 h).getLsbD i = false := by
      intro i hi
      rw [e]; simp
    have b0 := b 0 (by omega)
    have b1 := b 1 (by omega)
    have b2 := b 2 (by omega)
    have b3 := b 3 (by omega)
    have b4 := b 4 (by omega)
    have b5 := b 5 (by omega)
    simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] at b0 b1 b2 b3 b4 b5
    exact ⟨b5, b1, b3, b4, b2, b0⟩
  · rintro ⟨h12, h2, h3, h4, h5, h6⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;>
    simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', h2, h3, h4, h5, h6, h12]

private theorem addi16sp_guard_nonzero (h : BitVec 16)
    (hz : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)) :
    ¬ (BitVec.extractLsb' 12 1 h ++ BitVec.extractLsb' 3 2 h ++ BitVec.extractLsb' 5 1 h ++
        BitVec.extractLsb' 2 1 h ++ BitVec.extractLsb' 6 1 h = 0#6) :=
  fun e => hz ((addi16sp_guard_iff h).1 e)

private theorem addi16sp_guard_zero (h : BitVec 16)
    (hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) :
    BitVec.extractLsb' 12 1 h ++ BitVec.extractLsb' 3 2 h ++ BitVec.extractLsb' 5 1 h ++
        BitVec.extractLsb' 2 1 h ++ BitVec.extractLsb' 6 1 h = 0#6 :=
  (addi16sp_guard_iff h).2 hz

/-- Clear selector fields give a zero immediate; for example, C.JR has bit 12 and bits 6:2 clear. -/
private theorem compressed_zero_of_fields (h : BitVec 16)
    (ha : (h.setWidth 32 >>> 12 &&& 1).toNat = 0)
    (hb : (h.setWidth 32 >>> 2 &&& 31) = 0) :
    h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0 := by
  rw [compressed_zero_iff_bits]
  have bit : ∀ i, i < 5 → h.getLsbD (2 + i) = false := by
    intro i hi
    have := congrArg (fun x : BitVec 32 => x.getLsbD i) hb
    interval_cases i <;>
    simpa [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit] using this
  have h12 : h.getLsbD 12 = false := by
    have := congrArg (fun x : BitVec 32 => x.getLsbD 0) (BitVec.eq_of_toNat_eq (x := h.setWidth 32 >>> 12 &&& 1) (y := 0#32) (by rw [ha]; rfl))
    simpa [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth] using this
  exact ⟨h12, bit 0 (by omega), bit 1 (by omega), bit 2 (by omega), bit 3 (by omega), bit 4 (by omega)⟩

/-- A zero signed immediate forces the six source bits to be zero; for example, C.ADDI x1,0. -/
private theorem compressed_zero_of_ci (h : BitVec 16)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0) :
    h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0 := by
  rw [compressed_zero_iff_bits]
  have at_bit : ∀ i, i < 6 → (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)).getLsbD i = false := by
    intro i hi'
    rw [hi]; simp
  have lo : ∀ i, i < 6 → (signBitMask (h.setWidth 32) 0x1000 0xffffffc0).getLsbD i = false := by
    intro i hi'
    unfold signBitMask
    split
    · interval_cases i <;> simp [BitVec.getLsbD_ofNat, Nat.testBit]
    · simp
  have b0 := at_bit 0 (by omega)
  have b1 := at_bit 1 (by omega)
  have b2 := at_bit 2 (by omega)
  have b3 := at_bit 3 (by omega)
  have b4 := at_bit 4 (by omega)
  have b5 := at_bit 5 (by omega)
  have l0 := lo 0 (by omega)
  have l1 := lo 1 (by omega)
  have l2 := lo 2 (by omega)
  have l3 := lo 3 (by omega)
  have l4 := lo 4 (by omega)
  have l5 := lo 5 (by omega)
  simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit, l0, l1, l2, l3, l4, l5] at b0 b1 b2 b3 b4 b5
  exact ⟨b5.2, b0.2, b1.2, b2.2, b3.2, b4.2⟩

/-- The signed compressed immediates are zero when their six source bits are zero;
for example, C.ADDI x1,0 has this property. -/
private theorem compressed_immediates_zero (h : BitVec 16)
    (hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) :
    (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0 ∧
    (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) = 0 ∧
    (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) = 0 ∧
    ((h.setWidth 32 >>> 2) &&& 31) = 0 := by
  obtain ⟨h12, h2, h3, h4, h5, h6⟩ := compressed_zero_bits h hz
  have hm : h.setWidth 32 &&& 0x1000 ≠ 0x1000 := by
    intro he
    have := congrArg (fun x : BitVec 32 => x.getLsbD 12) he
    simp [-BitVec.getLsbD_eq_getElem, h12] at this
  simp only [signBitMask, hm, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;>
    simp [-BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
      Nat.testBit, h2, h3, h4, h5, h6, h12]

macro "uncompress_fields" : tactic => `(tactic|
  simp only [joltUncompress, *, ne_eq, not_false_eq_true, not_true_eq_false,
    true_or, or_true, false_or, or_false, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceBEq, Nat.reduceLT, ↓reduceIte])

macro "compare_compressed_fields" : tactic => `(tactic|
  (try have $(Lean.mkIdent `addi16sp_guard) :=
     addi16sp_guard_nonzero $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
   compressed_prepare
   decoder_pair
   · decode16_case
   · uncompress_fields
     decode_word_case
   · intro $(Lean.mkIdent `s') $(Lean.mkIdent `hinv')
     compressed_execution))

/-- Like `compare_compressed_fields`, for a parcel whose immediate bits are zero. The zero facts
about the expanded immediates join the context only where they are needed, because large
hypotheses slow down the decoder guards. -/
macro "compare_compressed_fields_zero" : tactic => `(tactic|
  (have $(Lean.mkIdent `addi16sp_guard) :=
     addi16sp_guard_zero $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
   compressed_prepare
   decoder_pair
   · decode16_case
   · obtain ⟨$(Lean.mkIdent `ci_zero), $(Lean.mkIdent `sp_zero),
         $(Lean.mkIdent `upper_zero), -⟩ :=
       compressed_immediates_zero $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
     uncompress_fields
     decode_word_case
   · intro $(Lean.mkIdent `s') $(Lean.mkIdent `hinv')
     obtain ⟨$(Lean.mkIdent `zbit12), $(Lean.mkIdent `zbit2), $(Lean.mkIdent `zbit3),
         $(Lean.mkIdent `zbit4), $(Lean.mkIdent `zbit5), $(Lean.mkIdent `zbit6)⟩ :=
       compressed_zero_bits $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
     compressed_execution))

/-- The case where the parcel's immediate bits are zero: either the selectors contradict this, or
the decoders agree on the zero-immediate form. -/
macro "compare_compressed_pos" : tactic => `(tactic|
  first
  | (obtain ⟨$(Lean.mkIdent `ci_zero), $(Lean.mkIdent `sp_zero),
        $(Lean.mkIdent `upper_zero), $(Lean.mkIdent `rs2_zero)⟩ :=
       compressed_immediates_zero $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
     contradiction)
  | (obtain ⟨$(Lean.mkIdent `zfield12), $(Lean.mkIdent `zfield56)⟩ :=
       compressed_zero_fields $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
     omega)
  | compare_compressed_fields_zero)

/-- The case where the parcel's immediate bits are not all zero: either the selectors force them to
be zero, or the decoders agree on the general form. -/
macro "compare_compressed_neg" : tactic => `(tactic|
  first
  | exact absurd (compressed_zero_of_fields $(Lean.mkIdent `h) $(Lean.mkIdent `ha)
      $(Lean.mkIdent `hb)) $(Lean.mkIdent `compressed_zero)
  | exact absurd (compressed_zero_of_ci $(Lean.mkIdent `h) $(Lean.mkIdent `hi))
      $(Lean.mkIdent `compressed_zero)
  | compare_compressed_fields)

/-- Decide the parcel's zero immediate bits first; every quadrant-one and quadrant-two decoder arm
checks them before its selectors, so a direct proof attempt would only fail. -/
macro "compare_compressed_split" : tactic => `(tactic|
  (by_cases $(Lean.mkIdent `compressed_zero) :
      ($(Lean.mkIdent `h)).extractLsb 12 12 ++ ($(Lean.mkIdent `h)).extractLsb 6 2 = 0
   · compare_compressed_pos
   · compare_compressed_neg))

macro "compare_compressed_case" : tactic => `(tactic|
  first | solve | compare_compressed_fields | compare_compressed_split)

private theorem compare_addi4spn (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hu : (((h.setWidth 32 >>> 7) &&& 0x30) ||| ((h.setWidth 32 >>> 1) &&& 0x3c0) ||| ((h.setWidth 32 >>> 4) &&& 4) ||| ((h.setWidth 32 >>> 2) &&& 8)) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_lw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_ld (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_sw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_sd (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_addi (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_addiw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 1)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_li (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_addi16sp_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 2)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_addi16sp_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 2)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_addi16sp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 2)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_addi16sp_zero <;> assumption
  · apply compare_addi16sp_nonzero <;> assumption

private theorem compare_lui_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr2 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 2)
    (hr0 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_lui_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr2 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 2)
    (hr0 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_lui (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr2 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 2)
    (hr0 : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_lui_zero <;> assumption
  · apply compare_lui_nonzero <;> assumption

private theorem compare_srli_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_srli_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_srli (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_srli_zero <;> assumption
  · apply compare_srli_nonzero <;> assumption

private theorem compare_srai_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 1)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_srai_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 1)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_srai (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 1)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_srai_zero <;> assumption
  · apply compare_srai_nonzero <;> assumption

private theorem compare_andi_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 2)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_andi_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 2)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_andi (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 2)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_andi_zero <;> assumption
  · apply compare_andi_nonzero <;> assumption

private theorem compare_sub_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_sub_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_sub (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_sub_zero <;> assumption
  · apply compare_sub_nonzero <;> assumption

private theorem compare_xor_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_xor_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_xor (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_xor_zero <;> assumption
  · apply compare_xor_nonzero <;> assumption

private theorem compare_or_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 2)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_or_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 2)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_or (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 2)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_or_zero <;> assumption
  · apply compare_or_nonzero <;> assumption

private theorem compare_and_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 3)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_and_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 3)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_and (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 3)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_and_zero <;> assumption
  · apply compare_and_nonzero <;> assumption

private theorem compare_subw_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_subw_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_subw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_subw_zero <;> assumption
  · apply compare_subw_nonzero <;> assumption

private theorem compare_addw_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_addw_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_addw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 3)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 5) &&& 3).toNat = 1)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_addw_zero <;> assumption
  · apply compare_addw_nonzero <;> assumption

private theorem compare_j (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 5)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_beqz_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_beqz_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_beqz (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_beqz_zero <;> assumption
  · apply compare_beqz_nonzero <;> assumption

private theorem compare_bnez_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_bnez_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_bnez (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_bnez_zero <;> assumption
  · apply compare_bnez_nonzero <;> assumption

private theorem compare_slli (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_lwsp_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_lwsp_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_lwsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_lwsp_zero <;> assumption
  · apply compare_lwsp_nonzero <;> assumption

private theorem compare_ldsp_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_ldsp_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_ldsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_ldsp_zero <;> assumption
  · apply compare_ldsp_nonzero <;> assumption

private theorem compare_jr_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_jr_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_jr (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_jr_zero <;> assumption
  · apply compare_jr_nonzero <;> assumption

private theorem compare_mv (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_ebreak_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_ebreak_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_ebreak (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_ebreak_zero <;> assumption
  · apply compare_ebreak_nonzero <;> assumption

private theorem compare_jalr_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_jalr_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_jalr (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_jalr_zero <;> assumption
  · apply compare_jalr_nonzero <;> assumption

private theorem compare_add_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_add_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_add (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_add_zero <;> assumption
  · apply compare_add_nonzero <;> assumption

private theorem compare_swsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_sdsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_nop (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_addi_zero_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_addi_zero_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_addi_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_addi_zero_zero <;> assumption
  · apply compare_addi_zero_nonzero <;> assumption

private theorem compare_li_hint_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_li_hint_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_li_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_li_hint_zero <;> assumption
  · apply compare_li_hint_nonzero <;> assumption

private theorem compare_lui_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (hi : h.extractLsb 12 12 ++ h.extractLsb 6 2 ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_mv_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 0)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_split

private theorem compare_add_hint_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_pos

private theorem compare_add_hint_nonzero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (compressed_zero : ¬ (h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0))
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_neg

private theorem compare_add_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (ha : ((h.setWidth 32 >>> 12) &&& 1).toNat = 1)
    (hb : ((h.setWidth 32 >>> 2) &&& 31) ≠ 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases compressed_zero : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0
  · apply compare_add_hint_zero <;> assumption
  · apply compare_add_hint_nonzero <;> assumption


macro "finish_compressed_case" : tactic => `(tactic|
  first
  | solve | apply (compare_addi4spn $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_lw $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_ld $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_sw $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_sd $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_addi $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_addiw $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_li $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_addi16sp $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_lui $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_srli $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_srai $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_andi $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_sub $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_xor $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_or $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_and $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_subw $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_addw $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_j $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_beqz $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_bnez $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_slli $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_lwsp $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_ldsp $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_jr $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_mv $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_ebreak $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_jalr $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_add $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_swsp $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_sdsp $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_nop $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_addi_zero $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_li_hint $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_lui_hint $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_mv_hint $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
  | solve | apply (compare_add_hint $(Lean.mkIdent `h) (s := $(Lean.mkIdent `s))
      (hinv := $(Lean.mkIdent `hinv))) <;> assumption
)

/-- The reserved parcels accepted by Jolt form a singleton: 0x6001 is C.LUI x0,0. -/
theorem reservedAccepted_iff (h : BitVec 16) : ReservedAccepted h ↔ h = 0x6001#16 := by
  unfold ReservedAccepted
  constructor
  · intro ⟨_, _, _, _, _⟩
    simp only [BitVec.toNat_eq, BitVec.extractLsb_toNat] at *
    simp at *
    omega
  · rintro rfl
    decide

private theorem rejected_opcode (w : BitVec 32) (advice : BitVec 64)
    (hop : (w.extractLsb 6 0).toNat = 7 ∨ (w.extractLsb 6 0).toNat = 39 ∨
      (w.extractLsb 6 0).toNat = 127) : joltDecode w advice = none := by
  rcases hop with h | h | h <;> simp [joltDecode, h]

private theorem compare_alu (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have hk_bound : ((h.setWidth 32 >>> 10) &&& 3).toNat < 4 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases hk : ((h.setWidth 32 >>> 10) &&& 3).toNat
  · finish_compressed_case
  · finish_compressed_case
  · finish_compressed_case
  · have ha_bound : ((h.setWidth 32 >>> 12) &&& 1).toNat < 2 :=
    Nat.lt_succ_of_le Nat.and_le_right
    have hb_bound : ((h.setWidth 32 >>> 5) &&& 3).toNat < 4 :=
      Nat.lt_succ_of_le Nat.and_le_right
    interval_cases ha : ((h.setWidth 32 >>> 12) &&& 1).toNat <;>
      interval_cases hb : ((h.setWidth 32 >>> 5) &&& 3).toNat
    all_goals first
      | finish_compressed_case
      | simp only [joltUncompress, hop, hf, hk, ha, hb, ne_eq, Nat.reduceLT, Nat.reduceEqDiff,
          ↓reduceIte, false_or, or_false, not_true_eq_false] at hn

private theorem compare_control (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have ha_bound : ((h.setWidth 32 >>> 12) &&& 1).toNat < 2 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases ha : ((h.setWidth 32 >>> 12) &&& 1).toNat <;>
    by_cases hb : ((h.setWidth 32 >>> 2) &&& 31) = 0 <;>
    by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
  all_goals first
    | finish_compressed_case
    | simp only [joltUncompress, hop, hf, ha, hb, hr, ne_eq,
        ↓reduceIte, not_false_eq_true, not_true_eq_false] at hn

/-- A quadrant-one parcel with funct3 three and register field zero is not reserved only if
its immediate bits are nonzero; for example, 0x6005 is C.LUI x0 with nonzero immediate. -/
private theorem compressed_upper_nonzero (h : BitVec 16)
    (hq : (h.setWidth 32 &&& 3) = 1#32) (hf : ((h.setWidth 32 >>> 13) &&& 7) = 3#32)
    (hres : ¬ ReservedAccepted h) (hr0 : ((h.setWidth 32 >>> 7) &&& 31) = 0) :
    h.extractLsb 12 12 ++ h.extractLsb 6 2 ≠ 0 := by
  intro hz
  obtain ⟨a, b⟩ := append_eq_zero_aux _ _ hz
  apply hres
  unfold ReservedAccepted
  decoder_omega

private theorem compare_upper (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hres : ¬ ReservedAccepted h) (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  by_cases hr2 : ((h.setWidth 32 >>> 7) &&& 31) = 2
  · by_cases hz : (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) = 0
    · simp only [joltUncompress, hop, hf, hr2, hz, ne_eq,
        ↓reduceIte, not_false_eq_true, not_true_eq_false] at hn
    · finish_compressed_case
  · by_cases hr0 : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · have hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 ≠ 0 := by
        have hq : (h.setWidth 32 &&& 3) = 1#32 := BitVec.eq_of_toNat_eq hop
        have hf' : ((h.setWidth 32 >>> 13) &&& 7) = 3#32 := BitVec.eq_of_toNat_eq hf
        exact compressed_upper_nonzero h hq hf' hres hr0
      finish_compressed_case
    · by_cases hz : (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) = 0
      · simp only [joltUncompress, hop, hf, hr2, hr0, hz, ne_eq,
          ↓reduceIte, not_false_eq_true, not_true_eq_false] at hn
      · finish_compressed_case

private theorem accepted_opcode (w : BitVec 32) (advice : BitVec 64)
    (i : RiscvInstruction) (hi : joltDecode w advice = some i) :
    ¬ ((w.extractLsb 6 0).toNat = 7 ∨ (w.extractLsb 6 0).toNat = 39 ∨
      (w.extractLsb 6 0).toNat = 127) := by
  intro hop
  rw [rejected_opcode w advice hop] at hi
  contradiction

macro "reject_compressed_case" : tactic => `(tactic|
  (compressed_prepare
   exfalso
   apply accepted_opcode _ _ _ $(Lean.mkIdent `hi)
   simp only [BitVec.toNat_eq_nat, Nat.reducePow, Nat.reduceLT, true_and]
   uncompress_fields
   decoder_bits))

private theorem compare_quadrant0 (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 0)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have hf_bound : ((h.setWidth 32 >>> 13) &&& 7).toNat < 8 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases hf : ((h.setWidth 32 >>> 13) &&& 7).toNat
  · by_cases hu : (((h.setWidth 32 >>> 7) &&& 0x30) ||| ((h.setWidth 32 >>> 1) &&& 0x3c0) ||| ((h.setWidth 32 >>> 4) &&& 4) ||| ((h.setWidth 32 >>> 2) &&& 8)) = 0
    · exfalso
      apply hn
      simp only [joltUncompress, hop, hf, hu, ne_eq, not_true_eq_false, ↓reduceIte]
    · finish_compressed_case
  · reject_compressed_case
  · finish_compressed_case
  · finish_compressed_case
  · exfalso
    apply hn
    simp only [joltUncompress, hop, hf]
  · reject_compressed_case
  · finish_compressed_case
  · finish_compressed_case

private theorem compare_quadrant1 (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hres : ¬ ReservedAccepted h) (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have hf_bound : ((h.setWidth 32 >>> 13) &&& 7).toNat < 8 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases hf : ((h.setWidth 32 >>> 13) &&& 7).toNat
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · finish_compressed_case
    · by_cases hz : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0
      · finish_compressed_case
      · finish_compressed_case
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · exfalso
      apply hn
      simp only [joltUncompress, hop, hf, hr, ne_eq, not_true_eq_false, ↓reduceIte]
    · finish_compressed_case
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · finish_compressed_case
    · finish_compressed_case
  · exact compare_upper h hop hf hres hn s hinv
  · exact compare_alu h hop hf hn s hinv
  · finish_compressed_case
  · finish_compressed_case
  · finish_compressed_case

private theorem compare_quadrant2 (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (hn : joltUncompress h ≠ 0xffffffff)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have hf_bound : ((h.setWidth 32 >>> 13) &&& 7).toNat < 8 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases hf : ((h.setWidth 32 >>> 13) &&& 7).toNat
  · finish_compressed_case
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · exfalso
      apply hn
      simp only [joltUncompress, hop, hf, hr, ne_eq, not_true_eq_false, ↓reduceIte]
    · reject_compressed_case
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · exfalso
      apply hn
      simp only [joltUncompress, hop, hf, hr, ne_eq, not_true_eq_false, ↓reduceIte]
    · finish_compressed_case
  · by_cases hr : ((h.setWidth 32 >>> 7) &&& 31) = 0
    · exfalso
      apply hn
      simp only [joltUncompress, hop, hf, hr, ne_eq, not_true_eq_false, ↓reduceIte]
    · finish_compressed_case
  · exact compare_control h hop hf hn s hinv
  · reject_compressed_case
  · finish_compressed_case
  · finish_compressed_case

private theorem compare_accepted (h : BitVec 16)
    (hc : h.extractLsb 1 0 ≠ 0b11#2) (hres : ¬ ReservedAccepted h)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  have hn : joltUncompress h ≠ 0xffffffff := by
    intro he
    rw [he] at hi
    change none = some i at hi
    contradiction
  have hq_bound : (h.setWidth 32 &&& 3).toNat < 4 :=
    Nat.lt_succ_of_le Nat.and_le_right
  interval_cases hq : (h.setWidth 32 &&& 3).toNat
  · exact compare_quadrant0 h hq advice i hi hn s hinv
  · exact compare_quadrant1 h hq hres hn s hinv
  · exact compare_quadrant2 h hq advice i hi hn s hinv
  · exfalso
    apply hn
    simp only [joltUncompress, hq]

/-- Every compressed parcel accepted by Jolt at `b65455e6d`, except reserved 0x6001,
has a Sail compressed AST executing like a matching base AST under the step invariant and reset misa;
for example, C.MV agrees with Jolt's ADD expansion. -/
theorem joltDecode_compressed_agrees (h : BitVec 16) (hc : h.extractLsb 1 0 ≠ 0b11#2)
    (hres : ¬ ReservedAccepted h)
    (advice : BitVec 64) (i : RiscvInstruction)
    (hi : joltDecode (joltUncompress h) advice = some i)
    (s : SailState) (hinv : _root_.Step.StepInvariant s)
    (hreset : s.regs.get? Register.misa = some resetMisa) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧ _root_.Step.Matches i base ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  obtain ⟨cast, base, hcdec, hbdec, he⟩ := compare_accepted h hc hres advice i hi s hinv
  obtain ⟨ast, hast, hm⟩ := joltDecode_agrees (joltUncompress h) advice i hi s hinv hreset
  have hab : base = ast := by simpa only [hbdec, EStateM.Result.ok.injEq, and_true] using hast
  subst ast
  exact ⟨cast, base, hcdec, hm, he⟩

end Decode
