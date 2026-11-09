import JoltBytecode.Decode.Agreement

/-!
Agreement of Jolt’s compressed expander at `b65455e6d` with Sail’s RV64IMAC decoder.
Cases follow `crates/jolt-riscv/src/uncompress.rs` (`uncompress_rv64_instruction`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

namespace Decode

/-- The signed compressed immediates are zero when their six source bits are zero;
for example, C.ADDI x1,0 has this property. -/
private theorem compressed_immediates_zero (h : BitVec 16)
    (hz : h.extractLsb 12 12 ++ h.extractLsb 6 2 = 0) :
    (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0 ∧
    (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) = 0 ∧
    (signBitMask (h.setWidth 32) 0x1000 0xfffc0000 ||| ((h.setWidth 32 <<< 5) &&& 0x20000) ||| ((h.setWidth 32 <<< 10) &&& 0x1f000)) = 0 ∧
    ((h.setWidth 32 >>> 2) &&& 31) = 0 := by
  simp only [signBitMask]
  bv_decide

macro "uncompress_fields" : tactic => `(tactic|
  simp only [joltUncompress, *, ne_eq, not_false_eq_true, not_true_eq_false,
    true_or, or_true, false_or, or_false, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceBEq, Nat.reduceLT, ↓reduceIte])

macro "compare_compressed_fields" : tactic => `(tactic|
  (compressed_prepare
   decoder_pair
   · decode16_case
   · uncompress_fields
     decode_word_case
   · intro $(Lean.mkIdent `s') $(Lean.mkIdent `hinv')
     compressed_execution))

macro "compare_compressed_case" : tactic => `(tactic|
  first
  | solve | compare_compressed_fields
  | (by_cases $(Lean.mkIdent `compressed_zero) :
        ($(Lean.mkIdent `h)).extractLsb 12 12 ++ ($(Lean.mkIdent `h)).extractLsb 6 2 = 0
     · obtain ⟨$(Lean.mkIdent `ci_zero), $(Lean.mkIdent `sp_zero),
           $(Lean.mkIdent `upper_zero), $(Lean.mkIdent `rs2_zero)⟩ :=
         compressed_immediates_zero $(Lean.mkIdent `h) $(Lean.mkIdent `compressed_zero)
       first | contradiction | compare_compressed_fields
     · compare_compressed_fields))

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
  compare_compressed_case

private theorem compare_addiw (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 1)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_li (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_addi16sp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 2)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xfffffc00 ||| ((h.setWidth 32 >>> 3) &&& 0x200) ||| ((h.setWidth 32 >>> 2) &&& 0x10) ||| ((h.setWidth 32 <<< 1) &&& 0x40) ||| ((h.setWidth 32 <<< 4) &&& 0x180) ||| ((h.setWidth 32 <<< 3) &&& 0x20)) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

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
  compare_compressed_case

private theorem compare_srli (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_srai (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 1)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_andi (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 4)
    (hk : ((h.setWidth 32 >>> 10) &&& 3).toNat = 2)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

private theorem compare_j (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 5)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_beqz (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_bnez (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_slli (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_lwsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_ldsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case

private theorem compare_swsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 6)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_sdsp (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 2)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 7)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_nop (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_addi_zero (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 0)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) ≠ 0)
    (hi : (signBitMask (h.setWidth 32) 0x1000 0xffffffc0 ||| ((h.setWidth 32 >>> 7) &&& 0x20) ||| ((h.setWidth 32 >>> 2) &&& 0x1f)) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_li_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 2)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

private theorem compare_lui_hint (h : BitVec 16)
    (hop : (h.setWidth 32 &&& 3).toNat = 1)
    (hf : ((h.setWidth 32 >>> 13) &&& 7).toNat = 3)
    (hr : ((h.setWidth 32 >>> 7) &&& 31) = 0)
    (hi : h.extractLsb 12 12 ++ h.extractLsb 6 2 ≠ 0)
    (s : SailState) (hinv : _root_.Step.StepInvariant s) :
    ∃ cast base, ext_decode_compressed h s = .ok cast s ∧
      ext_decode (joltUncompress h) s = .ok base s ∧
      ∀ s', _root_.Step.StepInvariant s' → _root_.Step.executeFull cast s' = _root_.Step.executeFull base s' := by
  compare_compressed_case

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
  compare_compressed_case

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
  compare_compressed_case


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
  bv_decide

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
        unfold ReservedAccepted at hres
        bv_decide
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
   bv_decide))

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
