import JoltConstraints.theorems.Soundness.UntrustedAdvice.ShiftWitness
import JoltConstraints.theorems.untrusted_advice_block

open LeanRV64D

/-! Turning committed untrusted-advice words into advice bytes.
Each committed word that is the cast of a 64-bit word keeps that word, and every other
committed word becomes zero. The tracer receives the little-endian bytes of these words,
one per byte of the untrusted-advice block.
No row selects a committed word outside the 64-bit range (`ShiftWitness.lean`), so
shifting the RAM table by the difference keeps every constraint, and the byte relation
holds for the shifted witness.
Jolt at `ff6fc6568`: `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_advice_block`) and `common/src/jolt_device.rs`
(`JoltDevice::try_with_io`). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

open TraceWitness

open Classical in
/-- The 64-bit word stored at untrusted-advice index `index`: the committed word if it is
the cast of a 64-bit word, and zero otherwise.
For example, in a field of characteristic above `2 ^ 64`, if `untrustedAdvice 3` is the
cast of `0x0102`, then `adviceWord untrustedAdvice 3 = 0x0102`, and if `untrustedAdvice 3`
is `2 ^ 64`, then `adviceWord untrustedAdvice 3 = 0`. -/
noncomputable def adviceWord {F : Type} [Field F] (untrustedAdvice : Nat → F) (index : Nat) :
    BitVec 64 :=
  if word : IsWord (untrustedAdvice index) then word.choose else 0

/-- A committed word in the 64-bit range is the cast of its `adviceWord`.
For example, the committed word `5` gives `adviceWord = 5`. -/
theorem adviceWord_spec {F : Type} [Field F] (untrustedAdvice : Nat → F) (index : Nat)
    (word : IsWord (untrustedAdvice index)) :
    untrustedAdvice index = ((adviceWord untrustedAdvice index).toNat : F) := by
  unfold adviceWord
  rw [dite_eq_left word]
  exact word.choose_spec

/-- The first `size` little-endian bytes of the word sequence `words`. Byte `k` is byte
`k % 8` of word `k / 8`.
For example, `wordBytes (fun _ => 0x0102) 3` is `#[0x02, 0x01, 0x00]`. -/
def wordBytes (words : Nat → BitVec 64) (size : Nat) : Array (BitVec 8) :=
  Array.ofFn (n := size) fun k => (words (k.val / 8)).extractLsb' (8 * (k.val % 8)) 8

/-- `wordBytes words size` has `size` bytes.
For example, `wordBytes words 12` has 12 bytes, a whole word and half of the next. -/
theorem wordBytes_size (words : Nat → BitVec 64) (size : Nat) :
    (wordBytes words size).size = size := by
  simp [wordBytes]

/-- A whole word of `wordBytes` packs back to the word.
For example, bytes 8 through 15 of `wordBytes words 16` pack back to `words 1`. -/
theorem ramImageWord_wordBytes (words : Nat → BitVec 64) (size index : Nat)
    (fits : 8 * index + 8 ≤ size) :
    ramImageWord (fun k => (wordBytes words size)[k]?.getD 0) (8 * index) = words index := by
  apply ramImageWord_of_bytes
  intro offset offsetLt
  have inRange : 8 * index + offset < size := by omega
  have quotient : (8 * index + offset) / 8 = index := by omega
  have remainder : (8 * index + offset) % 8 = offset := by omega
  simp [wordBytes, inRange, quotient, remainder]

variable {F : Type} [Field F]

/-- The relation Jolt's verifier checks reduces to the byte relation.
Each committed advice word that is the cast of a 64-bit word becomes that word, and every
other one becomes zero. The tracer receives the little-endian bytes of these words, one
per byte of the untrusted-advice block, and the witness's RAM table is shifted by the
difference (`shiftRam`). No row selects a word that changes, and the public I/O mask is
zero on the block.
No premise on the block size is needed: the checked layout makes the capacity a multiple
of 8, and initialization admits exactly that many bytes.
For example, in a field of characteristic above `2 ^ 64`, a 16-byte block with committed
words `0x0102` and `2 ^ 64` gives the advice bytes `0x02, 0x01` followed by fourteen zero
bytes. -/
theorem allConstraintsOnBytes_of_allConstraints (joltField : JoltField F)
    {params : WitnessParams} {joltInstance : JoltInstance SourceInstruction}
    (untrustedAdvice : Nat → F) {witness : WitnessType F params}
    (satisfied : AllConstraints joltInstance untrustedAdvice witness) :
    ∃ (privateInputs : JoltPrivateInputs) (witness' : WitnessType F params),
      AllConstraintsOnBytes joltInstance privateInputs witness' := by
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨empty, builtEmpty, ramIs⟩ := context.initialized
  have layoutIs := initial_state_memory_layout context builtEmpty
  obtain ⟨layout, layoutSome, code, trustedFits, -, inputsFit⟩ :=
    (initial_state_isSome_iff joltInstance _).mp (Option.isSome_iff_exists.mpr ⟨empty, builtEmpty⟩)
  have layoutBuilt : joltInstance.memory_layout = some context.io.memory_layout := by
    rw [← layoutIs]
    exact (initial_state_device joltInstance _ empty builtEmpty).1
  obtain rfl : context.io.memory_layout = layout :=
    Option.some.inj (layoutBuilt.symm.trans layoutSome)
  have configBuilt := layoutBuilt
  unfold JoltInstance.memory_layout at configBuilt
  -- the advice bytes and the run that starts from them
  let bytes := wordBytes (adviceWord untrustedAdvice)
    context.io.memory_layout.max_untrusted_advice_size.toNat
  obtain ⟨withBytes, builtBytes⟩ := Option.isSome_iff_exists.mp
    ((initial_state_isSome_iff joltInstance { untrusted_advice := bytes, advice_tape := #[] }).mpr
      ⟨_, layoutBuilt, code, trustedFits, by simp [bytes, wordBytes_size], inputsFit⟩)
  -- the two initial RAMs agree outside the block and on in-range words inside it
  have outside : ∀ address, untrustedAdviceWordIndex? context.io.memory_layout address = none →
      initialRamWordFromState withBytes address = context.initialRam address := by
    intro address indexIs
    rw [← layoutIs] at indexIs
    rw [ramIs]
    exact initialRamWord_outside_untrusted joltInstance #[] bytes empty withBytes builtEmpty
      builtBytes indexIs
  have inside : ∀ address index,
      untrustedAdviceWordIndex? context.io.memory_layout address = some index →
      initialRamWordFromState withBytes address = adviceWord untrustedAdvice index := by
    intro address index indexIs
    have inBlock := indexIs
    rw [untrustedAdviceWordIndex?_eq _ _ configBuilt] at inBlock
    dsimp only at inBlock
    split_ifs at inBlock with bounds
    have indexEq := Option.some.inj inBlock
    obtain ⟨-, -, -, -, sizeAligned, -, -, -⟩ := untrustedBlock_geometry _ _ configBuilt
    have fits : 8 * index + 8 ≤ context.io.memory_layout.max_untrusted_advice_size.toNat := by
      omega
    rw [← layoutIs] at indexIs
    have bytesFit : 8 * index + 8 ≤ bytes.size := by
      rw [wordBytes_size]
      exact fits
    rw [initialRamWord_inside_untrusted joltInstance #[] bytes empty withBytes builtEmpty
      builtBytes indexIs bytesFit]
    exact ramImageWord_wordBytes (adviceWord untrustedAdvice)
      context.io.memory_layout.max_untrusted_advice_size.toNat index fits
  -- the gap between the committed and the byte initial values
  obtain ⟨gap, gapIs⟩ : ∃ gap : Nat → F, ∀ address, gap address =
      committedInitialValue context.io.memory_layout context.initialRam untrustedAdvice address -
        ramInitialValue (initialRamWordFromState withBytes) address := ⟨_, fun _ => rfl⟩
  have gapOutside : ∀ address,
      untrustedAdviceWordIndex? context.io.memory_layout address = none → gap address = 0 := by
    intro address indexIs
    rw [gapIs]
    unfold committedInitialValue
    rw [indexIs]
    dsimp only
    unfold ramInitialValue
    rw [outside address indexIs, sub_self]
  have unselected : ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
      witness.RamRa address t * gap address.val = 0 := by
    intro address t
    rcases ramRa_zero_or_one context equations address t with zero | one
    · rw [zero, zero_mul]
    · rw [one, one_mul]
      cases indexIs : untrustedAdviceWordIndex? context.io.memory_layout address.val with
      | none => exact gapOutside address.val indexIs
      | some index =>
        have word := initialValue_word_of_selected joltField context equations address
          (writeProtectedMask_of_untrustedAdvice _ _ configBuilt context.bytecode indexIs) t one
        unfold committedInitialValue at word
        rw [indexIs] at word
        rw [gapIs]
        unfold committedInitialValue ramInitialValue
        rw [indexIs]
        dsimp only
        rw [inside address.val index indexIs, ← adviceWord_spec untrustedAdvice index word,
          sub_self]
  have nonPublic : ∀ address : Fin params.ramSize,
      ramPublicIoMask (F := F) context.io address.val * gap address.val = 0 := by
    intro address
    cases indexIs : untrustedAdviceWordIndex? context.io.memory_layout address.val with
    | none => rw [gapOutside address.val indexIs, mul_zero]
    | some index =>
      rw [publicIoMask_of_untrustedAdvice _ context.io configBuilt indexIs, zero_mul]
  have shifted := shiftRam_equations gap equations unselected nonPublic
  have initialIs : (fun address =>
      committedInitialValue context.io.memory_layout context.initialRam untrustedAdvice address -
        gap address) = ramInitialValue (initialRamWordFromState withBytes) := by
    funext address
    rw [gapIs]
    ring
  rw [initialIs] at shifted
  exact ⟨_, _, { context with
    initialRam := initialRamWordFromState withBytes
    initialized := ⟨withBytes, builtBytes, rfl⟩ }, shifted⟩

end JoltConstraints.Soundness.UntrustedAdvice
