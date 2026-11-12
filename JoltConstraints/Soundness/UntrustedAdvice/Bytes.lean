import JoltConstraints.Soundness.UntrustedAdvice.ShiftWitness
import JoltConstraints.advice_inputs
import JoltConstraints.Soundness.Assumptions

open LeanRV64D

/-! Turn committed untrusted-advice words into advice bytes.
Each committed word that is the cast of a 64-bit word keeps that word, and every
other committed word becomes zero.
The bytes are the little-endian bytes of these words, one per byte of the
untrusted-advice block.
Started with these bytes, the tracer's initial RAM agrees with the committed
initial values wherever those are 64-bit words, and equals them outside the
untrusted-advice block. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

open TraceWitness

open Classical in
/-- The 64-bit word stored at untrusted-advice index `index`: the committed word if it is
the cast of a 64-bit word, and zero otherwise. For example, if `untrustedAdvice 3` is the
cast of `0x0102`, then `adviceWord untrustedAdvice 3 = 0x0102`; if `untrustedAdvice 3` is
`2 ^ 64` in a field of characteristic above `2 ^ 64`, then
`adviceWord untrustedAdvice 3 = 0`. -/
noncomputable def adviceWord {F : Type} [Field F] (untrustedAdvice : Nat → F) (index : Nat) :
    BitVec 64 :=
  if h : ∃ value : BitVec 64, untrustedAdvice index = (value.toNat : F) then h.choose else 0

/-- The first `size` little-endian bytes of the word sequence `words`. Byte `k` is byte
`k % 8` of word `k / 8`. For example, `wordBytes (fun _ => 0x0102) 3` is
`#[0x02, 0x01, 0x00]`. -/
def wordBytes (words : Nat → BitVec 64) (size : Nat) : Array (BitVec 8) :=
  Array.ofFn (n := size) fun k => (words (k.val / 8)).extractLsb' (8 * (k.val % 8)) 8

/-- The 64-bit initial RAM after the reduction: `adviceWord` in the untrusted-advice block
and `fixedRam` elsewhere. -/
noncomputable def byteInitialRam {F : Type} [Field F] (layout : MemoryLayout)
    (fixedRam : Nat → BitVec 64) (untrustedAdvice : Nat → F) (address : Nat) : BitVec 64 :=
  match untrustedAdviceWordIndex? layout address with
  | some index => adviceWord untrustedAdvice index
  | none => fixedRam address

/-- `wordBytes words size` has `size` bytes. For example, `wordBytes words 12` has 12
bytes, a whole word and half of the next. -/
theorem wordBytes_size (words : Nat → BitVec 64) (size : Nat) :
    (wordBytes words size).size = size := by
  simp [wordBytes]

/-- A whole word of `wordBytes` packs back to the word. -/
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

/-- Wherever the committed initial value is a 64-bit word, the byte initial RAM gives the
same value. -/
theorem byteInitialRam_good (layout : MemoryLayout) (fixedRam : Nat → BitVec 64)
    (untrustedAdvice : Nat → F) (address : Nat)
    (word : ∃ value : BitVec 64,
      committedInitialValue layout fixedRam untrustedAdvice address = (value.toNat : F)) :
    ramInitialValue (byteInitialRam layout fixedRam untrustedAdvice) address =
      committedInitialValue layout fixedRam untrustedAdvice address := by
  unfold committedInitialValue at word ⊢
  unfold byteInitialRam ramInitialValue
  cases indexIs : untrustedAdviceWordIndex? layout address with
  | none => simp only [indexIs]
  | some index =>
    simp only [indexIs] at word ⊢
    unfold adviceWord
    rw [dite_eq_left word]
    exact word.choose_spec.symm

/-- The untrusted-advice block lies below the public I/O mask. -/
theorem publicIoMask_of_untrustedAdvice (config : MemoryConfig) (io : JoltDevice)
    (built : MemoryLayout.new config = some io.memory_layout) {address index : Nat}
    (indexIs : untrustedAdviceWordIndex? io.memory_layout address = some index) :
    ramPublicIoMask (F := F) io address = 0 := by
  obtain ⟨_, _, _, _, _, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config io.memory_layout built
  unfold untrustedAdviceWordIndex? at indexIs
  cases firstIs : TraceWitness.remapRamAddress io.memory_layout
      io.memory_layout.untrusted_advice_start with
  | none => simp only [firstIs, reduceCtorEq] at indexIs
  | some first =>
    rw [firstIs] at indexIs
    dsimp only at indexIs
    split_ifs at indexIs with inBlock
    unfold TraceWitness.remapRamAddress at firstIs
    dsimp only at firstIs
    split_ifs at firstIs
    simp only [Option.some.injEq] at firstIs
    unfold ramPublicIoMask ramLowestAddress
    dsimp only
    rw [ite_eq_right]
    omega

/-- The public I/O mask vanishes wherever the byte initial RAM differs from the committed
initial values. -/
theorem byteInitialRam_masked (config : MemoryConfig) (io : JoltDevice)
    (built : MemoryLayout.new config = some io.memory_layout) (fixedRam : Nat → BitVec 64)
    (untrustedAdvice : Nat → F) (address : Nat) :
    ramPublicIoMask io address *
      (committedInitialValue io.memory_layout fixedRam untrustedAdvice address -
        ramInitialValue (byteInitialRam io.memory_layout fixedRam untrustedAdvice) address) =
      0 := by
  unfold committedInitialValue byteInitialRam
  cases indexIs : untrustedAdviceWordIndex? io.memory_layout address with
  | none => simp [ramInitialValue, indexIs]
  | some index =>
    rw [publicIoMask_of_untrustedAdvice config io built indexIs, zero_mul]

/-- Replacing empty untrusted advice by the bytes of the reconstructed words changes the
tracer's initial RAM exactly in the untrusted-advice block, where it becomes the
reconstructed words. -/
theorem initialRamWordFromState_untrustedAdvice (untrustedAdvice : Nat → F)
    (state state' : SailJoltState)
    (empty : state.jolt_device.untrusted_advice = #[])
    (sail : state'.sail = state.sail)
    (device : state'.jolt_device = { state.jolt_device with
      untrusted_advice := wordBytes (adviceWord untrustedAdvice)
        state.jolt_device.memory_layout.max_untrusted_advice_size.toNat })
    (aligned : state.jolt_device.memory_layout.max_untrusted_advice_size.toNat % 8 = 0)
    (belowInput : state.jolt_device.memory_layout.untrusted_advice_start.toNat +
        state.jolt_device.memory_layout.max_untrusted_advice_size.toNat ≤
      state.jolt_device.memory_layout.input_start.toNat) :
    initialRamWordFromState state' =
      byteInitialRam state.jolt_device.memory_layout (initialRamWordFromState state)
        untrustedAdvice := by
  funext address
  unfold initialRamWordFromState byteInitialRam
  rw [sail, device]
  dsimp only
  rw [empty]
  cases indexIs : untrustedAdviceWordIndex? state.jolt_device.memory_layout address with
  | none =>
    -- outside the block the untrusted overlay keeps the previous word on both sides
    rw [overlay_untrusted_outside _ aligned _ (by simp [wordBytes_size]) indexIs,
      overlay_untrusted_outside _ aligned #[] (by simp) indexIs]
  | some index =>
    unfold untrustedAdviceWordIndex? at indexIs
    cases firstIs : TraceWitness.remapRamAddress state.jolt_device.memory_layout
        state.jolt_device.memory_layout.untrusted_advice_start with
    | none => simp only [firstIs, reduceCtorEq] at indexIs
    | some first =>
      rw [firstIs] at indexIs
      dsimp only at indexIs
      split_ifs at indexIs with inBlock
      · simp only [Option.some.injEq] at indexIs
        subst indexIs
        have fits : 8 * (address - first) + 8 ≤
            state.jolt_device.memory_layout.max_untrusted_advice_size.toNat := by
          omega
        have untrusted : ∀ previous : BitVec 64, overlayRamBytes state.jolt_device.memory_layout
            state.jolt_device.memory_layout.untrusted_advice_start
            (wordBytes (adviceWord untrustedAdvice)
              state.jolt_device.memory_layout.max_untrusted_advice_size.toNat)
            address previous = adviceWord untrustedAdvice (address - first) := by
          intro previous
          unfold overlayRamBytes
          rw [firstIs]
          dsimp only
          rw [ite_eq_left ⟨inBlock.1, by rw [wordBytes_size]; omega⟩, Nat.mul_comm]
          exact ramImageWord_wordBytes _ _ _ fits
        rw [untrusted]
        -- the input region starts after the untrusted-advice block
        unfold overlayRamBytes
        cases inputIs : TraceWitness.remapRamAddress state.jolt_device.memory_layout
            state.jolt_device.memory_layout.input_start with
        | none => rfl
        | some inputFirst =>
          dsimp only
          rw [ite_eq_right]
          unfold TraceWitness.remapRamAddress at firstIs inputIs
          dsimp only at firstIs inputIs
          split_ifs at firstIs inputIs
          simp only [Option.some.injEq] at firstIs inputIs
          omega

/-- The relation Jolt's verifier checks reduces to the byte relation.
Each committed advice word that is the cast of a 64-bit word becomes that word, and every
other one becomes zero.
The tracer receives the little-endian bytes of these words, one per byte of the
untrusted-advice block, and the witness is shifted so that its RAM values start from
these words (`shiftWitness`).
The block must fit the tracer's size check (`JoltInstance.UntrustedAdviceBlockFits`). -/
theorem onBytes_of_allConstraints (joltField : JoltField F)
    {params : WitnessParams} {joltInstance : JoltInstance SourceInstruction}
    (blockFits : joltInstance.UntrustedAdviceBlockFits)
    (untrustedAdvice : Nat → F) {witness : WitnessType F params}
    (satisfied : AllConstraints joltInstance untrustedAdvice witness) :
    ∃ (privateInputs : JoltPrivateInputs) (witness' : WitnessType F params),
      AllConstraintsOnBytes joltInstance privateInputs witness' := by
  have charAbove2pow127 := two_pow_127_lt_char joltField
  obtain ⟨context, equations⟩ := satisfied
  obtain ⟨state, initialized, ramIs⟩ := context.initialized
  obtain ⟨layoutBuilt, -, untrustedIs, -, -⟩ :=
    initial_state_device joltInstance _ state initialized
  have layoutEq := (initial_state_memory_layout context initialized).symm
  obtain ⟨-, -, -, aligned, -, untrustedEnd, -, -, -, inputStart⟩ :=
    new_advice_regions _ _ layoutBuilt
  have fits : (wordBytes (adviceWord untrustedAdvice)
      state.jolt_device.memory_layout.max_untrusted_advice_size.toNat).size ≤
      joltInstance.memory_config.max_untrusted_advice_size.toNat := by
    rw [wordBytes_size]
    exact blockFits _ layoutBuilt
  obtain ⟨state', built', sail, -, device⟩ :=
    joltInstance.initial_state_with_untrusted_advice _ _ fits state initialized
  have ramIs' : initialRamWordFromState state' =
      byteInitialRam context.io.memory_layout context.initialRam untrustedAdvice := by
    rw [ramIs, layoutEq]
    exact initialRamWordFromState_untrustedAdvice untrustedAdvice state state' untrustedIs
      sail device aligned (by omega)
  have publicBuilt : joltInstance.memory_layout = some context.io.memory_layout := by
    rw [layoutEq]
    exact layoutBuilt
  have shifted := shiftWitness_equations charAbove2pow127 context equations
    (byteInitialRam context.io.memory_layout context.initialRam untrustedAdvice)
    (fun address word => byteInitialRam_good _ _ _ _ word)
    (fun address => byteInitialRam_masked _ context.io publicBuilt _ _ _)
  exact ⟨{ JoltPrivateInputs.noUntrustedAdvice with
      untrusted_advice := wordBytes (adviceWord untrustedAdvice)
        state.jolt_device.memory_layout.max_untrusted_advice_size.toNat }, _,
    { context with
      initialRam := byteInitialRam context.io.memory_layout context.initialRam untrustedAdvice
      initialized := ⟨state', built', ramIs'.symm⟩ }, shifted⟩

end JoltConstraints.Soundness.UntrustedAdvice
