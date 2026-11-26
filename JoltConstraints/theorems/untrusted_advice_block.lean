import JoltConstraints.theorems.advice_inputs
import JoltConstraints.theorems.SharedMemoryInitialization
import JoltConstraints.theorems.Soundness.Layer3.State

open LeanRV64D

/-! The untrusted-advice block of the initial RAM.
Jolt's verifier adds a committed block of `max_untrusted_advice_size / 8` words at the
remapped word of `untrusted_advice_start` (`ram_val_check_advice_block`). This file shows
that the block is exactly where the tracer installs the untrusted-advice bytes: the
checked layout places the block at an 8-byte boundary above the lowest address, gives it
a whole number of words, and ends it at or before the inputs. Installing advice bytes
changes the initial RAM only inside the block.
Jolt at `ff6fc6568`: `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_advice_block`), `common/src/jolt_device.rs` (`MemoryLayout::try_new`,
`JoltDevice::try_with_io`) and `tracer/src/lib.rs` (`create_emulator`). -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness

/-- The numbers that place the untrusted-advice block in a checked layout.
The lowest address is the smaller advice start, positive and a multiple of 8; the
untrusted-advice start is a multiple of 8; its capacity is a multiple of 8; and the
block ends where its capacity ends, at or before the inputs.
For example, a layout with zero advice capacities has an empty block at the inputs.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`,
`get_lowest_address`). -/
theorem untrustedBlock_geometry (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat =
        layout.get_lowest_address.toNat ∧
      0 < layout.get_lowest_address.toNat ∧
      layout.get_lowest_address.toNat % 8 = 0 ∧
      layout.untrusted_advice_start.toNat % 8 = 0 ∧
      layout.max_untrusted_advice_size.toNat % 8 = 0 ∧
      layout.get_lowest_address.toNat ≤ layout.untrusted_advice_start.toNat ∧
      layout.untrusted_advice_end.toNat =
        layout.untrusted_advice_start.toNat + layout.max_untrusted_advice_size.toNat ∧
      layout.untrusted_advice_start.toNat + layout.max_untrusted_advice_size.toNat ≤
        layout.input_start.toNat := by
  have positive := new_lowest_address_pos config layout built
  have aligned := new_lowest_address_aligned config layout built
  obtain ⟨_, _, _, sizeAligned, _, untrustedEnd, _, _, startAligned, inputStart⟩ :=
    new_advice_regions config layout built
  unfold MemoryLayout.get_lowest_address at positive aligned ⊢
  rw [Nat.min_def]
  by_cases order : layout.trusted_advice_start.toNat ≤ layout.untrusted_advice_start.toNat
  · rw [ite_eq_left order] at positive aligned ⊢
    rw [ite_eq_left order]
    omega
  · rw [ite_eq_right order] at positive aligned ⊢
    rw [ite_eq_right order]
    omega

/-- In a checked layout, the untrusted-advice start remaps to the word
`(untrusted_advice_start - lowest) / 8`.
For example, if the untrusted advice starts at the lowest address, it remaps to word 0. -/
theorem remap_untrusted_start (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    remapRamAddress layout layout.untrusted_advice_start =
      some ((layout.untrusted_advice_start.toNat - layout.get_lowest_address.toNat) / 8) := by
  obtain ⟨lowestIs, positive, -, -, -, below, -, -⟩ := untrustedBlock_geometry config layout built
  unfold remapRamAddress
  dsimp only
  rw [lowestIs, ite_eq_right (by omega)]

/-- In a checked layout, word `address` lies in the untrusted-advice block exactly when it
is at most `max_untrusted_advice_size / 8 - 1` words past the block's first word.
For example, with the block at word 100 and a 16-byte capacity, word 101 has index 1. -/
theorem untrustedAdviceWordIndex?_eq (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) (address : Nat) :
    untrustedAdviceWordIndex? layout address =
      let first := (layout.untrusted_advice_start.toNat - layout.get_lowest_address.toNat) / 8
      if first ≤ address ∧ address - first < layout.max_untrusted_advice_size.toNat / 8 then
        some (address - first)
      else none := by
  unfold untrustedAdviceWordIndex?
  rw [remap_untrusted_start config layout built]

/-- Every word of the untrusted-advice block is write-protected.
For example, a store to the first advice word must keep its value.
Jolt at `ff6fc6568`: `crates/jolt-program/src/preprocess/ram.rs`
(`write_protected_word_intervals`). -/
theorem writeProtectedMask_of_untrustedAdvice {F : Type} [Field F] (config : MemoryConfig)
    (layout : MemoryLayout) (built : MemoryLayout.new config = some layout)
    (bytecode : Array JoltInstructionRow) {address index : Nat}
    (indexIs : untrustedAdviceWordIndex? layout address = some index) :
    ramWriteProtectedMask (F := F) bytecode layout address = 1 := by
  obtain ⟨-, -, lowestAligned, startAligned, sizeAligned, below, untrustedEnd, -⟩ :=
    untrustedBlock_geometry config layout built
  rw [untrustedAdviceWordIndex?_eq config layout built] at indexIs
  dsimp only at indexIs
  have inBlock : (layout.untrusted_advice_start.toNat - layout.get_lowest_address.toNat) / 8 ≤
      address ∧ address - (layout.untrusted_advice_start.toNat -
        layout.get_lowest_address.toNat) / 8 < layout.max_untrusted_advice_size.toNat / 8 := by
    by_contra outside
    rw [ite_eq_right outside] at indexIs
    cases indexIs
  unfold ramWriteProtectedMask
  dsimp only
  rw [ite_eq_left]
  right; right; right; left
  refine ⟨by omega, by omega, by omega⟩

/-- The public I/O mask is zero on the untrusted-advice block, which ends at or before the
inputs.
For example, the last advice word lies below the first input word. -/
theorem publicIoMask_of_untrustedAdvice {F : Type} [Field F] (config : MemoryConfig)
    (io : JoltPublicIo) (built : MemoryLayout.new config = some io.memory_layout)
    {address index : Nat}
    (indexIs : untrustedAdviceWordIndex? io.memory_layout address = some index) :
    ramPublicIoMask (F := F) io address = 0 := by
  obtain ⟨lowestIs, -, lowestAligned, startAligned, sizeAligned, below, -, inputAbove⟩ :=
    untrustedBlock_geometry config io.memory_layout built
  rw [untrustedAdviceWordIndex?_eq config io.memory_layout built] at indexIs
  dsimp only at indexIs
  have inBlock : (io.memory_layout.untrusted_advice_start.toNat -
      io.memory_layout.get_lowest_address.toNat) / 8 ≤ address ∧
      address - (io.memory_layout.untrusted_advice_start.toNat -
        io.memory_layout.get_lowest_address.toNat) / 8 <
        io.memory_layout.max_untrusted_advice_size.toNat / 8 := by
    by_contra outside
    rw [ite_eq_right outside] at indexIs
    cases indexIs
  unfold ramPublicIoMask ramLowestAddress
  dsimp only
  rw [lowestIs, ite_eq_right (by omega)]

/-- Installing a buffer sets each byte of its range and keeps every other byte.
For example, installing two bytes at address 100 sets bytes 100 and 101 only. -/
theorem buffer_insert_get? (start : Nat) (bytes : Array (BitVec 8))
    (mem : Std.ExtHashMap Nat (BitVec 8)) (address : Nat) :
    (bytes.toList.zipIdx.foldl (fun m byte => m.insert (start + byte.2) byte.1) mem).get?
        address =
      if start ≤ address ∧ address < start + bytes.size then bytes[address - start]?
      else mem.get? address := by
  by_cases inside : start ≤ address ∧ address < start + bytes.size
  · rw [ite_eq_left inside]
    have read := zipIdx_fold_get? start bytes.toList 0 (address - start) mem
    rw [Nat.add_sub_cancel' inside.1] at read
    rw [read, ite_eq_left (by simp only [Array.length_toList]; omega)]
    simp
  · rw [ite_eq_right inside]
    apply List.foldlRecOn (motive := fun m : Std.ExtHashMap Nat (BitVec 8) =>
      m.get? address = mem.get? address) _ _ rfl
    intro current same byte member
    have bound : byte.2 < bytes.size := by
      simpa using List.snd_lt_add_of_mem_zipIdx member
    have different : start + byte.2 ≠ address := by omega
    simpa [Std.ExtHashMap.getElem?_insert, different] using same

/-- Shared-memory initialization with untrusted-advice bytes equals initialization without
them followed by installing the bytes at `untrusted_advice_start`.
For example, the input bytes are the same in both maps. -/
theorem initialMem_untrusted_get? (device : JoltDevice) (base : Std.ExtHashMap Nat (BitVec 8))
    (inputs trusted bytes : Array (BitVec 8)) (empty withBytes : Std.ExtHashMap Nat (BitVec 8))
    (builtEmpty : device.initialMem base inputs trusted #[] = some empty)
    (builtBytes : device.initialMem base inputs trusted bytes = some withBytes)
    (address : Nat) :
    withBytes.get? address =
      if device.memory_layout.untrusted_advice_start.toNat ≤ address ∧
          address < device.memory_layout.untrusted_advice_start.toNat + bytes.size then
        bytes[address - device.memory_layout.untrusted_advice_start.toNat]?
      else empty.get? address := by
  unfold JoltDevice.initialMem at builtEmpty builtBytes
  obtain ⟨_, _, builtEmpty⟩ := Option.bind_eq_some_iff.mp builtEmpty
  obtain ⟨_, _, builtBytes⟩ := Option.bind_eq_some_iff.mp builtBytes
  rw [← Option.some.inj builtEmpty, ← Option.some.inj builtBytes]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [buffer_insert_get?]
  simp

/-- Two initializations that differ only in the untrusted-advice bytes have the same device,
and their memories differ only in the bytes' range above `untrusted_advice_start`.
For example, empty advice and two advice bytes give the same input bytes. -/
theorem initial_state_untrusted_get? {Source : Type} (joltInstance : JoltInstance Source)
    (tape bytes : Array (BitVec 8)) (empty withBytes : SailJoltState)
    (builtEmpty : joltInstance.initial_state
      { untrusted_advice := #[], advice_tape := tape } = some empty)
    (builtBytes : joltInstance.initial_state
      { untrusted_advice := bytes, advice_tape := tape } = some withBytes) :
    withBytes.jolt_device = empty.jolt_device ∧
      ∀ address, withBytes.sail.mem.get? address =
        if empty.jolt_device.memory_layout.untrusted_advice_start.toNat ≤ address ∧
            address < empty.jolt_device.memory_layout.untrusted_advice_start.toNat +
              bytes.size then
          bytes[address - empty.jolt_device.memory_layout.untrusted_advice_start.toNat]?
        else empty.sail.mem.get? address := by
  obtain ⟨layout, layoutBuilt, -, -, -, initEmpty⟩ :=
    initial_state_build joltInstance _ empty builtEmpty
  obtain ⟨layout', layoutBuilt', -, -, -, initBytes⟩ :=
    initial_state_build joltInstance _ withBytes builtBytes
  rw [layoutBuilt] at layoutBuilt'
  cases Option.some.inj layoutBuilt'
  obtain ⟨_, memEmpty, -, memEmptyBuilt, shapeEmpty⟩ :=
    initialState_shape _ _ _ _ _ _ initEmpty
  obtain ⟨_, memBytes, -, memBytesBuilt, shapeBytes⟩ :=
    initialState_shape _ _ _ _ _ _ initBytes
  subst shapeEmpty shapeBytes
  refine ⟨rfl, ?_⟩
  intro address
  exact initialMem_untrusted_get? _ _ _ _ _ _ _ memEmptyBuilt memBytesBuilt address

/-- Outside the untrusted-advice block, the initial RAM does not depend on the
untrusted-advice bytes.
For example, a program word reads the same with empty advice and with 16 advice bytes. -/
theorem initialRamWord_outside_untrusted {Source : Type} (joltInstance : JoltInstance Source)
    (tape bytes : Array (BitVec 8)) (empty withBytes : SailJoltState)
    (builtEmpty : joltInstance.initial_state
      { untrusted_advice := #[], advice_tape := tape } = some empty)
    (builtBytes : joltInstance.initial_state
      { untrusted_advice := bytes, advice_tape := tape } = some withBytes)
    {address : Nat}
    (outside : untrustedAdviceWordIndex? empty.jolt_device.memory_layout address = none) :
    initialRamWordFromState withBytes address = initialRamWordFromState empty address := by
  obtain ⟨sameDevice, memory⟩ :=
    initial_state_untrusted_get? joltInstance tape bytes empty withBytes builtEmpty builtBytes
  obtain ⟨layoutBuilt, -, bytesFit⟩ :=
    initial_state_device joltInstance _ withBytes builtBytes
  rw [sameDevice] at layoutBuilt bytesFit
  change bytes.size ≤ _ at bytesFit
  unfold JoltInstance.memory_layout at layoutBuilt
  obtain ⟨-, -, lowestAligned, startAligned, sizeAligned, below, -, -⟩ :=
    untrustedBlock_geometry _ _ layoutBuilt
  rw [untrustedAdviceWordIndex?_eq _ _ layoutBuilt] at outside
  dsimp only at outside
  have notInBlock : ¬ ((empty.jolt_device.memory_layout.untrusted_advice_start.toNat -
      empty.jolt_device.memory_layout.get_lowest_address.toNat) / 8 ≤ address ∧
      address - (empty.jolt_device.memory_layout.untrusted_advice_start.toNat -
        empty.jolt_device.memory_layout.get_lowest_address.toNat) / 8 <
        empty.jolt_device.memory_layout.max_untrusted_advice_size.toNat / 8) := by
    intro inBlock
    rw [ite_eq_left inBlock] at outside
    cases outside
  unfold initialRamWordFromState
  dsimp only
  rw [sameDevice]
  apply ramImageWord_congr
  intro offset _
  rw [memory, ite_eq_right (by omega)]

/-- Inside the untrusted-advice block, the initial RAM word packs the eight advice bytes
at its offset in the block.
For example, the block's word 1 packs advice bytes 8 through 15. -/
theorem initialRamWord_inside_untrusted {Source : Type} (joltInstance : JoltInstance Source)
    (tape bytes : Array (BitVec 8)) (empty withBytes : SailJoltState)
    (builtEmpty : joltInstance.initial_state
      { untrusted_advice := #[], advice_tape := tape } = some empty)
    (builtBytes : joltInstance.initial_state
      { untrusted_advice := bytes, advice_tape := tape } = some withBytes)
    {address index : Nat}
    (inside : untrustedAdviceWordIndex? empty.jolt_device.memory_layout address = some index)
    (fits : 8 * index + 8 ≤ bytes.size) :
    initialRamWordFromState withBytes address =
      ramImageWord (fun offset => bytes[offset]?.getD 0) (8 * index) := by
  obtain ⟨sameDevice, memory⟩ :=
    initial_state_untrusted_get? joltInstance tape bytes empty withBytes builtEmpty builtBytes
  obtain ⟨layoutBuilt, -, -⟩ := initial_state_device joltInstance _ empty builtEmpty
  unfold JoltInstance.memory_layout at layoutBuilt
  obtain ⟨-, -, lowestAligned, startAligned, sizeAligned, below, -, -⟩ :=
    untrustedBlock_geometry _ _ layoutBuilt
  rw [untrustedAdviceWordIndex?_eq _ _ layoutBuilt] at inside
  dsimp only at inside
  split_ifs at inside with inBlock
  cases inside
  unfold initialRamWordFromState
  dsimp only
  rw [sameDevice]
  apply ramImageWord_congr
  intro offset _
  rw [memory, ite_eq_left (by omega)]
  congr 2
  omega

/-- Initialization without untrusted advice succeeds whenever initialization with some
untrusted advice does, with the same execution tape.
For example, a run with 16 advice bytes has a matching run with none. -/
theorem initial_state_without_untrusted {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (state : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some state) :
    ∃ empty, joltInstance.initial_state
      { untrusted_advice := #[], advice_tape := privateInputs.advice_tape } = some empty := by
  obtain ⟨layout, layoutBuilt, code, trustedFits, -, inputsFit⟩ :=
    (initial_state_isSome_iff joltInstance privateInputs).mp
      (Option.isSome_iff_exists.mpr ⟨state, built⟩)
  exact Option.isSome_iff_exists.mp ((initial_state_isSome_iff joltInstance _).mpr
    ⟨layout, layoutBuilt, code, trustedFits, by simp, inputsFit⟩)

/-- The byte relation gives the relation Jolt's verifier checks, with the words of the
untrusted-advice block of the context's initial RAM as the committed words.
For example, an honest run's witness satisfies `AllConstraints` with the advice words of
its initial RAM. -/
theorem allConstraints_of_onBytes {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {witness : WitnessType F params}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io
      context.entry witness) :
    AllConstraints joltInstance (adviceBlockWords context.io.memory_layout context.initialRam)
      witness := by
  obtain ⟨state, built, ramIs⟩ := context.initialized
  have layoutIs := Soundness.initial_state_memory_layout context built
  -- the same run with an empty execution tape
  have builtTape := joltInstance.initial_state_with_advice_tape privateInputs #[]
  rw [built, Option.map_some] at builtTape
  -- the run without untrusted advice
  obtain ⟨empty, builtEmpty⟩ := initial_state_without_untrusted joltInstance
    { privateInputs with advice_tape := #[] } _ builtTape
  have emptyLayout : empty.jolt_device.memory_layout = context.io.memory_layout := by
    obtain ⟨sameDevice, -⟩ := initial_state_untrusted_get? joltInstance #[]
      privateInputs.untrusted_advice empty _ builtEmpty builtTape
    rw [← sameDevice]
    exact layoutIs
  obtain ⟨layoutBuilt, -, -⟩ := initial_state_device joltInstance _ empty builtEmpty
  rw [emptyLayout] at layoutBuilt
  unfold JoltInstance.memory_layout at layoutBuilt
  refine ⟨{ context with
    initialRam := initialRamWordFromState empty
    initialized := ⟨empty, builtEmpty, rfl⟩ }, ?_⟩
  have same : committedInitialValue (F := F) context.io.memory_layout
      (initialRamWordFromState empty)
      (adviceBlockWords context.io.memory_layout context.initialRam) =
      ramInitialValue (F := F) context.initialRam := by
    funext address
    unfold committedInitialValue
    cases indexIs : untrustedAdviceWordIndex? context.io.memory_layout address with
    | none =>
      dsimp only
      unfold ramInitialValue
      rw [← emptyLayout] at indexIs
      rw [ramIs, ← initialRamWord_outside_untrusted joltInstance #[]
        privateInputs.untrusted_advice empty _ builtEmpty builtTape indexIs]
      rfl
    | some index =>
      dsimp only
      have indexIs' := indexIs
      rw [untrustedAdviceWordIndex?_eq _ _ layoutBuilt] at indexIs'
      dsimp only at indexIs'
      split_ifs at indexIs' with inBlock
      cases indexIs'
      unfold adviceBlockWords
      rw [remap_untrusted_start _ _ layoutBuilt]
      dsimp only
      rw [Nat.add_sub_cancel' inBlock.1]
  change FieldConstraintEquations context.bytecode
    (committedInitialValue (F := F) context.io.memory_layout (initialRamWordFromState empty)
      (adviceBlockWords context.io.memory_layout context.initialRam))
    context.io context.entry witness
  rw [same]
  exact equations

end JoltConstraints
