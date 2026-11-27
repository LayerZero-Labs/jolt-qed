import JoltConstraints.theorems.Soundness.Layer5.RamAgreement
import JoltConstraints.theorems.Soundness.Layer3.Layout
import JoltConstraints.theorems.SharedMemoryExecution
import JoltConstraints.theorems.Soundness.Layer5.MemoryAccessRestriction

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

open JoltISA

/-- The public context binds the execution device to a checked layout.
For example, its input and output segments are those built for this instance. -/
private theorem device_layout_built
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (device : JoltDevice)
    (layoutIs : device.memory_layout = context.io.memory_layout) :
    MemoryLayout.new { inst.memory_config with program_size := some inst.program.program_size } =
      some device.memory_layout := by
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have publicLayout : layout = context.io.memory_layout :=
    congrArg JoltPublicIo.memory_layout (Option.some.inj sameIo)
  change MemoryLayout.new _ = some layout at hasLayout
  rwa [layoutIs, ← publicLayout]

/-- Every byte of an in-domain word passes the tracer's address-only check.
For example, an output word and a word in heap padding obey the same bound.
This follows from the verifier's domain checks, without a program restriction.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`assert_effective_address`). -/
theorem ram_word_address_checks
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (device : JoltDevice)
    (layoutIs : device.memory_layout = context.io.memory_layout)
    (index : Fin params.ramSize) (offset : Nat) (within : offset < 8) (write : Bool) :
    Mmu.effective_address_ok device
      (ramLowestAddress context.io.memory_layout + 8 * index.val + offset) write = true := by
  have built := device_layout_built context device layoutIs
  have backing := ram_domain_within_backing context
  unfold Mmu.effective_address_ok
  split
  · apply JoltDevice.readable_of_layout device _ built _
    · rw [layoutIs, MemoryLayout.get_lowest_address_toNat]
      unfold ramLowestAddress
      omega
    · assumption
  · simp only [decide_eq_true_eq, Mmu.ram_backing_end, layoutIs]
    have inDomain := index.isLt
    omega

/-- A memory row selects an admitted word, so its accessed doubleword passes
all address-only checks, including loads from I/O and stores to heap padding.
For example, `Load + Store = 1` excludes an otherwise unconstrained zero address.
Jolt at `ff6fc6568`:
`crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`
(the access-count claim). -/
theorem memory_row_address_checks
    {F : Type} [Field F] {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} {params : WitnessParams} {witness : WitnessType F params}
    (bound : 2 ^ 127 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (device : JoltDevice)
    (layoutIs : device.memory_layout = context.io.memory_layout)
    (address : BitVec 64) (encoded : witness.RamAddress t = (address.toNat : F))
    (memory : witness.OpFlags .Load t + witness.OpFlags .Store t = 1) (write : Bool) :
    DoublewordAddressChecks device address write := by
  obtain ⟨chosen, one, _⟩ := ramRa_unique_of_memory bound context equations t memory
  have addressIs := ramAddress_eq_of_selected bound context equations t chosen one address encoded
  have checked (offset : Nat) (within : offset < 8) :=
    ram_word_address_checks context device layoutIs chosen offset within write
  unfold DoublewordAddressChecks
  split
  · simpa only [← addressIs, Nat.add_zero] using checked 0 (by decide)
  · intro offset within
    simpa only [← addressIs] using checked offset within

/-- Bytes at or above the lowest checked I/O address bypass unsupported
peripheral dispatch.
For example, a shared input load cannot be mistaken for a UART load. -/
theorem unsupported_peripheral_false
    (config : MemoryConfig) (device : JoltDevice)
    (built : MemoryLayout.new config = some device.memory_layout)
    (address : Nat) (lower : device.memory_layout.get_lowest_address.toNat ≤ address) :
    Mmu.unsupported_load address = false ∧ Mmu.unsupported_store address = false := by
  have above := new_lowest_address_ge_half_ram config device.memory_layout built
  simp only [Mmu.unsupported_load, Mmu.unsupported_store, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- Every byte of an admitted word avoids unsupported peripheral dispatch.
For example, the first advice word lies above the UART and disk ranges. -/
theorem ram_word_peripheral_checks
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (device : JoltDevice)
    (layoutIs : device.memory_layout = context.io.memory_layout)
    (index : Fin params.ramSize) (offset : Nat) :
    Mmu.unsupported_load (ramLowestAddress context.io.memory_layout + 8 * index.val + offset) = false ∧
    Mmu.unsupported_store (ramLowestAddress context.io.memory_layout + 8 * index.val + offset) = false := by
  have built := device_layout_built context device layoutIs
  apply unsupported_peripheral_false _ device built
  rw [layoutIs, MemoryLayout.get_lowest_address_toNat]
  unfold ramLowestAddress
  omega

/-- Every byte of an aligned witness word rounds to that word and its remapped index.
For example, byte seven of witness word three still has remapped index three. -/
theorem ram_word_byte_geometry (layout : MemoryLayout)
    (aligned : layout.get_lowest_address.toNat % 8 = 0)
    (index offset : Nat) (within : offset < 8) :
    (ramLowestAddress layout + 8 * index + offset) / 8 * 8 =
        ramLowestAddress layout + 8 * index ∧
      (ramLowestAddress layout + 8 * index - layout.get_lowest_address.toNat) / 8 = index := by
  rw [MemoryLayout.get_lowest_address_toNat] at aligned ⊢
  unfold ramLowestAddress at *
  constructor <;> omega

/-- A protected byte of an admitted word makes the public C mask one.
The execution code interval must equal the interval computed from bytecode.
For example, an input byte and any byte of a canary-overlapping word are protected
by the same verifier mask that protects a code word.
Jolt at `ff6fc6568`: `preprocess/ram.rs` (`write_protected_word_intervals`). -/
theorem protected_byte_mask_one
    {F : Type} [Field F] (bytecode : Array JoltInstructionRow) (layout : MemoryLayout)
    (state : SailJoltState) (layoutIs : state.jolt_device.memory_layout = layout)
    (codeIs : state.codeRegion = ramCodeRegion bytecode layout)
    (aligned : layout.get_lowest_address.toNat % 8 = 0)
    (index offset : Nat) (within : offset < 8)
    (protects : Mmu.protected_byte state
      (ramLowestAddress layout + 8 * index + offset) = true) :
    ramWriteProtectedMask (F := F) bytecode layout index = 1 := by
  have lowIs := MemoryLayout.get_lowest_address_toNat layout
  obtain ⟨floorIs, indexIs⟩ := ram_word_byte_geometry layout aligned index offset within
  simp only [Mmu.protected_byte, SailJoltState.code_guard_any_region, layoutIs, codeIs,
      floorIs, indexIs,
    JoltDevice.is_input, JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at protects
  dsimp only [ramWriteProtectedMask]
  rw [ite_eq_left]
  rw [lowIs]
  unfold ramLowestAddress at protects
  simp only [STACK_CANARY_SIZE] at protects ⊢
  clear floorIs indexIs
  omega

/-- A word selected by the verifier's public C mask has every byte MMU-protected.
For example, a mask-selected input word preserves its eight initialized bytes.
The checked layout supplies the input/advice alignment used by the byte guard. -/
theorem mask_one_protected_byte
    {F : Type} [Field F] (bytecode : Array JoltInstructionRow) (layout : MemoryLayout)
    (config : MemoryConfig) (built : MemoryLayout.new config = some layout)
    (state : SailJoltState) (layoutIs : state.jolt_device.memory_layout = layout)
    (codeIs : state.codeRegion = ramCodeRegion bytecode layout)
    (index offset : Nat) (within : offset < 8)
    (masked : ramWriteProtectedMask (F := F) bytecode layout index = 1) :
    Mmu.protected_byte state (ramLowestAddress layout + 8 * index + offset) = true := by
  have aligned := new_lowest_address_aligned config layout built
  have inputAligned := new_input_word_aligned config layout built
  have low := (new_io_ordered config layout built).1
  obtain ⟨_, _, _, _, _, _, _, trustedAligned, untrustedAligned, _⟩ :=
    new_advice_regions config layout built
  obtain ⟨floorIs, indexIs⟩ := ram_word_byte_geometry layout aligned index offset within
  obtain ⟨outputAfter, inputMultiple⟩ := new_outputs_after_inputs config layout built
  have inputEnd := new_input_end_eq_output_start config layout built
  unfold ramWriteProtectedMask at masked
  dsimp only at masked
  split at masked
  · rename_i selected
    simp only [Mmu.protected_byte, SailJoltState.code_guard_any_region, layoutIs, codeIs,
      floorIs, indexIs,
      JoltDevice.is_input, JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [MemoryLayout.get_lowest_address_toNat] at aligned inputAligned low selected
    unfold ramLowestAddress
    simp only [STACK_CANARY_SIZE] at selected ⊢
    omega
  · exact False.elim (zero_ne_one masked)

/-- The protected-increment claim supplies the MMU's actual protected-value check.
The selected word agrees with shared memory, and the stored word is the constrained
write value.
For example, an input SD is admitted precisely when it keeps the old word.
No additional program restriction is an input to this theorem.
Jolt at `ff6fc6568`:
`crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`
(protected-increment claim) and
`tracer/src/emulator/mmu.rs` (`assert_write_protected_store`). -/
theorem protected_store_of_constraints
    {F : Type} [Field F] {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} {params : WitnessParams} {witness : WitnessType F params}
    (bound : 2 ^ 127 < ringChar F) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (state : SailJoltState)
    (layoutIs : state.jolt_device.memory_layout = context.io.memory_layout)
    (codeIs : state.codeRegion = ramCodeRegion context.bytecode context.io.memory_layout)
    (agrees : SharedRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) state)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1)
    (address value : BitVec 64) (encoded : witness.RamAddress t = (address.toNat : F))
    (written : witness.RamWriteValue t = (value.toNat : F)) :
    Mmu.assert_write_protected_store state address.toNat value 8 = true := by
  have addressIs := ramAddress_eq_of_selected bound context equations t chosen selected address encoded
  have built := device_layout_built context state.jolt_device layoutIs
  have aligned := new_lowest_address_aligned _ _ built
  rw [layoutIs] at aligned
  have wordAligned : address.toNat % 8 = 0 := by
    obtain ⟨floorIs, _⟩ := ram_word_byte_geometry context.io.memory_layout aligned chosen.val 0
      (by decide)
    rw [addressIs]
    simp only [Nat.add_zero] at floorIs
    omega
  apply (Mmu.assert_write_protected_store_aligned_iff state address.toNat value wordAligned).mpr
  intro hp
  have maskOne := protected_byte_mask_one (F := F) context.bytecode context.io.memory_layout
    state layoutIs codeIs aligned chosen.val 0 (by decide)
    (by simpa only [← addressIs, Nat.add_zero] using hp)
  have zero := ramInc_zero_of_selected_protected bound context equations t chosen selected maskOne
  have fieldSame : (value.toNat : F) =
      ((Mmu.ram_doubleword state.sail.mem address.toNat).toNat : F) := by
    calc
      (value.toNat : F) = witness.RamWriteValue t := written.symm
      _ = witness.RamVal chosen t := by
        rw [ramWriteValue_of_selected bound context equations t chosen selected, zero, add_zero]
      _ = _ := by simpa only [addressIs] using agrees chosen
  exact (BitVec.eq_of_toNat_eq (natCast_injective_below_char
    (lt_trans value.isLt (two_pow_64_lt_char bound))
    (lt_trans (Mmu.ram_doubleword state.sail.mem address.toNat).isLt
      (two_pow_64_lt_char bound)) fieldSame)).symm

end JoltConstraints.Soundness
