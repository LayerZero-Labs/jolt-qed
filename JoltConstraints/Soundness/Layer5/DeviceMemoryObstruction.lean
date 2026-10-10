import JoltConstraints.Soundness.Layer3.Updates
import JoltConstraints.Soundness.Layer3.Layout

/-! The known termination-device discrepancy obstructs the proposed full RAM
agreement invariant in Layer 5b. This file proves the execution behavior for
a layout produced by `MemoryLayout.new`, within the approved RAM-region bound,
and the conflicting next-table value forced by a selected store of one.

This is not a constructed witness satisfying `AllConstraints`, nor a new
verifier reproduction. It formalizes the local obstruction behind the existing
termination issue (#1950/#1951). No soundness premise or semantics is changed.
Jolt revision checked: 43cc043332762034b5f65379441576e06e7a3890,
common/src/jolt_device.rs:121-155 (loads return zero; stores are ignored). -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.DeviceMemoryObstruction

open Sail PreSail LeanRV64D.Functions JoltISA

private instance : DecidableEq MemoryLayout := by
  intro a b
  cases a
  cases b
  exact decidable_of_iff _ MemoryLayout.mk.injEq.symm

/-- A small configuration with one output word and no advice, stack or heap. -/
def config : MemoryConfig := {
  max_input_size := 0, max_trusted_advice_size := 0,
  max_untrusted_advice_size := 0, max_output_size := 8,
  stack_size := 0, heap_size := 0, program_size := some 8 }

/-- The corresponding layout has termination at 0x7ffffff0, RAM index 2. -/
def layout : MemoryLayout := {
  program_size := 8
  max_trusted_advice_size := 0
  trusted_advice_start := 0x7fffffe0
  trusted_advice_end := 0x7fffffe0
  max_untrusted_advice_size := 0
  untrusted_advice_start := 0x7fffffe0
  untrusted_advice_end := 0x7fffffe0
  max_input_size := 0
  max_output_size := 8
  input_start := 0x7fffffe0
  input_end := 0x7fffffe0
  output_start := 0x7fffffe0
  output_end := 0x7fffffe8
  stack_size := 0
  stack_end := 0x80000008
  heap_size := 0
  heap_end := 0x80000088
  panic := 0x7fffffe8
  termination := 0x7ffffff0
  io_end := 0x7ffffff8 }

/-- This is a successfully generated layout, rather than an arbitrary set of
device addresses. Kernel reduction checks the concrete layout computation. -/
theorem layout_from_config : MemoryLayout.new config = some layout := by decide +kernel

/-- The example's maximum RAM domain is small and satisfies the approved
64-bit region bound; address wraparound does not explain the discrepancy. -/
theorem layout_ram_bound :
    VerifierSizes.maxRamSize layout = some 32 ∧
    layout.get_lowest_address.toNat + 8 * 32 ≤ 2 ^ 64 ∧
    TraceWitness.remapRamAddress layout layout.termination = some 2 := by decide +kernel

/-- An initially empty device using the generated layout. -/
def device : JoltDevice := {
  inputs := #[], trusted_advice := #[], untrusted_advice := #[],
  outputs := #[], panic := false, memory_layout := layout }

/-- Storing any word at termination succeeds and leaves the full state
unchanged: each of the eight device-byte writes is ignored. -/
theorem termination_store_ignored (state : SailJoltState) (value : BitVec 64) :
    Mmu.store_doubleword layout.termination value { state with jolt_device := device } =
      .ok (.Ok true) { state with jolt_device := device } := by rfl

/-- Loading the termination word returns zero, even after an ignored store. -/
theorem termination_load_zero (state : SailJoltState) :
    Mmu.load_doubleword layout.termination { state with jolt_device := device } =
      .ok (.Ok 0) { state with jolt_device := device } := by rfl

/-- The composed memory operations store one successfully, then read zero.
Both calls use the actual MMU execution functions, including address checks. -/
theorem termination_store_then_load (state : SailJoltState) :
    (do
      let _ ← Mmu.store_doubleword layout.termination 1
      Mmu.load_doubleword layout.termination) { state with jolt_device := device } =
      .ok (.Ok 0) { state with jolt_device := device } := by
  simp only [bind, EStateM.bind, termination_store_ignored, termination_load_zero]

/-- In contrast, a selected store whose source value is one forces the next
RAM-table entry to one. Therefore it cannot match the termination device's
zero read after that store. This is conditional on the constraint facts; it
does not assert existence of a complete satisfying witness with such a row. -/
theorem selected_store_one_disagrees
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (address : Fin params.ramSize) (selected : witness.RamRa address t = 1)
    (store : witness.OpFlags .Store t = 1) (source : witness.Rs2Value t = 1) :
    witness.RamVal address ⟨t.val + 1, next⟩ = 1 ∧
    witness.RamVal address ⟨t.val + 1, next⟩ ≠ ((0 : BitVec 64).toNat : F) := by
  have write : witness.RamWriteValue t = 1 := by
    have relation := equations.rs2EqRamWriteIfStore t
    rw [store, source, one_mul] at relation
    exact (sub_eq_zero.mp relation).symm
  have updated : witness.RamVal address ⟨t.val + 1, next⟩ = 1 := by
    rw [ramVal_succ_of_selected charAbove2pow127 context equations address t next address selected,
      if_pos rfl, write]
  refine ⟨updated, ?_⟩
  rw [updated]
  change (1 : F) ≠ ((0 : Nat) : F)
  simp only [Nat.cast_zero]
  exact _root_.one_ne_zero

end JoltConstraints.Soundness.DeviceMemoryObstruction
