import JoltConstraints.theorems.Completeness.Helpers.RamOutputProofHelpers
import JoltConstraints.translation.Constraints.RamOutputEqPublicIo
import JoltConstraints.translation.honest_witness

open LeanRV64D
set_option autoImplicit false
namespace JoltConstraints

/-- The honest witness's final shared-memory words equal its public input and output
bytes on the verifier's input/output interval.
For example, input padding stays zero through protected stores, while output words
are extracted directly from final shared memory.
Jolt at `ff6fc6568`: `PublicIoMemory::new` and `Mmu::assert_write_protected_store`. -/
theorem honestWitness_ramOutputEqPublicIo
    {F : Type} [Field F] (params : WitnessParams)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace inst inputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramOutputEqPublicIo trace.publicIo (HonestTrace.honestWitness (F := F) params trace) := by
  intro address
  change ramPublicIoMask trace.publicIo address.val *
    (((TraceWitness.finalRamWord trace address.val).toNat : F) -
      ((ramPublicIoWord trace.publicIo address.val).toNat : F)) = 0
  let layout := trace.initialState.jolt_device.memory_layout
  have built := (initial_state_device inst inputs trace.initialState trace.initialized).1
  unfold JoltInstance.memory_layout at built
  have finalLayout := (finalTraceState_ioSame trace).1
  have ioLayout : trace.publicIo.memory_layout = layout := finalLayout
  obtain ⟨outputAfter, outputLength, _⟩ := new_io_word_geometry _ _ built
  rw [MemoryLayout.get_lowest_address_toNat] at outputAfter outputLength
  let inputFirst := (layout.input_start.toNat - ramLowestAddress layout) / 8
  let outputFirst := (layout.output_start.toNat - ramLowestAddress layout) / 8
  let outputEnd := (layout.output_end.toNat - ramLowestAddress layout) / 8
  change outputFirst = inputFirst + layout.max_input_size.toNat / 8 at outputAfter
  change outputEnd = outputFirst + layout.max_output_size.toNat / 8 at outputLength
  unfold ramPublicIoMask
  rw [ioLayout]
  dsimp only
  split_ifs with checked
  · have lower : inputFirst ≤ address.val := checked.1
    have upper : address.val < outputEnd := checked.2
    have sameWord : TraceWitness.finalRamWord trace address.val = ramPublicIoWord trace.publicIo address.val := by
      by_cases input : address.val < outputFirst
      · let q := address.val - inputFirst
        have qInside : q < layout.max_input_size.toNat / 8 := by dsimp only [q]; omega
        have indexEq : inputFirst + q = address.val := by dsimp only [q]; omega
        have finalWord := finalRamWord_input trace q qInside
        have publicWord := ramPublicIoWord_input _ layout built trace.publicIo ioLayout q qInside
        rw [show (layout.input_start.toNat - ramLowestAddress layout) / 8 + q = address.val from indexEq] at publicWord
        change TraceWitness.finalRamWord trace (inputFirst + q) = _ at finalWord
        rw [indexEq] at finalWord
        exact finalWord.trans publicWord.symm
      · let q := address.val - outputFirst
        have qInside : q < layout.max_output_size.toNat / 8 := by dsimp only [q]; omega
        have indexEq : outputFirst + q = address.val := by dsimp only [q]; omega
        have valid := trace.valid_inputs
        unfold JoltInstance.validate_inputs at valid
        have layoutIs : inst.memory_layout = some layout := built
        rw [layoutIs] at valid
        simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
        have inputFit : trace.publicIo.inputs.size ≤ layout.max_input_size.toNat := valid.1.1.2
        have finalWord := finalRamWord_output trace _ layout built rfl finalLayout q qInside
        have publicWord := ramPublicIoWord_output _ layout built trace.publicIo ioLayout inputFit q qInside
        change TraceWitness.finalRamWord trace (outputFirst + q) = _ at finalWord
        change ramPublicIoWord trace.publicIo (outputFirst + q) = _ at publicWord
        rw [indexEq] at finalWord publicWord
        exact finalWord.trans publicWord.symm
    rw [sameWord, sub_self, mul_zero]
  · rw [zero_mul]

end JoltConstraints
