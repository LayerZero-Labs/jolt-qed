import JoltConstraints.theorems.MemoryRowExecution

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA JoltConstraints JoltConstraints.Soundness

set_option autoImplicit false

noncomputable section

namespace WholeRun

local macro "storeRunHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.ProgramBlocks
    (`StoreProgramBlocks ++ n.getId)))

/-- Source bytes selected by a narrow store; for example, SH selects two bytes.
Its lowered store still writes a merged eight-byte word. -/
def narrowStoreBytes : AccessWidth → Nat
  | .byte => 1
  | .halfword => 2
  | .word => 4

private def floorWidth : AccessWidth → MemoryWidth
  | .byte => .byte
  | .halfword => .halfword
  | .word => .word

private theorem floorLoad_write (width : AccessWidth) (rs1 : regidx)
    (imm : BitVec 64) (pre post : SailJoltState)
    (runs : execInstr (LoadFamily.floorLoadRow width (.vreg 40) (.xreg rs1) imm
      .normal (.E_SAMO_Addr_Align ())) pre = .ok RETIRE_SUCCESS post) :
    (sourceValue (.xreg rs1) pre + imm) &&& LoadFamily.alignmentMask width = 0 ∧
      post = stateAfterVRegWrite pre 40 (Mmu.ram_doubleword pre.sail.mem
        ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7).toNat) := by
  let instruction := LoadFamily.floorLoadRow width (.vreg 40) (.xreg rs1) imm
    .normal (.E_SAMO_Addr_Align ())
  have row : LoadRow instruction (floorWidth width) (.vreg 40) (.xreg rs1) imm := by
    refine ⟨.normal, .E_SAMO_Addr_Align (), ?_⟩
    cases width <;> rfl
  let advice : instruction.RuntimeAdvice := by cases width <;> exact ()
  have runs' : execInstr (instruction.withRuntimeAdvice advice) pre = .ok RETIRE_SUCCESS post := by
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice]
    exact runs
  have aligned := (row.aligned_continuation_of_run advice pre post runs').1
  have postEq := row.vreg_post_of_run (by unfold WritableVReg; decide) advice pre post runs'
  have address : (floorWidth width).accessed (sourceValue (.xreg rs1) pre + imm) =
      (sourceValue (.xreg rs1) pre + imm) &&& ~~~7 := by cases width <;> rfl
  rw [address] at postEq
  refine ⟨?_, ?_⟩
  · cases width <;> exact aligned
  · exact postEq

private theorem floorStore_store (width : AccessWidth) (rs1 : regidx)
    (imm : BitVec 64) (pre post : SailJoltState)
    (runs : execInstr ((storeRunHelper% floorStoreRow) width (.xreg rs1) 40 imm
      (.E_SAMO_Addr_Align ())) pre = .ok RETIRE_SUCCESS post) :
    ∃ result, Mmu.store_doubleword ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7)
      (pre.vregs 40) pre = .ok result post := by
  let instruction := (storeRunHelper% floorStoreRow) width (.xreg rs1) 40 imm
    (.E_SAMO_Addr_Align ())
  have row : StoreRow instruction (floorWidth width) (.xreg rs1) (.vreg 40) imm := by
    refine ⟨.E_SAMO_Addr_Align (), ?_⟩
    cases width <;> rfl
  let advice : instruction.RuntimeAdvice := by cases width <;> exact ()
  have stored := row.store_of_run 0 advice pre post (by
    rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice,
      execWithTapeAnswer_of_ne _ 0 row.access.not_tape]
    exact runs)
  have address : (floorWidth width).accessed (sourceValue (.xreg rs1) pre + imm) =
      (sourceValue (.xreg rs1) pre + imm) &&& ~~~7 := by cases width <;> rfl
  rw [address] at stored
  simpa only [sourceValue] using stored

/-- A retiring narrow store writes the doubleword obtained by splicing its source
into the loaded shared word, from a state with unchanged memory and MMU setup.
For example, SH at address ten splices two bytes into the word at eight.
This covers both RAM and the I/O window at Jolt `ff6fc6568`:
`crates/jolt-program/src/expand/memory/shared.rs` (`expand_narrow_store`).
The primitive inversion is a candidate to move into JoltBytecode. -/
theorem laneStore_store_of_run (width : AccessWidth) (rs1 rs2 : regidx)
    (imm : BitVec 64) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (runs : Program.Run (StoreProgramBlocks.laneStoreProgram width rs1 rs2 imm) pre post) :
    (sourceValue (.xreg rs1) pre + imm) &&& LoadFamily.alignmentMask width = 0 ∧
    ∃ middle result,
      middle.sail = pre.sail ∧ middle.jolt_device = pre.jolt_device ∧
      middle.codeRegion = pre.codeRegion ∧
      Mmu.store_doubleword ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7)
        (StoreProgramBlocks.fusedSpliceValue width
          (Mmu.ram_doubleword pre.sail.mem
            ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7).toNat)
          (sourceValue (.xreg rs2) pre) (sourceValue (.xreg rs1) pre + imm)) middle =
        .ok result post := by
  rw [(storeRunHelper% laneStoreProgram_rows)] at runs
  obtain ⟨loaded, loadRun, restRun⟩ := execProgram_append_succeeds_inv _ _ pre post runs
  obtain ⟨loaded', rowRun, doneRun⟩ := execProgram_instr_run_retire_inv _ _ pre loaded loadRun
  have loadedEq : loaded' = loaded := by
    simpa only [execProgram_done, EStateM.run, pure, EStateM.pure,
      EStateM.Result.ok.injEq, true_and] using doneRun
  subst loaded'
  obtain ⟨aligned, loadedShape⟩ := floorLoad_write width rs1 imm pre loaded rowRun
  subst loaded
  obtain ⟨middle, spliceRun, sailSame, value, deviceSame⟩ :=
    (storeRunHelper% fusedSpliceBlock) width 40 41 (by decide)
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
      rs1 rs2 imm _ _ (stateAfterVRegWrite pre 40 _)
      (by simpa only [stateAfterVRegWrite] using baseRead)
      (by simpa only [stateAfterVRegWrite] using valueRead)
  obtain ⟨actual, actualRun, storeRun⟩ := execProgram_append_succeeds_inv _ _ _ post restRun
  have actualEq : actual = middle := (EStateM.Result.ok.inj (actualRun.symm.trans spliceRun)).2
  subst actual
  obtain ⟨stored, rowStore, doneStore⟩ := execProgram_instr_run_retire_inv _ _ middle post storeRun
  have storedEq : stored = post := by
    simpa only [execProgram_done, EStateM.run, pure, EStateM.pure,
      EStateM.Result.ok.injEq, true_and] using doneStore
  subst stored
  obtain ⟨result, stored⟩ := floorStore_store width rs1 imm middle post rowStore
  have sailEq : middle.sail = pre.sail := sailSame
  have sourceEq : sourceValue (.xreg rs1) middle = sourceValue (.xreg rs1) pre := by
    cases rs1 <;> simp only [sourceValue, sailEq]
  rw [sourceEq, value] at stored
  refine ⟨aligned, middle, result, sailEq, deviceSame, ?_, ?_⟩
  · simpa only [stateAfterVRegWrite] using JoltIOSetupFrame.codeRegion_of_program_run spliceRun
  · simpa only [stateAfterVRegWrite, ite_true] using stored

/-- A retiring narrow RAM store supplies the guard for its actual merged word.
For example, an SH into protected code passes only if its two bytes stay equal.
The guard is for eight bytes because the expansion stores the containing word;
untouched lanes retain the word loaded from shared memory.
Jolt at `ff6fc6568`: `Mmu::trace_store`, `assert_write_protected_store` and
`expand_narrow_store`. -/
theorem laneStore_ram_guard (width : AccessWidth) (rs1 rs2 : regidx)
    (imm : BitVec 64) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7).toNat)
    (runs : Program.Run (StoreProgramBlocks.laneStoreProgram width rs1 rs2 imm) pre post) :
    (sourceValue (.xreg rs1) pre + imm) &&& LoadFamily.alignmentMask width = 0 ∧
    Assumptions.JoltRamStoreOk ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7) pre
      (StoreProgramBlocks.fusedSpliceValue width
        (Mmu.ram_doubleword pre.sail.mem
          ((sourceValue (.xreg rs1) pre + imm) &&& ~~~7).toNat)
        (sourceValue (.xreg rs2) pre) (sourceValue (.xreg rs1) pre + imm)) 8 := by
  obtain ⟨aligned, middle, result, sailSame, deviceSame, codeSame, stored⟩ :=
    laneStore_store_of_run width rs1 rs2 imm pre post baseRead valueRead runs
  have guard := ramStore_guard_of_run _ _ middle post result inRam stored
  refine ⟨aligned, ?_, ?_⟩
  · simpa only [deviceSame] using guard.below_backing_end
  · simpa only [Mmu.protected_store_ok, Mmu.protected_byte, sailSame, deviceSame,
      codeSame] using guard.preserves_protected

/-- The source-store bundle's canonical value is accepted after a retiring narrow store.
For example, SH supplies width two but the checked row writes all eight merged bytes.
The alignment fact comes from the executed floor load, not a new caller premise.
Jolt at `ff6fc6568`: `expand_narrow_store` and `Mmu::assert_write_protected_store`. -/
theorem laneStore_bundle_guard (width : AccessWidth) (rs1 rs2 : regidx)
    (imm : BitVec 12) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤
      (compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm).toNat)
    (runs : Program.Run (StoreProgramBlocks.laneStoreProgram width rs1 rs2
      (sign_extend (m := 64) imm)) pre post) :
    Assumptions.JoltRamStoreOk
      (compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm) pre
      (storeDwordValue (narrowStoreBytes width)
        (load_effective_address (sourceValue (.xreg rs1) pre) imm)
        (Mmu.ram_doubleword pre.sail.mem
          (compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm).toNat)
        (sourceValue (.xreg rs2) pre)) 8 := by
  obtain ⟨aligned, guard⟩ := laneStore_ram_guard width rs1 rs2
    (sign_extend (m := 64) imm) pre post baseRead valueRead inRam runs
  let ea := load_effective_address (sourceValue (.xreg rs1) pre) imm
  let base := compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm
  let original := Mmu.ram_doubleword pre.sail.mem base.toNat
  let value := sourceValue (.xreg rs2) pre
  have splice : StoreProgramBlocks.fusedSpliceValue width original value ea =
      storeDwordValue (narrowStoreBytes width)
        ea original value := by
    cases width
    · exact StoreSplice.fusedByteSplice_eq original value ea base
        (StoreSplice.byteStoreFacts_of_effective_address _ imm)
    · exact StoreSplice.fusedHalfwordSplice_eq original value ea base
        (StoreSplice.halfwordStoreFacts_of_effective_address _ imm aligned)
    · exact StoreSplice.fusedWordSplice_eq original value ea base
        (StoreSplice.wordStoreFacts_of_effective_address _ imm aligned)
  change Assumptions.JoltRamStoreOk base pre
    (StoreProgramBlocks.fusedSpliceValue width original value ea) 8 at guard
  rw [splice] at guard
  exact guard

/-- A retiring native SD supplies acceptance of its full source value.
For example, an aligned same-value code store passes the protected-byte check.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`store_doubleword`). -/
theorem nativeStore_ram_guard (rs1 rs2 : regidx) (imm : BitVec 12)
    (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤
      (compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm).toNat)
    (runs : execInstr (.SD (.xreg rs1) (.xreg rs2) (sign_extend (m := 64) imm)) pre =
      .ok RETIRE_SUCCESS post) :
    Assumptions.JoltRamStoreOk
      (compute_aligned_dword_base_address (sourceValue (.xreg rs1) pre) imm) pre
      (sourceValue (.xreg rs2) pre) 8 := by
  let instruction := Instr.SD (.xreg rs1) (.xreg rs2) (sign_extend (m := 64) imm)
  have row : StoreRow instruction .double (.xreg rs1) (.xreg rs2)
      (sign_extend (m := 64) imm) := ⟨.E_SAMO_Addr_Align (), rfl⟩
  obtain ⟨aligned, result, stored⟩ := row.aligned_store_of_run 0 () pre post (by
    rw [withRuntimeAdvice_eq_of_noAdvice instruction () row.metadata.noAdvice,
      execWithTapeAnswer_of_ne _ 0 row.access.not_tape]
    exact runs)
  have cleared := BitVec.and_not_eq_self_of_and_eq_zero
    (sourceValue (.xreg rs1) pre + sign_extend (m := 64) imm) 7 aligned
  change RAM_START_ADDRESS ≤
    ((sourceValue (.xreg rs1) pre + sign_extend (m := 64) imm) &&& ~~~7).toNat at inRam
  change Assumptions.JoltRamStoreOk
    ((sourceValue (.xreg rs1) pre + sign_extend (m := 64) imm) &&& ~~~7) pre _ _
  rw [cleared] at inRam ⊢
  exact ramStore_guard_of_run _ _ pre post result inRam stored

end WholeRun
