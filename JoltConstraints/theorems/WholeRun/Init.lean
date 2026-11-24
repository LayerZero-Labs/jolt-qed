import JoltConstraints.theorems.WholeRun.Relation
import JoltConstraints.theorems.execution_facts
import JoltConstraints.theorems.layout_facts
import JoltConstraints.theorems.SharedMemoryInitialization

/-!
# The start of a run, and its outputs

The whole-run theorem starts Sail from `sailInit jt`, where `jt` is Jolt's
initial state. This file proves that the two are related (`related_sailInit`)
and that related states extract identical output bytes (`Related.outputs`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

open JoltISA JoltConstraints

/-- Jolt's initial Sail state satisfies the step invariant. -/
theorem stepInvariant_init_state (entry : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (tape : JoltAdviceTape) :
    Step.StepInvariant (init_state entry ram device tape).sail where
  present r := ⟨Option.isSome_iff_exists.mp (init_state_registers_present entry ram device tape {} r)⟩
  active := by rw [init_state_register]; rfl
  machine := by rw [init_state_register]; rfl
  mie_zero := by rw [init_state_register]; rfl
  mideleg_zero := by rw [init_state_register]; rfl
  misa_c := ⟨_, init_state_register .., by
    show _get_Misa_C (0x800000008014312f : BitVec 64) = 1#1
    decide⟩
  elp_none := by rw [init_state_register]; rfl

/-- The CSR overlay keeps the step invariant. -/
theorem stepInvariant_systemProject (js : SailJoltState) (hinv : Step.StepInvariant js.sail) :
    Step.StepInvariant (System.systemProject js) := by
  refine hinv.of_agree (fun r hr => ?_) (fun r => ?_)
  · exact Step.systemProject_get?_of_not_overlaid js (Step.not_overlaid_of_invariantReg hr)
  · by_cases ho : Step.Overlaid r
    · exact Step.systemProject_overlaid_present js ho
    · obtain ⟨v, hv⟩ := (hinv.present r).exists_value
      exact ⟨v, by rw [Step.systemProject_get?_of_not_overlaid js ho]; exact hv⟩

/-- Replacing `misa` by a value with the C bit set keeps the step invariant. -/
theorem stepInvariant_setMisa {s : SailState} (hinv : Step.StepInvariant s)
    (v : RegisterType Register.misa) (hv : _get_Misa_C v = 1#1) :
    Step.StepInvariant (Step.setReg s Register.misa v) where
  present := Step.setReg_present s _ v hinv.present
  active := by rw [Step.setReg_get?_ne s v (by decide)]; exact hinv.active
  machine := by rw [Step.setReg_get?_ne s v (by decide)]; exact hinv.machine
  mie_zero := by rw [Step.setReg_get?_ne s v (by decide)]; exact hinv.mie_zero
  mideleg_zero := by rw [Step.setReg_get?_ne s v (by decide)]; exact hinv.mideleg_zero
  misa_c := ⟨v, Std.ExtDHashMap.get?_insert_self, hv⟩
  elp_none := by rw [Step.setReg_get?_ne s v (by decide)]; exact hinv.elp_none

/-- `sailRegs` keeps the step invariant of Jolt's Sail state. -/
theorem stepInvariant_sailRegs (jt : SailJoltState) (hinv : Step.StepInvariant jt.sail)
    (pc m : BitVec 64) (inc : Bool) : Step.StepInvariant (sailRegs jt pc m inc) :=
  stepInvariant_setMisa
    (((((stepInvariant_systemProject jt hinv).setReg _ _ (by simp [Step.invariantReg])).setReg _ _
      (by simp [Step.invariantReg])).setReg _ _ (by simp [Step.invariantReg])).setReg _ _
      (by simp [Step.invariantReg]))
    _ resetMisa_c

/-- The step invariant reads registers only. -/
theorem stepInvariant_withMem {s : SailState} (hinv : Step.StepInvariant s)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Step.StepInvariant { s with mem := mem } :=
  hinv.of_agree (fun _ _ => rfl) (fun r => ⟨(hinv.present r).exists_value⟩)

/-- Outside `PC`, the retired-instruction counter, `pma_regions`, `misa` and the overlaid
CSRs, `sailRegs` reads Jolt's Sail registers. -/
theorem sailRegs_get?_other (jt : SailJoltState) (pc m : BitVec 64) (inc : Bool) {r : Register}
    (hpc : Register.PC ≠ r) (hm : Register.minstret ≠ r) (hinc : Register.minstret_increment ≠ r)
    (hpma : Register.pma_regions ≠ r) (hmisa : Register.misa ≠ r) (ho : ¬ Step.Overlaid r) :
    (sailRegs jt pc m inc).regs.get? r = jt.sail.regs.get? r := by
  unfold sailRegs
  rw [Step.setReg_get?_ne _ _ hmisa, Step.setReg_get?_ne _ _ hpma, Step.setReg_get?_ne _ _ hinc, Step.setReg_get?_ne _ _ hm,
    Step.setReg_get?_ne _ _ hpc, Step.systemProject_get?_of_not_overlaid jt ho]

/-- Sail starts related to the initialized Jolt state by using exactly its
shared byte map.
For example, initialized input and advice bytes require no second I/O overlay. -/
theorem related_sailInit {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    Related jt (sailInit jt) := by
  obtain ⟨layout, layoutBuilt, _, _, _, initialized⟩ :=
    initial_state_build joltInstance privateInputs jt built
  obtain ⟨region, mem, _, memoryBuilt, shape⟩ :=
    JoltConstraints.initialState_shape _ _ _ _ _ _ initialized
  let ram := initialRam layout joltInstance.program.memory_init
  let device : JoltDevice := { panic := false, memory_layout := layout }
  let tape : JoltAdviceTape := { bytes := privateInputs.advice_tape, readPosition := 0 }
  have hreg : ∀ r, jt.sail.regs.get? r =
      some (initialRegisterValue joltInstance.program.entry_address ram.size r) := by
    rw [shape]
    exact init_state_register joltInstance.program.entry_address ram device tape {}
  have hinv0 : Step.StepInvariant jt.sail := by
    rw [shape]
    exact stepInvariant_withMem (stepInvariant_init_state _ _ _ _) mem
  have hlayout : ∃ config, MemoryLayout.new config = some jt.jolt_device.memory_layout := by
    have h := (initial_state_device joltInstance privateInputs jt built).1
    unfold JoltInstance.memory_layout at h
    exact ⟨_, h⟩
  refine
    { regs := ⟨_, 0, false, hreg Register.nextPC, ?_⟩
      inv := stepInvariant_sailRegs jt hinv0 _ _ _
      htif := ?_
      ram := fun _ => rfl
      present := ?_
      layout := hlayout }
  · show (sailRegs jt ((jt.sail.regs.get? Register.nextPC).getD 0) 0 false).regs = _
    rw [hreg Register.nextPC]
    rfl
  · show (sailRegs jt _ 0 false).regs.get? _ = _
    rw [sailRegs_get?_other jt _ _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp [Step.Overlaid]), hreg]
    rfl
  · intro a low high
    change ∃ byte, jt.sail.mem.get? a = some byte
    rw [shape] at low high ⊢
    change ∃ byte, mem.get? a = some byte
    apply Option.isSome_iff_exists.mp
    apply initialMem_present device (init_state joltInstance.program.entry_address ram device tape).sail.mem
      mem joltInstance.inputs joltInstance.trusted_advice privateInputs.untrusted_advice memoryBuilt a
    by_cases inRam : RAM_START_ADDRESS ≤ a
    · left
      have size := initialRam_size_eq_ram_size layout joltInstance.program.memory_init
        { joltInstance.memory_config with program_size := some joltInstance.program.program_size }
        layoutBuilt
      have inside : a - RAM_START_ADDRESS < ram.size := by
        change a < Mmu.ram_backing_end device at high
        simp only [Mmu.ram_backing_end, device] at high
        dsimp only [ram]
        rw [size]
        omega
      have byte := init_state_mem_get? joltInstance.program.entry_address ram device tape
        (a - RAM_START_ADDRESS)
      rw [show RAM_START_ADDRESS + (a - RAM_START_ADDRESS) = a by omega,
        Array.getElem?_eq_getElem inside] at byte
      rw [byte]
      rfl
    · right
      exact ⟨low, by omega⟩

/-- Related states extract identical output-capacity bytes from their shared
memory maps.
For example, they agree on both a written output byte and an untouched zero. -/
theorem Related.outputs {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    jt.jolt_device.outputsOf s.mem = jt.jolt_device.outputsOf jt.sail.mem := by
  unfold JoltDevice.outputsOf
  apply Array.map_congr_left
  intro k _
  exact h.ram _

end WholeRun
