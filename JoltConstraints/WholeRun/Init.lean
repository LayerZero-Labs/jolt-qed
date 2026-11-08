import JoltConstraints.WholeRun.Relation
import JoltConstraints.execution_facts
import JoltConstraints.layout_facts
import JoltConstraints.Completeness.Helpers.VerifierSizes
import JoltConstraints.Completeness.Helpers.RamOutputProofHelpers

/-!
# The start of a run, and its outputs

The whole-run theorem starts Sail from `sailInit jt`, where `jt` is Jolt's
initial state. This file proves that the two are related (`related_sailInit`)
and that related states report the same outputs and panic flag
(`Related.outputs`, `Related.panic_flag`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

open JoltISA

/-- Inserting `f a` at each address `a` of `[lo, lo + n)`. -/
theorem foldl_insert_range_get? (lo n : Nat) (f : Nat → BitVec 8)
    (base : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    ((List.range n).foldl (fun mem k => mem.insert (lo + k) (f (lo + k))) base).get? a =
      if lo ≤ a ∧ a < lo + n then some (f a) else base.get? a := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, ← Std.ExtHashMap.get?_eq_getElem?, ih]
    by_cases h : lo + n = a
    · subst h
      simp
    · simp only [beq_iff_eq, h, ↓reduceIte]
      by_cases hin : lo ≤ a ∧ a < lo + n
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- Sail's initial memory: `sailByte` (zero at the flag words) on `[memLow,
memHigh)`, Jolt's memory elsewhere. -/
theorem sailInitMem_get? (jt : SailJoltState) (a : Nat) :
    (sailInitMem jt).get? a =
      if memLow jt.jolt_device ≤ a ∧ a < memHigh jt.jolt_device then
        some (if IsFlagWord jt.jolt_device a then 0 else sailByte jt a)
      else jt.sail.mem.get? a := by
  unfold sailInitMem
  rw [foldl_insert_range_get? (memLow jt.jolt_device) _
    (fun a => if IsFlagWord jt.jolt_device a then 0 else sailByte jt a)]
  by_cases h : memLow jt.jolt_device ≤ a ∧ a < memHigh jt.jolt_device
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- The layout facts the relation uses, from a layout `MemoryLayout.new` built. -/
theorem layout_facts {layout : MemoryLayout} {config : MemoryConfig}
    (built : MemoryLayout.new config = some layout) :
    layout.get_lowest_address.toNat ≤ layout.output_start.toNat ∧
    layout.panic.toNat = layout.output_start.toNat + layout.max_output_size.toNat ∧
    layout.io_end.toNat = layout.panic.toNat + 16 ∧
    layout.io_end.toNat ≤ RAM_START_ADDRESS := by
  obtain ⟨h1, h2, _, _, _⟩ := new_io_ordered config layout built
  obtain ⟨g1, _, g3, g4, g5⟩ := new_io_geometry config layout built
  omega

/-- What Jolt's initial state is: `init_state` at the entry address, with the
instance's layout and an empty, unpanicked device. -/
theorem initial_state_spec {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    ∃ (ram : Array (BitVec 8)) (device : JoltDevice) (tape : JoltAdviceTape),
      jt = init_state joltInstance.program.entry_address ram device tape := by
  unfold JoltInstance.initial_state at built
  cases layoutResult : joltInstance.memory_layout with
  | none =>
    simp only [layoutResult, bind, Option.bind] at built
    cases built
  | some layout =>
    simp only [layoutResult, bind, Option.bind] at built
    repeat' split at built
    all_goals first
      | (cases built; exact ⟨_, _, _, rfl⟩)
      | cases built

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

/-- `sailRegs` keeps the step invariant of Jolt's Sail state. -/
theorem stepInvariant_sailRegs (jt : SailJoltState) (hinv : Step.StepInvariant jt.sail)
    (pc m : BitVec 64) (inc : Bool) : Step.StepInvariant (sailRegs jt pc m inc) :=
  ((((stepInvariant_systemProject jt hinv).setReg _ _ (by simp [Step.invariantReg])).setReg _ _
    (by simp [Step.invariantReg])).setReg _ _ (by simp [Step.invariantReg])).setReg _ _
    (by simp [Step.invariantReg])

/-- The step invariant reads registers only. -/
theorem stepInvariant_withMem {s : SailState} (hinv : Step.StepInvariant s)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Step.StepInvariant { s with mem := mem } :=
  hinv.of_agree (fun _ _ => rfl) (fun r => ⟨(hinv.present r).exists_value⟩)

/-- Outside `PC`, the retired-instruction counter, `pma_regions` and the overlaid
CSRs, `sailRegs` reads Jolt's Sail registers. -/
theorem sailRegs_get?_other (jt : SailJoltState) (pc m : BitVec 64) (inc : Bool) {r : Register}
    (hpc : Register.PC ≠ r) (hm : Register.minstret ≠ r) (hinc : Register.minstret_increment ≠ r)
    (hpma : Register.pma_regions ≠ r) (ho : ¬ Step.Overlaid r) :
    (sailRegs jt pc m inc).regs.get? r = jt.sail.regs.get? r := by
  unfold sailRegs
  rw [Step.setReg_get?_ne _ _ hpma, Step.setReg_get?_ne _ _ hinc, Step.setReg_get?_ne _ _ hm,
    Step.setReg_get?_ne _ _ hpc, Step.systemProject_get?_of_not_overlaid jt ho]

/-- **The run starts related.** Sail's initial state `sailInit jt` is related to
Jolt's initial state `jt`. -/
theorem related_sailInit {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) :
    Related jt (sailInit jt) := by
  obtain ⟨ram, device, tape, hjt⟩ := initial_state_spec joltInstance privateInputs jt built
  have hreg : ∀ r, jt.sail.regs.get? r =
      some (initialRegisterValue joltInstance.program.entry_address ram.size r) := by
    subst hjt; exact init_state_register _ _ _ _ _
  have hinv0 : Step.StepInvariant jt.sail := by
    subst hjt; exact stepInvariant_init_state _ _ _ _
  have hpanic : jt.jolt_device.panic = false := by subst hjt; rfl
  have houts : jt.jolt_device.outputs = #[] := by subst hjt; rfl
  have hlayout : ∃ config, MemoryLayout.new config = some jt.jolt_device.memory_layout := by
    have h := (initial_state_device joltInstance privateInputs jt built).1
    unfold JoltInstance.memory_layout at h
    exact ⟨_, h⟩
  obtain ⟨config, hbuilt⟩ := hlayout
  obtain ⟨hlow, hpw, hio, hram⟩ := layout_facts hbuilt
  obtain ⟨_, _, hheap⟩ := new_heap_end_ge config _ hbuilt
  have hmem : (sailInit jt).mem = sailInitMem jt := rfl
  refine
    { regs := ⟨_, 0, false, hreg Register.nextPC, ?_⟩
      inv := stepInvariant_withMem (stepInvariant_sailRegs jt hinv0 _ _ _) _
      htif := ?_
      ram := fun a ha => ?_
      present := fun a h1 h2 => ?_
      io := fun a h1 h2 hflag => ?_
      panic := ?_
      layout := ⟨config, hbuilt⟩
      outputs_size := by rw [houts]; exact Nat.zero_le _ }
  · show (sailRegs jt ((jt.sail.regs.get? Register.nextPC).getD 0) 0 false).regs = _
    rw [hreg Register.nextPC]
    rfl
  · show (sailRegs jt _ 0 false).regs.get? _ = _
    rw [sailRegs_get?_other jt _ _ _ (by decide) (by decide) (by decide) (by decide)
      (by simp [Step.Overlaid]), hreg]
    rfl
  · have hflag : IsFlagWord jt.jolt_device a = false := by
      simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    unfold Mmu.ram_byte
    rw [hmem, sailInitMem_get?]
    split
    · simp only [hflag, sailByte, ite_eq_left ha, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
      rfl
    · rfl
  · rw [hmem, sailInitMem_get?, ite_eq_left ⟨h1, h2⟩]
    exact ⟨_, rfl⟩
  · have hhigh : a < memHigh jt.jolt_device := by unfold memHigh; omega
    rw [hmem, sailInitMem_get?, ite_eq_left ⟨h1, hhigh⟩]
    simp only [hflag, sailByte, ite_eq_right (Nat.not_le.mpr h2), Bool.false_eq_true, ↓reduceIte]
  · have hbyte : ∀ i, i < 8 →
        (sailInitMem jt).get? (jt.jolt_device.memory_layout.panic.toNat + i) = some 0 := by
      intro i hi
      have hflag : IsFlagWord jt.jolt_device
          (jt.jolt_device.memory_layout.panic.toNat + i) = true := by
        simp only [IsFlagWord, Bool.and_eq_true, decide_eq_true_eq]
        omega
      rw [sailInitMem_get?, ite_eq_left ⟨by unfold memLow; omega, by unfold memHigh; omega⟩]
      simp only [hflag, ↓reduceIte]
    have hzero : sailPanicWord jt.jolt_device (sailInit jt) = 0 := by
      have h0 := hbyte 0 (by omega)
      rw [Nat.add_zero] at h0
      unfold sailPanicWord read_doubleword?
      rw [hmem, h0, hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega),
        hbyte 4 (by omega), hbyte 5 (by omega), hbyte 6 (by omega), hbyte 7 (by omega)]
      rfl
    rw [hpanic, hzero]
    simp

/-- `MemoryLayout.new` ends the input region where the output region starts. -/
theorem new_input_end_eq_output_start {config : MemoryConfig} {layout : MemoryLayout}
    (built : MemoryLayout.new config = some layout) : layout.input_end = layout.output_start := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  rfl

/-- Jolt's device reads the output byte at an output address, zero past the
buffer. -/
theorem load?_output (device : JoltDevice) {config : MemoryConfig}
    (built : MemoryLayout.new config = some device.memory_layout) (k : Nat)
    (hk : k < device.memory_layout.max_output_size.toNat) :
    device.load? (device.memory_layout.output_start.toNat + k) =
      some (device.outputs[k]?.getD 0) := by
  obtain ⟨_, _, _, _, ht, hu, _, _, _, hin⟩ := new_advice_regions config _ built
  have hie := congrArg BitVec.toNat (new_input_end_eq_output_start built)
  obtain ⟨hpw, _, hterm, _, _⟩ := new_io_geometry config _ built
  obtain ⟨_, hinOut, _, _, _⟩ := new_io_ordered config _ built
  unfold JoltDevice.load? JoltDevice.is_panic JoltDevice.is_termination JoltDevice.is_input
    JoltDevice.is_trusted_advice JoltDevice.is_untrusted_advice JoltDevice.is_output
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> first
    | omega
    | simp only [Nat.add_sub_cancel_left]

/-- **Related states report the same outputs.** The output bytes in Sail's
memory, trimmed of trailing zeros, are Jolt's output buffer, trimmed. -/
theorem Related.outputs {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    trimTrailingZeros (sailOutputs jt.jolt_device s) = trimTrailingZeros jt.jolt_device.outputs := by
  obtain ⟨config, built⟩ := h.layout
  obtain ⟨hlow, hpw, hio, hram⟩ := layout_facts built
  apply JoltConstraints.trimTrailingZeros_of_padded_eq _ _
    jt.jolt_device.memory_layout.max_output_size.toNat
  · simp [sailOutputs]
  · exact h.outputs_size
  · intro i hi
    have hflag : IsFlagWord jt.jolt_device
        (jt.jolt_device.memory_layout.output_start.toNat + i) = false := by
      simp only [IsFlagWord, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    have hget := h.io _ (by unfold memLow; omega) (by omega) hflag
    rw [load?_output _ built i hi, Std.ExtHashMap.get?_eq_getElem?] at hget
    simp [sailOutputs, hi, hget]

end WholeRun
