import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionFrame

open LeanRV64D

/-
Every Jolt ISA instruction leaves the device's memory layout and the code guard
unchanged. Jolt's tracer fixes the layout in `create_emulator` and the code guard
in `Mmu::protect_code`, and no instruction updates either; stores change only memory.
See `tracer/src/emulator/mmu.rs` (`store_raw`, `store_doubleword`) at Jolt `504dd78a2`.
Based on Quang Dao's version in PR #73.
-/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltIOSetupFrame

open JoltISA

/-- The device setup Jolt's tracer fixes for a run: its memory layout.
For example, storing an output byte leaves this layout unchanged.
Input and advice bytes live in memory, not in the device. -/
structure Same (a b : JoltDevice) : Prop where
  layout : b.memory_layout = a.memory_layout

/-- Setup agrees with itself; for example, a load leaves the layout unchanged. -/
theorem Same.refl (a : JoltDevice) : Same a a := ⟨rfl⟩

/-- Compose setup agreement; for example, two consecutive stores keep the layout. -/
theorem Same.trans {a b c : JoltDevice} (hab : Same a b) (hbc : Same b c) : Same a c :=
  ⟨hbc.layout.trans hab.layout⟩

/-- Setup preservation for a computation; for example, every row preserves layout. -/
def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  StatePreservation.Preserves (fun s t => Same s.jolt_device t.jolt_device) m

/-- Static MMU setup agrees across two states: the layout and the code guard.
For example, a store changes memory while keeping both. -/
def SetupSame (s t : SailJoltState) : Prop :=
  t.jolt_device.memory_layout = s.jolt_device.memory_layout ∧ t.code_guard = s.code_guard

/-- Compose unchanged MMU setup across fragments.
For example, a load followed by an arithmetic row keeps the same code guard. -/
theorem SetupSame.trans {s t u : SailJoltState} (hst : SetupSame s t)
    (htu : SetupSame t u) : SetupSame s u :=
  ⟨htu.1.trans hst.1, htu.2.trans hst.2⟩

private theorem setup_refl (s : SailJoltState) : SetupSame s s := ⟨rfl, rfl⟩

private theorem setup_trans (s t u : SailJoltState) (h : SetupSame s t) (h' : SetupSame t u) :
    SetupSame s u := h.trans h'

/-- A successful doubleword store changes only memory, so it keeps the static MMU setup.
For example, a store into an output byte keeps the layout and the code guard. -/
theorem store_doubleword_setup (address value : BitVec 64) :
    StatePreservation.Preserves SetupSame (Mmu.store_doubleword address value) := by
  intro s t v h
  simp only [Mmu.store_doubleword] at h
  repeat' split at h
  all_goals first
    | (cases h; exact setup_refl _)
    | (rename_i heq
       cases h
       exact InstructionFrame.storeFold_rule_of_step _ value s _
         (fun _ _ _ _ before stored => setup_trans _ _ _ before
           (InstructionFrame.storeRaw_rule (relation := SetupSame)
             (fun _ _ => setup_refl _) (fun _ _ _ _ _ => setup_refl _) _ _ _ _ stored))
         (some s) (fun s1 hs1 => by cases hs1; exact setup_refl _) _ heq)
    | cases h

/-- Every row preserves the static MMU setup, including both halt kinds.
For example, a panic halt records its kind but keeps the code guard. -/
theorem execInstr_setup (instr : Instr) :
    StatePreservation.Preserves SetupSame (execInstr instr) :=
  InstructionFrame.execInstr_rule
    { refl := setup_refl
      trans := setup_trans
      sail := fun _ _ _ => setup_refl _
      vreg := fun _ _ _ => setup_refl _
      store := store_doubleword_setup
      halt := fun _ _ => setup_refl _
      append := fun _ _ => setup_refl _ }
    instr (fun _ _ _ _ _ _ _ => setup_refl _)

/-- Every program preserves the static MMU setup; for example, an AMO prefix. -/
theorem execProgram_setup (program : Program) :
    StatePreservation.Preserves SetupSame (execProgram program) := by
  induction program with
  | done result => exact StatePreservation.pure_rule setup_refl _
  | instr instr rest ih =>
    simp only [execProgram]
    refine StatePreservation.bind_rule setup_trans (execInstr_setup instr) (fun result => ?_)
    split
    · exact ih
    · exact StatePreservation.pure_rule setup_refl _

/-- Every row preserves the device layout; for example, an output store. -/
theorem execInstr_rule (instr : Instr) : Preserves (execInstr instr) :=
  fun _ _ _ h => ⟨(execInstr_setup instr _ _ _ h).1⟩

/-- Every row program preserves the device layout; for example, a narrow store. -/
theorem execProgram_rule (program : Program) : Preserves (execProgram program) :=
  fun _ _ _ h => ⟨(execProgram_setup program _ _ _ h).1⟩

/-- Recover the code guard after a successful expansion; for example, an AMO prefix. -/
theorem code_guard_of_program_run {program : Program} {s t : SailJoltState} {r : ExecutionResult}
    (h : execProgram program s = .ok r t) : t.code_guard = s.code_guard :=
  (execProgram_setup program s t r h).2

/-- Recover static MMU setup from a prefix whose continuation can be chosen freely.
For example, choosing a successful empty tail certifies a narrow-store prefix.
Based on Quang Dao's version in PR #73. -/
theorem setup_of_tail_run {step : Program → Program} {s t : SailJoltState}
    (h : ∀ tail, (execProgram (step tail)).run s = (execProgram tail).run t) :
    SetupSame s t :=
  execProgram_setup _ s t _ (h (.done RETIRE_SUCCESS))

/-- Recover layout agreement from a program run; for example, an AMO prefix. -/
theorem layout_of_tail_run {step : Program → Program} {s t : SailJoltState}
    (h : ∀ tail, (execProgram (step tail)).run s = (execProgram tail).run t) :
    t.jolt_device.memory_layout = s.jolt_device.memory_layout :=
  (execProgram_rule _ s t _ (h (.done RETIRE_SUCCESS))).layout

/-- Recover layout agreement from a row run; for example, a load. -/
theorem layout_of_instr_run {instr : Instr} {s t : SailJoltState} {r : ExecutionResult}
    (h : (execInstr instr).run s = .ok r t) :
    t.jolt_device.memory_layout = s.jolt_device.memory_layout :=
  (execInstr_rule instr s t r h).layout

end JoltIOSetupFrame
