import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionFrame

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D.Functions

set_option autoImplicit false

namespace JoltIOSetupFrame
open JoltISA

/-- The non-memory setup fixed by Jolt's tracer: its layout.
For example, storing an output or executing EBREAK leaves this layout unchanged.
Input/advice bytes now belong to shared memory and use protection checks. -/
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

/-- Successful byte stores update memory rather than the device.
For example, an output store preserves the layout and panic claim. -/
theorem store_raw_same (s s' : SailJoltState) (ea : Nat) (value : BitVec 8)
    (h : Mmu.store_raw? s ea value = some s') : Same s.jolt_device s'.jolt_device := by
  exact InstructionFrame.storeRaw_rule
    (relation := fun s t => Same s.jolt_device t.jolt_device)
    (fun _ _ => ⟨rfl⟩) (fun _ _ _ _ _ => ⟨rfl⟩) s s' ea value h

/-- Static MMU setup agrees across two states: layout and the code-word interval.
For example, a store changes memory while preserving both components. -/
def SetupSame (s t : SailJoltState) : Prop :=
  t.jolt_device.memory_layout = s.jolt_device.memory_layout ∧ t.codeRegion = s.codeRegion

/-- Compose unchanged MMU setup across fragments.
For example, a load followed by an arithmetic row keeps the same code interval. -/
theorem SetupSame.trans {s t u : SailJoltState} (hst : SetupSame s t)
    (htu : SetupSame t u) : SetupSame s u :=
  ⟨htu.1.trans hst.1, htu.2.trans hst.2⟩

private theorem setup_refl (s : SailJoltState) : SetupSame s s := ⟨rfl, rfl⟩
private theorem setup_trans (s t u : SailJoltState) (h : SetupSame s t) (h' : SetupSame t u) :
    SetupSame s u := ⟨h'.1.trans h.1, h'.2.trans h.2⟩

/-- Every row preserves the static MMU setup, including both halt kinds.
For example, a panic halt changes the claim but keeps its code guard. -/
theorem execInstr_setup (instr : Instr) : StatePreservation.Preserves SetupSame (execInstr instr) :=
  InstructionFrame.execInstr_rule
    { refl := setup_refl
      trans := setup_trans
      sail := fun _ _ _ => ⟨rfl, rfl⟩
      vreg := fun _ _ _ => ⟨rfl, rfl⟩
      store := fun addr value s t result h =>
        let frame := Mmu.store_doubleword_protected addr value s t result h
        ⟨frame.layout, frame.code⟩
      halt := fun _ _ => ⟨rfl, rfl⟩
      append := fun _ _ => ⟨rfl, rfl⟩ }
    instr (fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩)

/-- Every program preserves static MMU setup; for example, an AMO prefix. -/
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

/-- Every successful row preserves protected shared-memory bytes and MMU setup.
For example, output writes can change memory, while input and advice bytes keep their values. -/
theorem execInstr_memory (instr : Instr) :
    StatePreservation.Preserves Mmu.ProtectedMemory (execInstr instr) :=
  InstructionFrame.execInstr_rule
    { refl := Mmu.ProtectedMemory.refl
      trans := fun _ _ _ h h' => h.trans h'
      sail := fun _ _ hm => ⟨rfl, rfl, fun a _ => by rw [hm]⟩
      vreg := fun _ _ _ => ⟨rfl, rfl, fun _ _ => rfl⟩
      store := Mmu.store_doubleword_protected
      halt := fun _ _ => ⟨rfl, rfl, fun _ _ => rfl⟩
      append := fun _ _ => ⟨rfl, rfl, fun _ _ => rfl⟩ }
    instr (fun _ _ _ _ _ _ _ => ⟨rfl, rfl, fun _ _ => rfl⟩)

/-- Every successful expansion preserves the original protected bytes in shared memory.
For example, an AMO can store the same code word but cannot change it. -/
theorem execProgram_memory (program : Program) :
    StatePreservation.Preserves Mmu.ProtectedMemory (execProgram program) := by
  induction program with
  | done result => exact StatePreservation.pure_rule Mmu.ProtectedMemory.refl _
  | instr instr rest ih =>
    simp only [execProgram]
    refine StatePreservation.bind_rule (fun _ _ _ h h' => h.trans h')
      (execInstr_memory instr) (fun result => ?_)
    split
    · exact ih
    · exact StatePreservation.pure_rule Mmu.ProtectedMemory.refl _

/-- Every row preserves the device layout; for example, an output store. -/
theorem execInstr_rule (instr : Instr) : Preserves (execInstr instr) :=
  fun _ _ _ h => ⟨(execInstr_setup instr _ _ _ h).1⟩

/-- Every row program preserves the device layout; for example, a narrow store. -/
theorem execProgram_rule (program : Program) : Preserves (execProgram program) :=
  fun _ _ _ h => ⟨(execProgram_setup program _ _ _ h).1⟩

/-- Recover the code interval after a successful instruction, for example a load. -/
theorem codeRegion_of_instr_run {instr : Instr} {s t : SailJoltState} {r : ExecutionResult}
    (h : execInstr instr s = .ok r t) : t.codeRegion = s.codeRegion :=
  (execInstr_setup instr s t r h).2

/-- Recover the code interval after a successful expansion, for example an AMO prefix. -/
theorem codeRegion_of_program_run {program : Program} {s t : SailJoltState} {r : ExecutionResult}
    (h : execProgram program s = .ok r t) : t.codeRegion = s.codeRegion :=
  (execProgram_setup program s t r h).2

/-- Recover static MMU setup from a prefix whose continuation can be chosen freely.
For example, choosing a successful empty tail certifies a narrow-store prefix. -/
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

namespace JoltISA

/-- A halt writes the advanced PC to its temporary, restores the source PC as nextPC,
and records its kind without changing shared memory.
For example, success uses temporary v40 and sets the panic claim to false. -/
theorem execHalt_vreg_run (kind : JoltHaltKind) (dst : VReg) (s : SailJoltState)
    (link address : BitVec 64) (hw : WritableVReg dst)
    (hlink : LeanRV64D.readReg Register.nextPC s.sail = .ok link s.sail)
    (hpc : LeanRV64D.readReg Register.PC s.sail = .ok address s.sail) :
    execHalt kind (.vreg dst) s = .ok RETIRE_SUCCESS
      (recordHalt kind { s with
        vregs := fun r => if r = dst then link else s.vregs r
        sail := { s.sail with regs := s.sail.regs.insert Register.nextPC address } }) := by
  have hdst : ¬ dst.toNat < 32 := hw
  simp [execHalt, liftSail, hlink, hpc, writeDst, writeVReg, WritableVReg,
    LeanRV64D.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg, hdst,
    bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA
