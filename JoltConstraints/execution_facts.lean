/-
Facts about executing Jolt instructions that the old trace assumed per row. Each
one is proved from the instruction semantics in JoltBytecode.
-/
import JoltConstraints.honest_trace
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt
import Mathlib.Tactic.IntervalCases
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace SailUnchanged

-- A step that, when it succeeds, leaves the Sail state exactly as it found it.
def Preserves {Value : Type} (step : JoltMonad Value) : Prop :=
  ∀ (state after : SailJoltState) (value : Value),
    step state = .ok value after → after.sail = state.sail

theorem pure_rule {Value : Type} (value : Value) : Preserves (pure value) := by
  intro state after result runs
  cases runs
  rfl

-- Two steps that each keep the Sail state keep it when run one after the other.
theorem bind_rule {Value Next : Type} {first : JoltMonad Value} {next : Value → JoltMonad Next}
    (keepsFirst : Preserves first) (keepsNext : ∀ value, Preserves (next value)) :
    Preserves (first >>= next) := by
  intro state after result runs
  cases firstRun : first state with
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    cases runs
  | ok value middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    exact (keepsNext value middle after result runs).trans (keepsFirst state middle value firstRun)

-- Reading a register, real or virtual, changes nothing.
theorem read_rule (source : JoltISA.Src) : Preserves (JoltISA.readSrc source) := by
  intro state after value runs
  cases source with
  | vreg register =>
    simp only [JoltISA.readSrc_vreg, readVReg_run] at runs
    cases runs
    rfl
  | xreg register =>
    change liftSail (rX_bits register) state = .ok value after at runs
    unfold liftSail at runs
    cases readResult : rX_bits register state.sail with
    | error failure sail =>
      rw [readResult] at runs
      cases runs
    | ok readValue sail =>
      have same := rX_bits_pure register state.sail readValue sail readResult
      rw [readResult] at runs
      cases runs
      exact same

theorem get_rule : Preserves (get : JoltMonad SailJoltState) := by
  intro state after value runs
  cases runs
  rfl

theorem throw_rule {Value : Type} (failure : Error exception) :
    Preserves (throw failure : JoltMonad Value) := by
  intro state after value runs
  cases runs

-- Changing only the advice tape (or anything else outside Sail) keeps the Sail state.
theorem modify_rule (change : SailJoltState → SailJoltState)
    (keeps : ∀ state, (change state).sail = state.sail) :
    Preserves (modify change : JoltMonad Unit) := by
  intro state after value runs
  cases runs
  exact keeps state

-- A one-byte load changes nothing.
theorem load_rule (address : BitVec 64) : Preserves (JoltISA.Mmu.load address) := by
  intro state after value runs
  rw [JoltISA.Mmu.load_state runs]

-- Reading a run of bytes for a host call changes nothing in the Sail state.
theorem readHostBytes_rule (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Preserves (JoltISA.readHostBytes JoltISA.Mmu.load
      overflowChecks incrementAfterLast pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact pure_rule _
  | succ count ih =>
    dsimp only [JoltISA.readHostBytes]
    refine bind_rule (load_rule _) (fun result => ?_)
    cases result with
    | Err failure => exact pure_rule _
    | Ok byte =>
      split_ifs
      · exact bind_rule (throw_rule _) (fun _ => ih _ _)
      · exact bind_rule (pure_rule _) (fun _ => ih _ _)

end SailUnchanged

-- A HostIO call changes nothing in the Sail state: it only reads memory and may
-- append to the advice tape, which is not part of it.
theorem execHostIO_keeps_sail (state after : SailJoltState) (result : ExecutionResult)
    (runs : JoltISA.execHostIO state = .ok result after) :
    after.sail = state.sail := by
  have keeps : SailUnchanged.Preserves JoltISA.execHostIO := by
    unfold JoltISA.execHostIO JoltISA.execHostIOWith
    refine SailUnchanged.bind_rule SailUnchanged.get_rule (fun config => ?_)
    dsimp only
    split
    · exact SailUnchanged.pure_rule _
    · refine SailUnchanged.bind_rule (SailUnchanged.pure_rule _) (fun _ => ?_)
      refine SailUnchanged.bind_rule (SailUnchanged.read_rule _) (fun callId => ?_)
      repeat' first
        | exact SailUnchanged.readHostBytes_rule _ _ _ _ _
        | exact SailUnchanged.read_rule _
        | exact SailUnchanged.pure_rule _
        | exact SailUnchanged.throw_rule _
        | exact SailUnchanged.modify_rule _ (fun _ => rfl)
        | split
        | refine SailUnchanged.bind_rule ?_ (fun _ => ?_)
  exact keeps state after result runs

-- Every Sail register has a value in the register map.
def AllRegistersPresent (sail : SailState) : Prop :=
  ∀ register : Register, (sail.regs.get? register).isSome

-- Inserting a value for every register in a list leaves each of them in the map,
-- along with whatever was there before.
private theorem fold_insert_contains (value : (register : Register) → RegisterType register) :
    ∀ (registers : List Register) (start : Std.ExtDHashMap Register RegisterType)
      (register : Register),
      register ∈ registers ∨ start.contains register = true →
      (registers.foldl (fun map next => map.insert next (value next)) start).contains
        register = true := by
  intro registers
  induction registers with
  | nil =>
    intro start register present
    rcases present with member | inStart
    · exact absurd member List.not_mem_nil
    · exact inStart
  | cons head tail ih =>
    intro start register present
    rw [List.foldl_cons]
    apply ih
    rcases present with member | inStart
    · rcases List.mem_cons.mp member with isHead | inTail
      · right
        rw [isHead]
        exact Std.ExtDHashMap.contains_insert_self
      · left
        exact inTail
    · right
      rw [Std.ExtDHashMap.contains_insert, inStart, Bool.or_true]

-- The initial state puts every register in the map.
theorem init_state_registers_present (entryAddress : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (adviceTape : JoltAdviceTape) (hostIO : JoltHostIOConfig) :
    AllRegistersPresent (init_state entryAddress ram device adviceTape hostIO).sail := by
  intro register
  unfold init_state
  rw [Std.ExtDHashMap.isSome_get?_eq_contains]
  exact fold_insert_contains _ _ _ register
    (Or.inl (Finset.mem_toList.mpr (Finset.mem_univ register)))

-- Overwriting one register keeps every register present.
private theorem insert_keeps_present (regs : Std.ExtDHashMap Register RegisterType)
    (written : Register) (value : RegisterType written)
    (present : ∀ register, (regs.get? register).isSome) :
    ∀ register, ((regs.insert written value).get? register).isSome := by
  intro register
  rw [Std.ExtDHashMap.isSome_get?_eq_contains, Std.ExtDHashMap.contains_insert,
    ← Std.ExtDHashMap.isSome_get?_eq_contains, present register, Bool.or_true]

-- Sail's write to an integer register keeps every register present.
private theorem wX_update_regs_keeps_present (destination : regidx) (value : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType)
    (present : ∀ register, (regs.get? register).isSome) :
    ∀ register, ((wX_update_regs destination value regs).get? register).isSome := by
  intro register
  obtain ⟨index⟩ := destination
  have small : index.toNat < 32 := index.isLt
  unfold wX_update_regs
  dsimp only
  generalize index.toNat = number at small ⊢
  interval_cases number
  all_goals first
    | exact present register
    | exact insert_keeps_present _ _ _ present register

namespace SailStateUnchanged

-- A Sail step that, when it succeeds, leaves the Sail state exactly as it found it.
def Preserves {Value : Type} (step : SailM Value) : Prop :=
  ∀ (sail after : SailState) (value : Value), step sail = .ok value after → after = sail

theorem pure_rule {Value : Type} (value : Value) : Preserves (pure value) := by
  intro sail after result runs
  cases runs
  rfl

theorem bind_rule {Value Next : Type} {first : SailM Value} {next : Value → SailM Next}
    (keepsFirst : Preserves first) (keepsNext : ∀ value, Preserves (next value)) :
    Preserves (first >>= next) := by
  intro sail after result runs
  cases firstRun : first sail with
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    cases runs
  | ok value middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    exact (keepsNext value middle after result runs).trans (keepsFirst sail middle value firstRun)

theorem read_rule (register : Register) : Preserves (Sail.readReg register) := by
  intro sail after value runs
  exact readReg_pure register sail value after runs

end SailStateUnchanged

-- Checking whether compressed instructions are enabled only reads `misa`.
private theorem zca_enabled_unchanged :
    SailStateUnchanged.Preserves (currentlyEnabled extension.Ext_Zca) := by
  unfold currentlyEnabled
  apply SailStateUnchanged.bind_rule
  · unfold currentlyEnabled
    exact SailStateUnchanged.bind_rule (SailStateUnchanged.read_rule Register.misa)
      (fun _ => SailStateUnchanged.pure_rule _)
  · intro enabled
    exact SailStateUnchanged.pure_rule _

-- A jump either changes nothing or writes the target into nextPC.
private theorem jump_to_shape (target : BitVec 64) (sail after : SailState)
    (result : ExecutionResult) (runs : jump_to target sail = .ok result after) :
    after = sail ∨ after = { sail with regs := sail.regs.insert Register.nextPC target } := by
  unfold jump_to ext_control_check_pc at runs
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, Functor.map, EStateM.map,
    bind, EStateM.bind, pure, EStateM.pure,
    Sail.assert, PreSail.assert] at runs
  by_cases evenTarget : (BitVec.access target 0 == 0#1) = true
  · simp only [evenTarget, ↓reduceIte, pure, EStateM.pure, EStateM.bind,
      ExceptT.bindCont, EStateM.map] at runs
    cases zcaRun : currentlyEnabled extension.Ext_Zca sail with
    | error failure middle =>
      simp only [zcaRun] at runs
      cases runs
    | ok zca middle =>
      have same := zca_enabled_unchanged sail middle zca zcaRun
      subst same
      by_cases misaligned : bit_to_bool (BitVec.access target 1) = true ∧
          LeanRV64D.Functions.not zca = true
      all_goals
        simp only [zcaRun, ExceptT.bindCont, EStateM.map, Bool.and_eq_true, misaligned,
          ↓reduceIte, set_next_pc, Sail.writeReg, bind, EStateM.bind,
          pure, EStateM.pure] at runs
        cases runs
        first
        | exact Or.inl rfl
        | exact Or.inr rfl
  · simp only [evenTarget, throw, throwThe] at runs
    cases runs

namespace RegistersKept

-- A Sail step that, when it succeeds, removes no register.
def SailPreserves {Value : Type} (step : SailM Value) : Prop :=
  ∀ (sail after : SailState) (value : Value),
    step sail = .ok value after → AllRegistersPresent sail → AllRegistersPresent after

-- A Jolt step that, when it succeeds, removes no Sail register.
def Preserves {Value : Type} (step : JoltMonad Value) : Prop :=
  ∀ (state after : SailJoltState) (value : Value),
    step state = .ok value after → AllRegistersPresent state.sail → AllRegistersPresent after.sail

-- A step that leaves Sail's registers exactly as they were removes none of them.
theorem regs_unchanged_rule {Value : Type} {step : JoltMonad Value}
    (unchanged : ∀ (state after : SailJoltState) (value : Value),
      step state = .ok value after → after.sail.regs = state.sail.regs) :
    Preserves step := by
  intro state after value runs present register
  rw [unchanged state after value runs]
  exact present register

theorem pure_rule {Value : Type} (value : Value) : Preserves (pure value) :=
  regs_unchanged_rule (fun state after result runs => by cases runs; rfl)

theorem bind_rule {Value Next : Type} {first : JoltMonad Value} {next : Value → JoltMonad Next}
    (keepsFirst : Preserves first) (keepsNext : ∀ value, Preserves (next value)) :
    Preserves (first >>= next) := by
  intro state after result runs present
  cases firstRun : first state with
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    cases runs
  | ok value middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    exact keepsNext value middle after result runs (keepsFirst state middle value firstRun present)

theorem get_rule : Preserves (get : JoltMonad SailJoltState) :=
  regs_unchanged_rule (fun state after value runs => by cases runs; rfl)

theorem throw_rule {Value : Type} (failure : Error exception) :
    Preserves (throw failure : JoltMonad Value) := by
  intro state after value runs
  cases runs

theorem lift_rule {Value : Type} {step : SailM Value} (keeps : SailPreserves step) :
    Preserves (liftSail step) := by
  intro state after value runs present
  unfold liftSail at runs
  cases stepRun : step state.sail with
  | error failure sail =>
    rw [stepRun] at runs
    cases runs
  | ok result sail =>
    have kept := keeps state.sail sail result stepRun present
    rw [stepRun] at runs
    cases runs
    exact kept

theorem readReg_rule (register : Register) : Preserves (liftSail (Sail.readReg register)) :=
  lift_rule (fun sail after value runs present => by
    rw [readReg_pure register sail value after runs]
    exact present)

theorem writeReg_rule (register : Register) (value : RegisterType register) :
    Preserves (liftSail (Sail.writeReg register value)) :=
  lift_rule (fun sail after result runs present => by
    cases runs
    exact insert_keeps_present _ _ _ present)

theorem arch_pc_rule : Preserves (liftSail (get_arch_pc ())) :=
  lift_rule (fun sail after value runs present => by
    unfold get_arch_pc at runs
    rw [readReg_pure Register.PC sail value after runs]
    exact present)

theorem jump_rule (target : BitVec 64) : Preserves (liftSail (jump_to target)) :=
  lift_rule (fun sail after result runs present => by
    rcases jump_to_shape target sail after result runs with same | written
    · rw [same]
      exact present
    · rw [written]
      exact insert_keeps_present _ _ _ present)

theorem read_rule (source : JoltISA.Src) : Preserves (JoltISA.readSrc source) := by
  cases source with
  | vreg register =>
    exact regs_unchanged_rule (fun state after value runs => by
      simp only [JoltISA.readSrc_vreg, readVReg_run] at runs
      cases runs
      rfl)
  | xreg register =>
    exact lift_rule (fun sail after value runs present => by
      rw [rX_bits_pure register sail value after runs]
      exact present)

theorem write_rule (destination : JoltISA.Dst) (value : BitVec 64) :
    Preserves (JoltISA.writeDst destination value) := by
  cases destination with
  | vreg register =>
    exact regs_unchanged_rule (fun state after result runs => by
      simp only [JoltISA.writeDst, writeVReg] at runs
      split at runs
      · cases runs
      · cases runs
        rfl)
  | xreg register =>
    exact lift_rule (fun sail after result runs present => by
      rw [wX_bits_eq_stateAfterWrite register value sail after runs]
      exact wX_update_regs_keeps_present register value sail.regs present)

theorem load_doubleword_rule (address : BitVec 64) :
    Preserves (JoltISA.Mmu.load_doubleword address) :=
  regs_unchanged_rule (fun state after value runs => by
    rw [JoltISA.Mmu.load_doubleword_state runs])

theorem store_doubleword_rule (address value : BitVec 64) :
    Preserves (JoltISA.Mmu.store_doubleword address value) :=
  regs_unchanged_rule (fun _ _ _ runs => (JoltISA.Mmu.store_doubleword_regs runs).1)

theorem execHostIO_rule : Preserves JoltISA.execHostIO :=
  regs_unchanged_rule (fun state after result runs => by
    rw [execHostIO_keeps_sail state after result runs])

end RegistersKept

macro "registers_kept_auto" : tactic => `(tactic|
  repeat' first
  | with_reducible exact RegistersKept.read_rule _
  | with_reducible exact RegistersKept.write_rule _ _
  | with_reducible exact RegistersKept.pure_rule _
  | with_reducible exact RegistersKept.throw_rule _
  | with_reducible exact RegistersKept.get_rule
  | with_reducible exact RegistersKept.readReg_rule _
  | with_reducible exact RegistersKept.writeReg_rule _ _
  | with_reducible exact RegistersKept.arch_pc_rule
  | with_reducible exact RegistersKept.jump_rule _
  | with_reducible exact RegistersKept.load_doubleword_rule _
  | with_reducible exact RegistersKept.store_doubleword_rule _ _
  | with_reducible exact RegistersKept.execHostIO_rule
  | split
  | refine RegistersKept.bind_rule ?_ (fun _ => ?_))

-- Executing an instruction never removes a register from Sail's register map.
theorem execInstr_keeps_registers (instruction : JoltISA.Instr) (state after : SailJoltState)
    (result : ExecutionResult) (runs : JoltISA.execInstr instruction state = .ok result after)
    (present : AllRegistersPresent state.sail) :
    AllRegistersPresent after.sail := by
  have keeps : RegistersKept.Preserves (JoltISA.execInstr instruction) := by
    cases instruction
    case VirtualAdviceLoad destination byteCount =>
      -- reading the advice tape changes only the tape, then the value is written
      intro before afterLoad value loadRuns beforePresent
      simp only [JoltISA.execInstr] at loadRuns
      cases tapeRead : JoltISA.readAdviceTape before.adviceTape byteCount with
      | none =>
        simp only [tapeRead] at loadRuns
        cases loadRuns
      | some pair =>
        obtain ⟨adviceValue, tape⟩ := pair
        simp only [tapeRead] at loadRuns
        exact RegistersKept.bind_rule (RegistersKept.write_rule destination adviceValue)
          (fun _ => RegistersKept.pure_rule _)
          { before with adviceTape := tape } afterLoad value loadRuns beforePresent
    all_goals simp only [JoltISA.execInstr]
    all_goals registers_kept_auto
  exact keeps state after result runs present

-- Every integer register can be read when every Sail register is present.
theorem readable_of_present (sail : SailState) (present : AllRegistersPresent sail)
    (register : regidx) : Assumptions.XRegReadable register sail := by
  refine ⟨?_⟩
  obtain ⟨index⟩ := register
  unfold rX_bits rX regval_from_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind, pure, EStateM.pure]
  have small : index.toNat < 32 := index.isLt
  generalize index.toNat = number at small ⊢
  interval_cases number
  all_goals dsimp only
  · -- x0 is read as zero without looking it up
    exact ⟨_, rfl⟩
  all_goals
    obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp (present _)
    rw [readReg_eq_of_get? _ sail _ lookup]
    exact ⟨_, rfl⟩

-- Moving the PC overwrites only PC and nextPC, so every register stays present.
theorem advance_pc_keeps_registers (address : BitVec 64) (is_compressed : Bool)
    (state : SailJoltState) (present : AllRegistersPresent state.sail) :
    AllRegistersPresent (advance_pc address is_compressed state).sail := by
  intro register
  unfold advance_pc
  dsimp only
  exact insert_keeps_present _ _ _ (insert_keeps_present _ _ _ present) register

-- The instance's initial state has every register present.
theorem initial_state_registers_present {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    AllRegistersPresent initialState.sail := by
  unfold JoltInstance.initial_state at built
  cases layoutResult : joltInstance.memory_layout with
  | none =>
    simp only [layoutResult, bind, Option.bind] at built
    cases built
  | some layout =>
    simp only [layoutResult, bind, Option.bind] at built
    repeat' split at built
    all_goals first
      | exact init_state_registers_present _ _ _ _ _
      | (cases built
         exact init_state_registers_present _ _ _ _ _)
      | cases built

-- In an honest trace, every row starts with every Sail register present.
theorem HonestTrace.registers_present {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (position : Nat) (row : HonestTraceRow trace.bytecode)
    (atPosition : trace.rows[position]? = some row) :
    AllRegistersPresent row.preState.sail := by
  induction position generalizing row with
  | zero =>
    -- the first row starts from the initial state with the PC moved
    obtain ⟨_, _, startState⟩ := trace.starts row atPosition
    rw [startState]
    exact advance_pc_keeps_registers _ _ _
      (initial_state_registers_present _ _ _ trace.initialized)
  | succ position ih =>
    -- the previous row ran from a state with every register, so it ended with them
    obtain ⟨inRange, _⟩ := Array.getElem?_eq_some_iff.mp atPosition
    have previousAt : trace.rows[position]? = some trace.rows[position] :=
      Array.getElem?_eq_getElem (by omega)
    have previousEnd : AllRegistersPresent trace.rows[position].postState.sail :=
      execInstr_keeps_registers _ _ _ _ trace.rows[position].executes
        (ih trace.rows[position] previousAt)
    have link := trace.linked position trace.rows[position] row previousAt atPosition
    split at link
    · -- the same instruction continues from where the previous row ended
      rw [link.2]
      exact previousEnd
    · -- a new instruction starts, with the PC moved
      obtain ⟨_, _, _, _, startState⟩ := link
      rw [startState]
      exact advance_pc_keeps_registers _ _ _ previousEnd

-- A successful Sail register read returns the value stored for that register.
private theorem readReg_value (register : Register) (sail after : SailState)
    (value : RegisterType register)
    (runs : (Sail.readReg register : SailM (RegisterType register)) sail = .ok value after) :
    sail.regs.get? register = some value := by
  unfold Sail.readReg PreSail.readReg at runs
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure] at runs
  generalize lookup : sail.regs.get? register = stored at runs
  cases stored with
  | some storedValue =>
    cases runs
    rfl
  | none =>
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at runs
    cases runs

-- Reading a source gives its value in the state and changes nothing.
theorem readSrc_value (source : JoltISA.Src) (state after : SailJoltState) (value : BitVec 64)
    (runs : JoltISA.readSrc source state = .ok value after) :
    after = state ∧ value = JoltISA.sourceValue source state := by
  cases source with
  | vreg register =>
    simp only [JoltISA.readSrc_vreg, readVReg_run] at runs
    cases runs
    exact ⟨rfl, rfl⟩
  | xreg register =>
    simp only [JoltISA.readSrc_xreg] at runs
    unfold liftSail at runs
    cases readResult : rX_bits register state.sail with
    | error failure sail =>
      rw [readResult] at runs
      cases runs
    | ok readValue sail =>
      have same := rX_bits_pure register state.sail readValue sail readResult
      subst same
      rw [readResult] at runs
      cases runs
      refine ⟨rfl, ?_⟩
      -- the value read is the value stored for the register (x0 reads as 0)
      obtain ⟨index⟩ := register
      unfold rX_bits rX regval_from_reg at readResult
      simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
        bind, EStateM.bind, pure, EStateM.pure] at readResult
      unfold JoltISA.sourceValue
      have small : index.toNat < 32 := index.isLt
      generalize registerNumber : index.toNat = number at small readResult
      simp only [registerNumber]
      interval_cases number
      all_goals dsimp only at readResult ⊢
      · cases readResult
        rfl
      all_goals
        split at readResult
        · rename_i storedValue _ readStored
          cases readResult
          rw [readReg_value _ _ _ _ readStored]
          rfl
        · cases readResult

-- An ordinary assert (imm = 0) that executes had equal sides: Rust's assert_eq!
-- panics otherwise. (A spoil assert, imm ≠ 0, only warns in Rust; see model_review.md.)
-- See : jolt/tracer/src/instruction/virtual_assert_eq.rs:18-23
theorem assert_eq_holds (lhs rhs : JoltISA.Src) (state after : SailJoltState)
    (result : ExecutionResult)
    (runs : JoltISA.execInstr (.VirtualAssertEQ lhs rhs 0) state = .ok result after) :
    JoltISA.sourceValue lhs state = JoltISA.sourceValue rhs state := by
  simp only [JoltISA.execInstr] at runs
  split at runs
  · cases leftRead : JoltISA.readSrc lhs state with
    | error failure middle =>
      simp only [bind, EStateM.bind, leftRead] at runs
      cases runs
    | ok leftValue middle =>
      obtain ⟨middleSame, leftIs⟩ := readSrc_value lhs state middle leftValue leftRead
      simp only [bind, EStateM.bind, leftRead] at runs
      rw [middleSame] at runs
      cases rightRead : JoltISA.readSrc rhs state with
      | error failure middle =>
        rw [rightRead] at runs
        cases runs
      | ok rightValue middle =>
        obtain ⟨_, rightIs⟩ := readSrc_value rhs state middle rightValue rightRead
        rw [rightRead] at runs
        dsimp only at runs
        split at runs
        · rename_i equal
          rw [← leftIs, ← rightIs]
          exact equal
        · cases runs
  · -- the immediate is 0, so this is not a spoil assert
    rename_i notZero
    exact absurd (by decide) notZero

-- After inserting a value for every register in a list, a listed register holds its
-- value and any other register keeps what it had.
private theorem fold_insert_get (value : (register : Register) → RegisterType register) :
    ∀ (registers : List Register) (start : Std.ExtDHashMap Register RegisterType)
      (register : Register),
      (registers.foldl (fun map next => map.insert next (value next)) start).get? register =
        if register ∈ registers then some (value register) else start.get? register := by
  intro registers
  induction registers with
  | nil =>
    intro start register
    rw [if_neg List.not_mem_nil]
    rfl
  | cons head tail ih =>
    intro start register
    rw [List.foldl_cons, ih]
    by_cases inTail : register ∈ tail
    · rw [if_pos inTail, if_pos (List.mem_cons_of_mem _ inTail)]
    · rw [if_neg inTail]
      by_cases isHead : head = register
      · subst isHead
        rw [Std.ExtDHashMap.get?_insert_self, if_pos List.mem_cons_self]
      · rw [Std.ExtDHashMap.get?_insert, dif_neg (by rw [beq_iff_eq]; exact isHead)]
        rw [if_neg (fun member => by
          rcases List.mem_cons.mp member with same | later
          · exact isHead same.symm
          · exact inTail later)]

-- The initial state holds each register's initial value.
theorem init_state_register (entryAddress : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (adviceTape : JoltAdviceTape) (hostIO : JoltHostIOConfig)
    (register : Register) :
    (init_state entryAddress ram device adviceTape hostIO).sail.regs.get? register =
      some (initialRegisterValue entryAddress ram.size register) := by
  unfold init_state
  dsimp only
  rw [fold_insert_get, if_pos (Finset.mem_toList.mpr (Finset.mem_univ register))]

-- Every register, real or virtual, starts at 0.
theorem init_state_sourceValue (entryAddress : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (adviceTape : JoltAdviceTape) (hostIO : JoltHostIOConfig)
    (source : JoltISA.Src) :
    JoltISA.sourceValue source (init_state entryAddress ram device adviceTape hostIO) = 0 := by
  cases source with
  | vreg register => rfl
  | xreg register =>
    obtain ⟨index⟩ := register
    unfold JoltISA.sourceValue
    have small : index.toNat < 32 := index.isLt
    generalize registerNumber : index.toNat = number at small
    simp only [registerNumber]
    interval_cases number
    -- x0 reads as 0 directly; every other register holds its initial value, 0
    all_goals dsimp only
    all_goals
      rw [init_state_register]
      rfl

-- The instance's initial state has every register, real or virtual, at 0, as Rust's
-- Cpu::new sets them.
-- See : jolt/tracer/src/emulator/cpu.rs:504 (x: [0; REGISTER_COUNT])
theorem initial_state_sourceValue {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState)
    (source : JoltISA.Src) :
    JoltISA.sourceValue source initialState = 0 := by
  unfold JoltInstance.initial_state at built
  cases layoutResult : joltInstance.memory_layout with
  | none =>
    simp only [layoutResult, bind, Option.bind] at built
    cases built
  | some layout =>
    simp only [layoutResult, bind, Option.bind] at built
    repeat' split at built
    all_goals first
      | exact init_state_sourceValue _ _ _ _ _ source
      | (cases built
         exact init_state_sourceValue _ _ _ _ _ source)
      | cases built
