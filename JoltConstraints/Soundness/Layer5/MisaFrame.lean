import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.execution_facts
import JoltConstraints.witness_helpers.ram_state

/-! Sail's instruction-set configuration is initialized once and preserved by
Jolt execution, including independent tape answers.
Jolt's CSR instructions use virtual registers rather than Sail's CSR map.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::new`) and
jolt/crates/jolt-program/src/expand/control_flow/csrrw.rs (`expand_csrrw`)
at 5def437f. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- Equality of the optional Sail `misa` values in two Jolt states.
For example, changing only nextPC preserves this relation. -/
private abbrev SameMisa (s t : SailJoltState) : Prop :=
  s.sail.regs.get? Register.misa = t.sail.regs.get? Register.misa

private theorem sameMisa_trans (s t u : SailJoltState)
    (st : SameMisa s t) (tu : SameMisa t u) : SameMisa s u := st.trans tu

private theorem unchanged_rule {α : Type} {step : JoltMonad α}
    (unchanged : ∀ s t v, step s = .ok v t → t.sail.regs = s.sail.regs) :
    StatePreservation.Preserves SameMisa step := by
  intro s t v runs
  dsimp only [SameMisa]
  rw [unchanged s t v runs]

private theorem read_rule (src : Src) :
    StatePreservation.Preserves SameMisa (readSrc src) :=
  unchanged_rule (fun s t v runs => by rw [(readSrc_value src s t v runs).1])

private theorem lift_rule {α : Type} {step : SailM α}
    (keeps : StatePreservation.Preserves
      (fun s t : SailState => s.regs.get? Register.misa = t.regs.get? Register.misa) step) :
    StatePreservation.Preserves SameMisa (liftSail step) :=
  StatePreservation.liftSail_rule (fun _ _ same => same) keeps

private theorem readReg_rule (r : Register) :
    StatePreservation.Preserves SameMisa (liftSail (Sail.readReg r)) :=
  lift_rule (fun s t v runs => by rw [readReg_pure r s v t runs])

private theorem writeNextPC_rule (value : BitVec 64) :
    StatePreservation.Preserves SameMisa (liftSail (Sail.writeReg Register.nextPC value)) :=
  lift_rule (fun s t v runs => by cases runs; simp [Std.ExtDHashMap.get?_insert])

private theorem write_rule (dst : Dst) (value : BitVec 64) :
    StatePreservation.Preserves SameMisa (writeDst dst value) := by
  cases dst with
  | vreg vr =>
    apply unchanged_rule
    intro s t v runs
    simp only [writeDst, writeVReg] at runs
    split at runs
    · cases runs
    · cases runs; rfl
  | xreg rd =>
    apply lift_rule
    intro s t v runs
    cases v
    rw [wX_bits_eq_stateAfterWrite rd value s t runs]
    obtain ⟨index⟩ := rd
    simp only [stateAfterWrite, wX_update_regs]
    split <;> simp [Std.ExtDHashMap.get?_insert]

private theorem jump_rule (target : BitVec 64) :
    StatePreservation.Preserves SameMisa (liftSail (jump_to target)) := by
  apply lift_rule
  intro s t v runs
  rcases jump_to_shape target s t v runs with same | written
  · rw [same]
  · rw [written]; simp [Std.ExtDHashMap.get?_insert]

private theorem load_rule (address : BitVec 64) :
    StatePreservation.Preserves SameMisa (Mmu.load_doubleword address) :=
  unchanged_rule (fun _ _ _ runs => by rw [Mmu.load_doubleword_state runs])

private theorem store_rule (address value : BitVec 64) :
    StatePreservation.Preserves SameMisa (Mmu.store_doubleword address value) :=
  unchanged_rule (fun _ _ _ runs => (Mmu.store_doubleword_regs runs).1)

private theorem host_rule : StatePreservation.Preserves SameMisa execHostIO :=
  unchanged_rule (fun s t v runs => by rw [execHostIO_keeps_sail s t v runs])

/-- Every successful instruction with an independent tape answer preserves
Sail's `misa` register, which holds the enabled ISA extensions.
For example, a branch can change `nextPC`, but cannot disable compressed instructions.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at 5def437f. -/
theorem execWithTapeAnswer_keeps_misa (instruction : Instr) (answer : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => s.sail.regs.get? Register.misa =
        t.sail.regs.get? Register.misa) (execWithTapeAnswer instruction answer) := by
  change StatePreservation.Preserves SameMisa _
  cases instruction <;> simp only [execWithTapeAnswer, execInstr, get_arch_pc]
  case VirtualAdviceLoad dst width =>
    intro s t v runs
    split at runs
    · have kept := StatePreservation.bind_rule sameMisa_trans (write_rule dst answer)
        (fun _ => StatePreservation.pure_rule (relation := SameMisa)
          (fun _ => rfl) RETIRE_SUCCESS) _ _ _ runs
      exact kept
    · cases runs
  all_goals
    preservation_auto [read_rule _, write_rule _ _, readReg_rule _, writeNextPC_rule _,
      readReg_rule Register.PC, jump_rule _, load_rule _, store_rule _ _, host_rule,
      StatePreservation.pure_rule (relation := SameMisa) (fun _ => rfl) _,
      StatePreservation.throw_rule SameMisa _,
      StatePreservation.get_rule (relation := SameMisa) (fun _ => rfl)]
      using StatePreservation.bind_rule sameMisa_trans

/-- Preparing an instruction changes PC and nextPC, leaving `misa` fixed.
For example, fetching a compressed instruction advances nextPC by two without
changing the enabled ISA extensions.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at 5def437f. -/
theorem advance_pc_misa (address : BitVec 64) (compressed : Bool) (state : SailJoltState) :
    (advance_pc address compressed state).sail.regs.get? Register.misa =
      state.sail.regs.get? Register.misa := by
  simp [advance_pc, Std.ExtDHashMap.get?_insert]

private theorem initial_state_misa {Source : Type}
    (joltInstance : JoltInstance Source) (inputs : JoltPrivateInputs) (state : SailJoltState)
    (initialized : joltInstance.initial_state inputs = some state) :
    state.sail.regs.get? Register.misa = some 0x800000008014312f := by
  unfold JoltInstance.initial_state at initialized
  cases layout : joltInstance.memory_layout with
  | none => simp only [layout, bind, Option.bind] at initialized; cases initialized
  | some deviceLayout =>
    simp only [layout, bind, Option.bind] at initialized
    repeat' split at initialized
    all_goals first
      | (cases initialized; exact init_state_register _ _ _ _ _ Register.misa)
      | cases initialized

/-- The final state of an initialized run retains Jolt's initial `misa` value.
The final state is the last recorded post-state, or the initial state for an
empty run; for example, the C extension's bit stays set after a taken branch.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::new`, `Cpu::tick`) at 5def437f. -/
theorem UntrustedAnswerRun.final_misa
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance inputs) :
    (TraceWitness.finalTraceState run.toTrace).sail.regs.get? Register.misa =
      some 0x800000008014312f := by
  have rowStep (i : Fin run.rows.size) :=
    execWithTapeAnswer_keeps_misa _ _ _ _ _ (run.executes i)
  have rowPre (n : Nat) (bound : n < run.rows.size) :
      run.rows[n].preState.sail.regs.get? Register.misa =
        run.initialState.sail.regs.get? Register.misa := by
    induction n with
    | zero =>
      rw [(run.starts run.rows[0] (Array.getElem?_eq_getElem bound)).2.2]
      exact advance_pc_misa _ _ _
    | succ n ih =>
      have previous : n < run.rows.size := by omega
      have link := run.linked n run.rows[n] run.rows[n + 1]
        (Array.getElem?_eq_getElem previous) (Array.getElem?_eq_getElem bound)
      have preEq : run.rows[n + 1].preState.sail.regs.get? Register.misa =
          run.rows[n].postState.sail.regs.get? Register.misa := by
        split at link
        · rw [link.2]
        · obtain ⟨_, _, _, _, prepared⟩ := link
          rw [prepared]
          exact advance_pc_misa _ _ _
      exact preEq.trans ((rowStep ⟨n, previous⟩).symm.trans (ih previous))
  have initial := initial_state_misa joltInstance inputs run.initialState run.initialized
  unfold TraceWitness.finalTraceState
  split
  · rename_i nonempty
    exact (rowStep ⟨run.rows.size - 1, by change 0 < run.rows.size at nonempty; omega⟩).symm.trans
      ((rowPre _ (by change 0 < run.rows.size at nonempty; omega)).trans initial)
  · exact initial

end JoltConstraints.Soundness
