import JoltConstraints.WholeRun.SailCompleteness
import JoltConstraints.WholeRun.SystemBlocks

/-!
# Jolt follows Sail at a RISC-V instruction

`JoltInstance.sail_completeness` assumes that Jolt follows each step of the Sail run
(`JoltFollows`). This file proves the core of that premise for a RISC-V instruction that
accesses no memory or accesses RAM: if Sail's `execute` of the instruction retires and Jolt's
tracer accepts the instruction's RAM access (`MemoryConditions`), Jolt's rows for the
instruction retire too (`Block.Runs`).

The proof runs the soundness argument of `SystemBlocks.lean` backwards. Jolt's rows on the ghost
state (Sail's state after its prelude, with Jolt's virtual registers) project to Sail's
`execute` (`joltRun_eq_execute`), so they retire when Sail retires. The ghost state shadows the
block's first state with system registers overlaid (`Shadow`), and a shadow retires only when
the state it shadows retires.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace WholeRun

-- Reuse the private implementation lemmas of `BlockStep.lean` without changing that module.
local macro "blockHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.BlockStep
    (`WholeRun ++ n.getId)))
local macro "systemHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.SystemBlocks
    (`WholeRun ++ n.getId)))
local macro "unfold_overlay" " at " h:ident : tactic =>
  `(tactic| unfold $(Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.BlockStep
    `WholeRun.overlayRows)) at $h:ident)

/-- If the right result of `SameResult` is a success, so is the left one, with the same value and
related states. For example, a shadow block that retires forces the real block to retire. -/
theorem SameResult.ok_exists_left {α : Type} {R : SailJoltState → SailJoltState → Prop}
    {a : α} {g : SailJoltState} {r : EStateM.Result (Error exception) SailJoltState α}
    (h : SameResult R r (.ok a g)) : ∃ s, r = .ok a s ∧ R s g := by
  cases h with
  | ok a he => exact ⟨_, rfl, he⟩

/-- A projected result is a success only if the result is.
For example, a projected retiring run comes from a retiring run. -/
theorem systemProjectResult_ok {α : Type}
    {r : EStateM.Result (Error exception) SailJoltState α} {a : α} {t : SailState}
    (h : System.systemProjectResult r = .ok a t) :
    ∃ js, r = .ok a js ∧ System.systemProject js = t := by
  cases r with
  | ok a' js =>
    simp only [System.systemProjectResult, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨js, rfl, rfl⟩
  | error e js => simp [System.systemProjectResult] at h

/-- A mapped result is a success only if the result is. -/
theorem mapState_ok {ε σ τ α : Type} {f : σ → τ} {r : EStateM.Result ε σ α} {a : α} {t : τ}
    (h : mapState f r = .ok a t) : ∃ s, r = .ok a s ∧ f s = t := by
  cases r with
  | ok a' s =>
    simp only [mapState, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, rfl⟩
  | error e s => simp [mapState] at h

/-- Writing a register twice keeps the second value. -/
theorem withReg_withReg (js : SailJoltState) (r : Register) (v w : RegisterType r) :
    withReg (withReg js r v) r w = withReg js r w := by
  simp only [withReg, Step.setReg]
  congr 2
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split <;> rfl

/-- Writing a register its current value changes nothing. -/
theorem withReg_self (js : SailJoltState) (r : Register) (v : RegisterType r)
    (h : js.sail.regs.get? r = some v) : withReg js r v = js := by
  simp only [withReg, Step.setReg]
  have : js.sail.regs.insert r v = js.sail.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro k
    simp only [Std.ExtDHashMap.get?_insert]
    split
    · rename_i hk
      have hk : r = k := by simpa using hk
      subst hk
      simp [h]
    · rfl
  rw [this]

/-- **A retiring overlay run comes from a retiring run.** Jolt's rows retire from a state with
system registers overlaid (`overlayRows`) only if they retire from the state itself, provided
the state's embedded `misa` has the C bit set. The overlay writes registers no row reads, except
`misa`, whose C bit a taken branch tests. -/
theorem execProgram_of_overlayRows (p : Program) (cs : BitVec 7 → BitVec 64) (m : BitVec 64)
    (inc : Bool) (js : SailJoltState) {t : SailJoltState}
    {misa : RegisterType Register.misa} (hmisa : js.sail.regs.get? Register.misa = some misa)
    (hc : _get_Misa_C misa = 1#1)
    (h : JoltISA.execProgram p ((blockHelper% overlayRows) cs m inc js) = .ok RETIRE_SUCCESS t) :
    ∃ t', JoltISA.execProgram p js = .ok RETIRE_SUCCESS t' := by
  unfold_overlay at h
  simp only [execProgram_withReg p .pma_regions (by trivial),
    execProgram_withReg p .minstret_increment (by trivial),
    execProgram_withReg p .minstret (by trivial),
    execProgram_withReg p .reservation_width (by trivial),
    execProgram_withReg p .reservation_addr (by trivial),
    execProgram_withReg p .reservation_valid (by trivial),
    execProgram_withReg p .mstatus (by trivial),
    execProgram_withReg p .mtval (by trivial),
    execProgram_withReg p .mcause (by trivial),
    execProgram_withReg p .mepc (by trivial),
    execProgram_withReg p .mscratch (by trivial),
    execProgram_withReg p .mtvec (by trivial)] at h
  iterate 12 obtain ⟨_, h, _⟩ := mapState_ok h
  have back := execProgram_withMisa p misa hc _ _ h
  rw [withReg_withReg, withReg_self js _ _ hmisa] at back
  exact ⟨_, back⟩

/-- Jolt's load check depends only on the device. -/
theorem JoltRamLoadOk.congr {a : BitVec 64} {js g : SailJoltState}
    (hdev : g.jolt_device = js.jolt_device) (h : Assumptions.JoltRamLoadOk a js) :
    Assumptions.JoltRamLoadOk a g := ⟨by rw [hdev]; exact h.below_heap_end⟩

/-- Jolt's store check depends only on the device. -/
theorem JoltRamStoreOk.congr {a : BitVec 64} {js g : SailJoltState}
    (hdev : g.jolt_device = js.jolt_device) (h : Assumptions.JoltRamStoreOk a js) :
    Assumptions.JoltRamStoreOk a g :=
  ⟨by rw [hdev]; exact h.below_heap_end, by rw [hdev]; exact h.outside_canary⟩

/-- An instruction's memory conditions depend only on the source registers and the device.
For example, they carry over from a block's first state to its shadow. -/
theorem MemoryConditions.congr {i : RiscvInstruction} {js g : SailJoltState}
    (hsrc : ∀ r, sourceValue (.xreg r) g = sourceValue (.xreg r) js)
    (hdev : g.jolt_device = js.jolt_device) (h : MemoryConditions i js) :
    MemoryConditions i g := by
  cases i <;> simp only [MemoryConditions, hsrc] at h ⊢
  all_goals first
    | exact JoltRamLoadOk.congr hdev h
    | exact JoltRamStoreOk.congr hdev h
    | (refine ⟨by rw [hsrc]; exact h.align, by rw [hsrc]; exact JoltRamLoadOk.congr hdev h.load,
         ?_⟩
       have hs := h.store_ok
       simp only [↓reduceIte, Bool.false_eq_true] at hs ⊢
       all_goals (rw [hsrc]; exact JoltRamStoreOk.congr hdev hs))

/-- **Sail retires an instruction.** From Sail's state `s` at `pc`, after `try_step`'s prelude
for an instruction of `len` bytes, Sail's `execute` of an instruction matching `i` retires.
For example, an ADDI always retires, and a misaligned LW traps and does not. -/
def SailRetires (i : RiscvInstruction) (s : SailState) (pc : BitVec 64) (len : Int) : Prop :=
  ∃ (inc : Bool) (ast : instruction) (t : SailState), RiscvInstruction.Matches i ast ∧
    execute ast (Step.preludeState s inc pc len) = .ok RETIRE_SUCCESS t

/-- **Jolt runs a RISC-V instruction that Sail retires.** Let Jolt's state `jt` be related to
Sail's state `s`, with `nextPC` at the image row `row` of a lifted RISC-V instruction `i` that
accesses no memory or accesses RAM (`RamAccess`). If Sail's `execute` of `i` retires
(`SailRetires`) and Jolt's tracer accepts the access (`MemoryConditions`), then Jolt's rows for
`row` retire: the block from `jt` runs (`Block.Runs`).
The other premises are run invariants (`SystemInv`, the heap bound, `misa`'s C bit), facts
from decoding (`EvenOffsets`, the even address) and that the row expands.
For example, an ADDI block runs from every related state. -/
theorem Block.runs_of_sailRetires {program : Rv64ProgramImage SourceInstruction}
    {jt : SailJoltState} {s : SailState} (hrel : Related jt s) (hsys : SystemInv jt)
    (hheap : jt.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    {misa : RegisterType Register.misa} (hmisa : jt.sail.regs.get? Register.misa = some misa)
    (hc : _get_Misa_C misa = 1#1)
    {row : SourceInstructionRow SourceInstruction}
    (hnext : jt.sail.regs.get? Register.nextPC = some row.address)
    (hat : rowAt program row.address = some row) (hexp : (expand_instruction row).isSome)
    {i : RiscvInstruction} (hrow : row.instruction = .riscv i) (hlift : i.Lifted)
    (heven : i.EvenOffsets) (hpc : row.address.getLsbD 0 = false)
    (hram : RamAccess i (advance_pc row.address row.is_compressed jt))
    (hmem : MemoryConditions i (advance_pc row.address row.is_compressed jt))
    (retires : SailRetires i s row.address (if row.is_compressed then 2 else 4)) :
    ∃ post, (Block.mk row jt post).Runs program := by
  let b0 : Block := ⟨row, jt, jt⟩
  obtain ⟨inc, ast, t, hm, hexec⟩ := retires
  obtain ⟨pc, m, oldInc, hn, hr⟩ := hrel.regs
  have hp : pc = row.address := Option.some.inj (hn.symm.trans hnext)
  subst hp
  -- The rows of the block, with honest advice from its first state.
  obtain ⟨rows, hrows⟩ := Option.isSome_iff_exists.mp hexp
  let instrs := patchAdvice (row.instruction.honestTracerAdvice b0.start)
    (rows.map (·.instruction))
  have hblock : blockInstrs row b0.start = some instrs := by
    simp only [blockInstrs, hrows, Option.map_some, instrs]
  -- The ghost state: Sail's state after the prelude, with Jolt's virtual registers.
  let Gs := Step.preludeJolt { jt with sail := s } inc row.address (if row.is_compressed then 2 else 4)
  have hshadow : Shadow ((blockHelper% overlayRows) jt.vregs m inc b0.start) Gs :=
    (blockHelper% prelude_shadow) b0 s row.address m oldInc inc rfl hr hrel.ram
  have hadvice : blockInstrs row Gs = blockInstrs row b0.start := by
    have he := ((blockHelper% advice_shadow) i _ _ hshadow).trans
      ((blockHelper% advice_overlayRows) i jt.vregs m inc b0.start)
    simp only [blockInstrs, hrow, he]
  have hrawG := blockInstrs_run i row.address row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hlink : System.systemProject Gs = Gs.sail := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, ghost_projects hrel]
    rfl
  have hinv : Step.StepInvariant Gs.sail := hrel.inv.preludeState inc row.address _
  have hsrc : ∀ r, sourceValue (.xreg r) Gs = sourceValue (.xreg r) b0.start := fun r =>
    ((blockHelper% sourceValue_shadow) hshadow r).trans
      ((blockHelper% sourceValue_overlayRows) jt.vregs m inc b0.start r)
  have hramG : RamAccess i Gs := (systemHelper% ramAccess_of_sources) i b0.start Gs hsrc hram
  have hmemG : MemoryConditions i Gs := MemoryConditions.congr hsrc rfl hmem
  obtain ⟨hb, ha⟩ := equivAssumptions_of_conditions i hlift Gs (hsys.of_vregs rfl)
    hlink hinv hsys.mstatus_bits hrel.layout heven
    (by
      intro pc' hread
      have heq : pc' = row.address := Option.some.inj (hread.symm.trans (by
        simp [Gs, Step.preludeJolt, Step.preludeState,
          hr, sailRegs, System.systemProject, Step.setReg, Std.ExtDHashMap.get?_insert]))
      simpa only [heq] using hpc)
    hheap
    (by simp [Gs, Step.preludeJolt, Step.preludeState, Step.setReg, hr,
      sailRegs, Std.ExtDHashMap.get?_insert])
    (by simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg,
      Std.ExtDHashMap.get?_insert] using hrel.htif)
    hrel.present hramG hmemG
  -- Jolt's rows on the ghost project to Sail's `execute`, which retires.
  have hproj := RiscvInstruction.joltRun_eq_execute (honestInstr i Gs)
    ((blockHelper% honest_lifted) i Gs hlift) ast ((blockHelper% honest_matches) i Gs ast hm)
    Gs hb ha
  rw [hlink] at hproj
  have hsail : Gs.sail = Step.preludeState s inc row.address (if row.is_compressed then 2 else 4) := rfl
  rw [hsail, hexec] at hproj
  obtain ⟨ghostPost, hghost, _⟩ := systemProjectResult_ok hproj
  -- The real rows retire because their shadow does.
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hrawG, hghost] at hsync
  obtain ⟨overlayPost, hoverlay, _⟩ := hsync.ok_exists_left
  obtain ⟨post, hpost⟩ := execProgram_of_overlayRows _ _ _ _ _
    (by rw [show b0.start = advance_pc row.address row.is_compressed jt from rfl,
      JoltConstraints.Soundness.advance_pc_misa]; exact hmisa) hc hoverlay
  exact ⟨post, hat, hnext,
    ⟨_, instrs, Or.inr rfl, by simp only [hrows, Option.map_some, instrs]; rfl, hpost⟩⟩

/-- `Block.runs_of_sailRetires` with the `misa` premise in the form that `JoltFollows` provides
(`MisaC`). -/
theorem Block.runs_of_sailRetires_misaC {program : Rv64ProgramImage SourceInstruction}
    {jt : SailJoltState} {s : SailState} (hrel : Related jt s) (hsys : SystemInv jt)
    (hheap : jt.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8) (hmisa : MisaC jt)
    {row : SourceInstructionRow SourceInstruction}
    (hnext : jt.sail.regs.get? Register.nextPC = some row.address)
    (hat : rowAt program row.address = some row) (hexp : (expand_instruction row).isSome)
    {i : RiscvInstruction} (hrow : row.instruction = .riscv i) (hlift : i.Lifted)
    (heven : i.EvenOffsets) (hpc : row.address.getLsbD 0 = false)
    (hram : RamAccess i (advance_pc row.address row.is_compressed jt))
    (hmem : MemoryConditions i (advance_pc row.address row.is_compressed jt))
    (retires : SailRetires i s row.address (if row.is_compressed then 2 else 4)) :
    ∃ post, (Block.mk row jt post).Runs program :=
  let ⟨_, hm, hc⟩ := hmisa
  Block.runs_of_sailRetires hrel hsys hheap hm hc hnext hat hexp hrow hlift heven hpc hram hmem
    retires

end WholeRun
