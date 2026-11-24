import JoltConstraints.theorems.WholeRun.Run
import JoltConstraints.theorems.DeviceFrame

/-!
# The run before an explicit halt

Jolt at `ff6fc6568` ends on a success or panic row.
Both halt kinds preserve shared memory, restore the source PC as nextPC and
record their kind in CPU state.
This file cuts a block chain before either source halt and retains the final
shared memory and the panic claim determined by that halt kind.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions
set_option autoImplicit false
noncomputable section
namespace WholeRun

/-- The source instruction for an explicit halt kind.
For example, EBREAK is the panic source and `jolt.success` the success source.
Jolt at `ff6fc6568`: `expand_ebreak` and `JoltSuccess::exec`. -/
def haltSource : JoltHaltKind → SourceInstruction
  | .success => .jolt .JoltSuccess
  | .panic => .riscv .EBREAK

/-- The next source row is the halt of the specified kind.
For example, an EBREAK address gives `NextIsHalt program state .panic`. -/
def NextIsHalt (program : Rv64ProgramImage SourceInstruction) (state : SailJoltState)
    (kind : JoltHaltKind) : Prop :=
  ∃ row : SourceInstructionRow SourceInstruction,
    state.sail.regs.get? Register.nextPC = some row.address ∧
    rowAt program row.address = some row ∧ row.instruction = haltSource kind

/-- The final state shares memory and layout with the state before the halt.
An explicit halt also supplies its CPU marker and panic claim.
For example, a panic source leaves output bytes unchanged and records true. -/
def HaltObservation (program : Rv64ProgramImage SourceInstruction)
    (halt final : SailJoltState) : Prop :=
  final.sail.mem = halt.sail.mem ∧
  final.jolt_device.memory_layout = halt.jolt_device.memory_layout ∧
  ((∃ kind, NextIsHalt program halt kind ∧ final.halted = some kind ∧
      final.jolt_device.panic = (kind == JoltHaltKind.panic)) ∨ halt = final)

/-- Either source halt expands to its single scratch-register halt row.
For example, EBREAK expands to `Panic v40`, without any flag-word store. -/
private theorem halt_blockInstrs (row : SourceInstructionRow SourceInstruction)
    (state : SailJoltState) (kind : JoltHaltKind)
    (source : row.instruction = haltSource kind) (instrs : List JoltISA.Instr)
    (expanded : blockInstrs row state = some instrs) :
    instrs = [match kind with
      | .success => .JoltSuccess (.vreg JoltISA.systemScratchVReg)
      | .panic => .Panic (.vreg JoltISA.systemScratchVReg)] := by
  cases kind <;>
    simp [blockInstrs, expand_instruction, source, haltSource, SourceInstruction.expand,
      ExpandedSource.ofProgram, ExpandedSource.ofNative, JoltISA.Instr.rewriteNative,
      JoltISA.sideEffectingDst, JoltISA.isX0, JoltISA.ebreakProgram, JoltISA.Program.instrs,
      MAX_FINAL_ROWS_PER_SOURCE, stamp_sequence, patchAdvice] at expanded ⊢ <;>
    exact expanded.symm

/-- A source halt preserves the shared byte map and layout, restores its address
and records its kind and claim.
For example, `jolt.success` records false even if an earlier device claim was true. -/
theorem Block.halt_post {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) (kind : JoltHaltKind)
    (source : b.row.instruction = haltSource kind) :
    b.post.sail.mem = b.pre.sail.mem ∧
    b.post.jolt_device.memory_layout = b.pre.jolt_device.memory_layout ∧
    b.post.sail.regs.get? Register.nextPC = some b.row.address ∧
    b.post.halted = some kind ∧ b.post.jolt_device.panic = (kind == JoltHaltKind.panic) := by
  obtain ⟨instrs, expanded, executed⟩ := runs.executes
  rw [halt_blockInstrs _ _ kind source _ expanded] at executed
  obtain ⟨middle, haltRun, doneRun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ executed
  have postEq : middle = b.post := by
    simp only [JoltISA.execProgram, EStateM.run, pure, EStateM.pure] at doneRun
    exact (EStateM.Result.ok.inj doneRun).2
  subst middle
  have haltExec : JoltISA.execHalt kind (.vreg JoltISA.systemScratchVReg) b.start =
      .ok RETIRE_SUCCESS b.post := by
    cases kind <;> exact haltRun
  have readNext := readReg_eq_of_get? Register.nextPC b.start.sail
    (b.row.address + (if b.row.is_compressed then 2 else 4))
    (by simp [Block.start, advance_pc])
  have readPC := readReg_eq_of_get? Register.PC b.start.sail b.row.address
    (by simp [Block.start, advance_pc, Std.ExtDHashMap.get?_insert])
  rw [JoltISA.execHalt_vreg_run kind JoltISA.systemScratchVReg _ _ _ (by change ¬ (40 : Nat) < 32; omega)
    readNext readPC] at haltExec
  obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj haltExec
  rw [← stateEq]
  simp [JoltISA.recordHalt, Block.start, advance_pc]

/-- A chain after a halt repeats that same source halt and retains its memory
and final claim.
For example, every block linked after an EBREAK still records panic. -/
private theorem halt_tail {program : Rv64ProgramImage SourceInstruction} :
    ∀ (rest : List Block) (b : Block), (b :: rest).IsChain (fun x y => x.post = y.pre) →
      (∀ c ∈ b :: rest, c.Runs program) →
      ∀ kind, b.row.instruction = haltSource kind →
      ∀ last ∈ (b :: rest).getLast?,
        last.post.sail.mem = b.pre.sail.mem ∧
        last.post.jolt_device.memory_layout = b.pre.jolt_device.memory_layout ∧
        last.post.halted = some kind ∧ last.post.jolt_device.panic = (kind == JoltHaltKind.panic)
  | [], b, _, runs, kind, source, last, atLast => by
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at atLast
      subst last
      obtain ⟨memory, layout, _, marker, claim⟩ := Block.halt_post (runs b (by simp)) kind source
      exact ⟨memory, layout, marker, claim⟩
  | c :: rest, b, chain, runs, kind, source, last, atLast => by
      obtain ⟨linked, tailChain⟩ := List.isChain_cons_cons.mp chain
      have bRun := runs b (by simp)
      have cRun := runs c (by simp)
      obtain ⟨memory, layout, nextPC, _, _⟩ := Block.halt_post bRun kind source
      have address : c.row.address = b.row.address := by
        have continues := cRun.continues
        rw [← linked, nextPC] at continues
        exact (Option.some.inj continues).symm
      have rowEq : c.row = b.row := by
        have atRow := cRun.at_row
        rw [address, bRun.at_row] at atRow
        exact (Option.some.inj atRow).symm
      obtain ⟨tailMem, tailLayout, marker, claim⟩ :=
        halt_tail rest c tailChain (fun d hd => runs d (List.mem_cons_of_mem _ hd)) kind
          (rowEq ▸ source) last (by simpa only [List.getLast?_cons_cons] using atLast)
      exact ⟨tailMem.trans ((congrArg (fun s : SailJoltState => s.sail.mem) linked).symm.trans memory),
        tailLayout.trans ((congrArg (fun s : SailJoltState => s.jolt_device.memory_layout) linked).symm.trans layout),
        marker, claim⟩

/-- The halt prefix of a block chain, by induction on the chain. -/
private theorem halt_prefix_aux (program : Rv64ProgramImage SourceInstruction)
    (P : Block → Prop) :
    ∀ (bs : List Block) (p : SailJoltState),
      bs.IsChain (fun x y => x.post = y.pre) → (∀ b ∈ bs, b.Runs program ∧ P b) →
      (∀ f ∈ bs.head?, f.pre = p) →
      ∃ (pre : List Block) (halt : SailJoltState),
        (∀ b ∈ pre, b.Runs program ∧ (¬ ∃ kind, b.row.instruction = haltSource kind) ∧ P b) ∧
        pre.IsChain (fun x y => x.post = y.pre) ∧
        (∀ f ∈ pre.head?, f.pre = p) ∧
        (∀ l ∈ pre.getLast?, l.post = halt) ∧
        (pre = [] → halt = p) ∧
        ∀ l ∈ bs.getLast?, HaltObservation program halt l.post
  | [], p, _, _, _ => ⟨[], p, by simp, by simp, by simp, by simp, fun _ => rfl, by simp⟩
  | b :: rest, p, hchain, hruns, hhead => by
      have hbp : b.pre = p := hhead b rfl
      obtain ⟨hbr, hP⟩ := hruns b (by simp)
      by_cases hb : ∃ kind, b.row.instruction = haltSource kind
      · refine ⟨[], p, by simp, by simp, by simp, by simp, fun _ => rfl, ?_⟩
        intro l hl
        obtain ⟨kind, source⟩ := hb
        obtain ⟨memory, layout, recorded, claim⟩ :=
          halt_tail rest b hchain (fun c hc => (hruns c hc).1) kind source l hl
        refine ⟨?_, ?_, Or.inl ⟨kind, ⟨b.row, ?_, hbr.at_row, source⟩, recorded, claim⟩⟩
        · simpa only [hbp] using memory
        · simpa only [hbp] using layout
        · rw [← hbp]; exact hbr.continues
      · cases rest with
        | nil =>
          refine ⟨[b], b.post, ?_, by simp, ?_, ?_, by simp, ?_⟩
          · intro x hx
            simp only [List.mem_singleton] at hx
            subst hx
            exact ⟨hbr, hb, hP⟩
          · simp [hbp]
          · simp
          · intro l hl
            simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hl
            subst hl
            exact ⟨rfl, rfl, Or.inr rfl⟩
        | cons c rest' =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨hlink, hchain'⟩ := hchain
          obtain ⟨pre', halt, h1, h2, h3, h4, h5, h6⟩ := halt_prefix_aux program P (c :: rest')
            b.post hchain' (fun d hd => hruns d (List.mem_cons_of_mem _ hd))
            (by
              intro f hf
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
              subst hf
              exact hlink.symm)
          refine ⟨b :: pre', halt, ?_, ?_, ?_, ?_, by simp, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨hbr, hb, hP⟩
            · exact h1 x hx
          · cases pre' with
            | nil => simp
            | cons d t =>
              rw [List.isChain_cons_cons]
              exact ⟨(h3 d rfl).symm, h2⟩
          · simp [hbp]
          · intro l hl
            cases pre' with
            | nil =>
              simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hl
              subst hl
              exact (h5 rfl).symm
            | cons d t =>
              exact h4 l (by simpa only [List.getLast?_cons_cons] using hl)
          · intro l hl
            exact h6 l (by simpa only [List.getLast?_cons_cons] using hl)

/-- Every honest trace has a chain of non-halting source blocks before its
explicit halt, with final memory and claim described by `HaltObservation`.
For example, a trace beginning with EBREAK has an empty prefix. -/
theorem HonestTrace.halt_prefix {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace inst inputs) :
    ∃ (pre : List Block) (halt final : SailJoltState),
      trace.rows.back?.map (·.postState) = some final ∧
      (∀ b ∈ pre, b.Runs inst.program ∧ ¬ ∃ kind, b.row.instruction = haltSource kind) ∧
      pre.IsChain (fun b c => b.post = c.pre) ∧
      (∀ first ∈ pre.head?, first.pre = trace.initialState) ∧
      (∀ last ∈ pre.getLast?, last.post = halt) ∧
      (pre = [] → halt = trace.initialState) ∧
      HaltObservation inst.program halt final ∧
      (∀ b ∈ pre, ∃ k, b.FirstRowAt trace.toTrace k) := by
  obtain ⟨blocks, nonempty, runs, head, chain, back, _, traced⟩ := HonestTrace.blocks trace
  obtain ⟨last, atLast⟩ : ∃ last, blocks.getLast? = some last := by
    cases found : blocks.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp found) nonempty
    | some last => exact ⟨last, rfl⟩
  have starts : ∀ first ∈ blocks.head?, first.pre = trace.initialState := by
    intro first atFirst
    rw [Option.mem_def] at atFirst
    rw [atFirst] at head
    simpa using head
  obtain ⟨pre, halt, prefixRuns, prefixChain, first, lastEq, empty, observation⟩ :=
    halt_prefix_aux inst.program (fun b => ∃ k, b.FirstRowAt trace.toTrace k)
      blocks trace.initialState chain (fun b member => ⟨runs b member, traced b member⟩) starts
  refine ⟨pre, halt, last.post, ?_, ?_, prefixChain, first, lastEq, empty,
    observation last atLast, ?_⟩
  · rw [← back, atLast]; rfl
  · intro b member; exact ⟨(prefixRuns b member).1, (prefixRuns b member).2.1⟩
  · intro b member; exact (prefixRuns b member).2.2

/-- A completed honest trace records its final halt kind and the corresponding
panic claim.
For example, a final panic row records `some panic` and claim true. -/
theorem HonestTrace.final_halt {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace inst inputs)
    (final : SailJoltState) (back : trace.rows.back?.map (·.postState) = some final) :
    ∃ kind, final.halted = some kind ∧ final.jolt_device.panic = (kind == JoltHaltKind.panic) := by
  have inside : trace.rows.size - 1 < trace.rows.size := by have := trace.nonempty; omega
  have lastBack : trace.rows.back? = some trace.rows[trace.rows.size - 1] := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem inside]
  have finalEq : trace.rows[trace.rows.size - 1].postState = final := by
    simpa only [lastBack, Option.map_some, Option.some.injEq] using back
  obtain ⟨_, _, kind, _, recorded, claim⟩ :=
    trace.halt_row (trace.rows.size - 1) inside (trace.stops _ lastBack)
  exact ⟨kind, finalEq ▸ recorded, finalEq ▸ claim⟩

/-- Output matching reads outputs from the final shared map and the panic claim
from the final CPU device.
For example, a panic trace can match a true public panic claim. -/
theorem HonestTrace.matches_outputs_final {inst : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace inst inputs)
    (final : SailJoltState) (back : trace.rows.back?.map (·.postState) = some final) :
    trace.matches_outputs inst ↔
      trimTrailingZeros (final.jolt_device.outputsOf final.sail.mem) = trimTrailingZeros inst.outputs ∧
      final.jolt_device.panic = inst.panic := by
  unfold Trace.matches_outputs
  simp only [back, Option.getD_some]

end WholeRun
