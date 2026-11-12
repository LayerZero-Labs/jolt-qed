import JoltConstraints.WholeRun.Run

/-!
# The run up to the first EBREAK

`docs/riscv-alignment.md`, section 4, ends the whole-run theorem at the first state whose next
instruction is EBREAK. Jolt expands EBREAK to the self-jump `JAL v40, 0`
(`JoltISA.ebreakProgram`): the block leaves `nextPC` at the instruction's own address and
changes only a virtual register, so the chain keeps re-running the same EBREAK row and never
touches `jolt_device`.

This file cuts the block chain of an honest trace (`HonestTrace.blocks`) at the first EBREAK
block. The blocks before it are the *halt prefix*. Every one of them is a non-EBREAK block, so
a per-block Sail simulation chains over the prefix alone (`HonestTrace.sailRun_halt`). The
state `halt` the prefix ends in agrees with the trace's final state on `jolt_device`, which is
all that `Trace.matches_outputs` reads (the output bytes and the panic flag).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- The state `jt` is about to run an EBREAK: its `nextPC` is the address of an image row whose
instruction is EBREAK (the C.EBREAK form decodes to the same instruction, flagged compressed).
For example, the state after the last instruction before `ebreak` in a guest program. -/
def NextIsEbreak (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState) : Prop :=
  ∃ row : SourceInstructionRow SourceInstruction,
    jt.sail.regs.get? Register.nextPC = some row.address ∧
    rowAt program row.address = some row ∧
    row.instruction = .riscv .EBREAK

/-- A register present in a state is read back by a lifted Sail read, without changing the
state. -/
private theorem liftSail_readReg (r : Register) (s : SailJoltState) (v : RegisterType r)
    (h : s.sail.regs.get? r = some v) :
    liftSail (LeanRV64D.readReg r : SailM (RegisterType r)) s = .ok v s := by
  unfold liftSail
  rw [readReg_eq_of_get? r s.sail v h]

/-- The jump `JAL v, imm` into a virtual register changes no part of the state but that
register and `nextPC`; `nextPC` becomes the address in `PC` plus `imm`. -/
private theorem jal_vreg_run (v : JoltISA.VReg) (hv : ¬ v.toNat < 32) (imm : BitVec 64)
    (s post : SailJoltState) (result : ExecutionResult) (pc : BitVec 64)
    (hpc : s.sail.regs.get? Register.PC = some pc)
    (hnext : ∃ n, s.sail.regs.get? Register.nextPC = some n)
    (h : JoltISA.execInstr (.JAL (.vreg v) imm) s = .ok result post) :
    post.jolt_device = s.jolt_device ∧ post.sail.regs.get? Register.nextPC = some (pc + imm) := by
  obtain ⟨n, hn⟩ := hnext
  simp only [JoltISA.execInstr, bind, EStateM.bind, liftSail_readReg _ s _ hn,
    liftSail_readReg _ s _ hpc, JoltISA.writeDst, writeVReg, hv, ite_false, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure] at h
  have write : ∀ (t : SailJoltState) (x : BitVec 64),
      liftSail (LeanRV64D.writeReg Register.nextPC x : SailM Unit) t =
        .ok () { t with sail := Step.setReg t.sail Register.nextPC x } := by
    intro t x
    unfold liftSail
    rw [Step.writeReg_run]
  rw [write] at h
  simp only [EStateM.Result.ok.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨rfl, by simp [Step.setReg]⟩

/-- Jolt's tracer expands EBREAK to the one row `JAL v40, 0`. -/
private theorem ebreak_blockInstrs (row : SourceInstructionRow SourceInstruction)
    (js : SailJoltState) (h : row.instruction = .riscv .EBREAK) (instrs : List JoltISA.Instr)
    (hb : blockInstrs row js = some instrs) :
    instrs = [JoltISA.Encoded.JAL (.vreg JoltISA.systemScratchVReg) 0] := by
  simp [blockInstrs, expand_instruction, h, SourceInstruction.expand,
    ExpandedSource.ofProgram, JoltISA.ebreakProgram, JoltISA.Program.instrs,
    SourceInstruction.rowCapacity, MAX_FINAL_ROWS_PER_SOURCE, stamp_sequence,
    patchAdvice] at hb
  exact hb.symm

/-- **A block running EBREAK stalls.** Its rows leave `jolt_device` unchanged and `nextPC` at
the row's own address, so the next block of the chain runs the same EBREAK row again. -/
theorem Block.ebreak_post {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) (hb : b.row.instruction = .riscv .EBREAK) :
    b.post.jolt_device = b.pre.jolt_device ∧
      b.post.sail.regs.get? Register.nextPC = some b.row.address := by
  obtain ⟨instrs, hinstrs, hexec⟩ := hruns.executes
  rw [ebreak_blockInstrs _ _ hb _ hinstrs] at hexec
  have hseq : JoltISA.Program.seq [JoltISA.Encoded.JAL (.vreg JoltISA.systemScratchVReg) 0] =
      .instr (JoltISA.Encoded.JAL (.vreg JoltISA.systemScratchVReg) 0) (.done RETIRE_SUCCESS) :=
    rfl
  rw [hseq] at hexec
  obtain ⟨js₁, h1, h2⟩ := JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hexec
  have hpost : js₁ = b.post := by
    simp only [JoltISA.execProgram, EStateM.run, pure, EStateM.pure] at h2
    exact (EStateM.Result.ok.inj h2).2
  subst hpost
  have hpc : b.start.sail.regs.get? Register.PC = some b.row.address := by
    simp [Block.start, advance_pc, Std.ExtDHashMap.get?_insert]
  have hnext : ∃ n, b.start.sail.regs.get? Register.nextPC = some n :=
    ⟨b.row.address + (if b.row.is_compressed then 2 else 4), by
      simp [Block.start, advance_pc]⟩
  obtain ⟨hdevice, hnextPC⟩ := jal_vreg_run JoltISA.systemScratchVReg (by decide) _ b.start b.post RETIRE_SUCCESS _ hpc hnext h1
  refine ⟨hdevice, ?_⟩
  have zero : (sign_extend (m := 64) (0 : BitVec 21)) = 0 := by decide
  rw [hnextPC, zero]
  simp

/-- Once a block runs EBREAK, so does every block after it in a chain: the chain's `nextPC`
link names the same address, and the image has one row per address. The last block's state
then has the same `jolt_device` as the first EBREAK block's pre-state. -/
private theorem ebreak_tail {program : Rv64ProgramImage SourceInstruction} :
    ∀ (rest : List Block) (b : Block), (b :: rest).IsChain (fun x y => x.post = y.pre) →
      (∀ c ∈ b :: rest, c.Runs program) → b.row.instruction = .riscv .EBREAK →
      ∀ l ∈ (b :: rest).getLast?, l.post.jolt_device = b.pre.jolt_device
  | [], b, _, hruns, hb, l, hl => by
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hl
      subst hl
      exact (Block.ebreak_post (hruns _ (by simp)) hb).1
  | c :: rest, b, hchain, hruns, hb, l, hl => by
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hlink, hchain'⟩ := hchain
      have hbr := hruns b (by simp)
      have hcr := hruns c (by simp)
      have hbp := Block.ebreak_post hbr hb
      have haddr : c.row.address = b.row.address := by
        have h1 := hcr.continues
        rw [← hlink, hbp.2] at h1
        exact (Option.some.inj h1).symm
      have hrow : c.row = b.row := by
        have h1 := hcr.at_row
        rw [haddr, hbr.at_row] at h1
        exact (Option.some.inj h1).symm
      have ih := ebreak_tail rest c hchain' (fun d hd => hruns d (List.mem_cons_of_mem _ hd))
        (hrow ▸ hb) l (by simpa only [List.getLast?_cons_cons] using hl)
      rw [ih, ← hlink]
      exact hbp.1

/-- The halt prefix of a block chain, by induction on the chain. -/
private theorem halt_prefix_aux (program : Rv64ProgramImage SourceInstruction)
    (P : Block → Prop) :
    ∀ (bs : List Block) (p : SailJoltState),
      bs.IsChain (fun x y => x.post = y.pre) → (∀ b ∈ bs, b.Runs program ∧ P b) →
      (∀ f ∈ bs.head?, f.pre = p) →
      ∃ (pre : List Block) (halt : SailJoltState),
        (∀ b ∈ pre, b.Runs program ∧ b.row.instruction ≠ .riscv .EBREAK ∧ P b) ∧
        pre.IsChain (fun x y => x.post = y.pre) ∧
        (∀ f ∈ pre.head?, f.pre = p) ∧
        (∀ l ∈ pre.getLast?, l.post = halt) ∧
        (pre = [] → halt = p) ∧
        ∀ l ∈ bs.getLast?, (NextIsEbreak program halt ∨ halt = l.post) ∧
          l.post.jolt_device = halt.jolt_device
  | [], p, _, _, _ => ⟨[], p, by simp, by simp, by simp, by simp, fun _ => rfl, by simp⟩
  | b :: rest, p, hchain, hruns, hhead => by
      have hbp : b.pre = p := hhead b rfl
      obtain ⟨hbr, hP⟩ := hruns b (by simp)
      by_cases hb : b.row.instruction = .riscv .EBREAK
      · refine ⟨[], p, by simp, by simp, by simp, by simp, fun _ => rfl, ?_⟩
        intro l hl
        refine ⟨Or.inl ⟨b.row, ?_, hbr.at_row, hb⟩, ?_⟩
        · rw [← hbp]; exact hbr.continues
        · rw [← hbp]; exact ebreak_tail rest b hchain (fun c hc => (hruns c hc).1) hb l hl
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
            exact ⟨Or.inr rfl, rfl⟩
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

/-- **The halt prefix of an honest trace.** The chain of blocks before the first EBREAK block
is `pre`; `halt` is the state it ends in (the initial state if `pre` is empty). Either the next
instruction at `halt` is an EBREAK, or the trace ended without one and `halt` is the final
state. Every later block only re-runs the same EBREAK row, so `halt` and the final state share
`jolt_device`. -/
theorem HonestTrace.halt_prefix {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ (pre : List Block) (halt final : SailJoltState),
      trace.rows.back?.map (·.postState) = some final ∧
      (∀ b ∈ pre, b.Runs joltInstance.program ∧ b.row.instruction ≠ .riscv .EBREAK) ∧
      pre.IsChain (fun b c => b.post = c.pre) ∧
      (∀ first ∈ pre.head?, first.pre = trace.initialState) ∧
      (∀ last ∈ pre.getLast?, last.post = halt) ∧
      (pre = [] → halt = trace.initialState) ∧
      (NextIsEbreak joltInstance.program halt ∨ halt = final) ∧
      halt.jolt_device = final.jolt_device ∧
      (∀ b ∈ pre, ∃ k, b.FirstRowAt trace.toTrace k) := by
  obtain ⟨bs, hne, hruns, hhead, hchain, hlast, -, htraced⟩ := HonestTrace.blocks trace
  obtain ⟨last, hl⟩ : ∃ l, bs.getLast? = some l := by
    cases h : bs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some l => exact ⟨l, rfl⟩
  have hheads : ∀ f ∈ bs.head?, f.pre = trace.initialState := by
    intro f hf
    rw [Option.mem_def] at hf
    rw [hf] at hhead
    simpa using hhead
  obtain ⟨pre, halt, h1, h2, h3, h4, h5, h6⟩ :=
    halt_prefix_aux joltInstance.program (fun b => ∃ k, b.FirstRowAt trace.toTrace k)
      bs trace.initialState hchain (fun b hb => ⟨hruns b hb, htraced b hb⟩) hheads
  have hfinal : trace.rows.back?.map (·.postState) = some last.post := by
    rw [← hlast, hl]; rfl
  obtain ⟨hn, hjd⟩ := h6 last hl
  exact ⟨pre, halt, last.post, hfinal, fun b hb => ⟨(h1 b hb).1, (h1 b hb).2.1⟩,
    h2, h3, h4, h5, hn, hjd.symm, fun b hb => (h1 b hb).2.2⟩

/-- `Trace.matches_outputs` reads the final state only through its `jolt_device`, so it can be
read at the halt state. -/
theorem HonestTrace.matches_outputs_halt {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (halt final : SailJoltState) (hfinal : trace.rows.back?.map (·.postState) = some final)
    (hdevice : halt.jolt_device = final.jolt_device) :
    trace.matches_outputs joltInstance ↔
      trimTrailingZeros halt.jolt_device.outputs = trimTrailingZeros joltInstance.outputs ∧
        halt.jolt_device.panic = joltInstance.panic := by
  unfold Trace.matches_outputs
  simp only [hfinal, Option.getD_some, hdevice]

/-- **The Sail run up to the first EBREAK.** If every non-EBREAK block of the trace is
simulated, `sailRun` from a state related to the initial state reaches a state related to
`halt`. At `halt` either the next instruction is EBREAK (the run stops before it, as in
`docs/riscv-alignment.md` section 4) or `halt` is the trace's final state, and `halt` has the
final state's `jolt_device`. -/
theorem HonestTrace.sailRun_halt {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (R : SailJoltState → SailState → Prop)
    (hsim : ∀ b : Block, b.Runs joltInstance.program → b.row.instruction ≠ .riscv .EBREAK →
      BlockSimulates R b)
    (s₀ : SailState) (h₀ : R trace.initialState s₀) :
    ∃ (n : Nat) (halt final : SailJoltState) (s : SailState),
      trace.rows.back?.map (·.postState) = some final ∧
      WholeRun.sailRun n s₀ = .ok () s ∧ R halt s ∧
      (NextIsEbreak joltInstance.program halt ∨ halt = final) ∧
      halt.jolt_device = final.jolt_device := by
  obtain ⟨pre, halt, final, hfinal, hpre, hchain, hhead, hlast, hnil, hn, hjd, -⟩ :=
    HonestTrace.halt_prefix trace
  cases pre with
  | nil =>
    exact ⟨0, halt, final, s₀, hfinal, rfl, by rw [hnil rfl]; exact h₀, hn, hjd⟩
  | cons first rest =>
    obtain ⟨l, s, hl, hrun, hrel⟩ := sailRun_of_chain R (first :: rest) hchain
      (fun b hb => hsim b (hpre b hb).1 (hpre b hb).2) first rfl s₀
      (by rw [hhead first rfl]; exact h₀)
    have hlh : l.post = halt := hlast l hl
    exact ⟨_, halt, final, s, hfinal, hrun, hlh ▸ hrel, hn, hjd⟩

end WholeRun
