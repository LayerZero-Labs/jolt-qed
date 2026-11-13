import JoltConstraints.WholeRun.SystemInv
import JoltConstraints.WholeRun.Bundles
import JoltConstraints.WholeRun.BlockStep

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace WholeRun

attribute [local instance] Classical.propDecidable

-- Reuse the established implementation lemmas without changing their modules.
local macro "bridgeHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.Bridge
    (`WholeRun ++ n.getId)))
local macro "blockHelper%" n:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JoltConstraints.WholeRun.BlockStep
    (`WholeRun ++ n.getId)))

/-- The raw row program of a RISC-V block is its honest instruction run.
For example, the patched division advice is the advice computed from its sources. -/
theorem blockInstrs_run (i : RiscvInstruction) (address : BitVec 64) (compressed : Bool)
    (js : SailJoltState) (instrs : List Instr)
    (hblock : blockInstrs ⟨address, .riscv i, compressed⟩ js = some instrs) :
    execProgram (Program.seq instrs) js = RiscvInstruction.joltRun (honestInstr i js) js := by
  have hex : ∃ e, (SourceInstruction.riscv i).expand = some e := by
    cases i <;> exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hex
  rw [(bridgeHelper% blockInstrs_eq) he hblock]
  exact (bridgeHelper% expanded_exec) i js e he

private theorem trapFinish_run (s : SailState) (hi : Step.StepInvariant s)
    (pc : BitVec 64) (hn : s.regs.get? Register.nextPC = some pc) :
    Step.trapFinish s = .ok false (Step.setReg s Register.PC pc) := by
  have hp : (Step.setReg s Register.PC pc).regs.get? Register.PC = some pc := by
    simp [Step.setReg]
  simp [Step.trapFinish, tick_pc, readReg_eq_of_get? _ _ _ hi.active,
    readReg_eq_of_get? _ _ _ hn, readReg_eq_of_get? _ _ _ hp, hart_is_active,
    Step.writeReg_run, pc_write_callback, bind, EStateM.bind, pure, EStateM.pure]

private theorem ecall_regs (pre : SailJoltState) (s : SailState) (pc m : BitVec 64)
    (oldInc inc compressed : Bool)
    (hr : s.regs = (sailRegs pre pc m oldInc).regs) :
    (Step.setReg (System.systemProject (SystemProofs.ecallPost
      (Step.preludeJolt { pre with sail := s } inc pc 4) pc (BitVec.addInt pc 4)))
      Register.PC (jolt_jalr_target64 (pre.vregs trapHandlerVReg) 0#64)).regs =
    (sailRegs (SystemProofs.ecallPost (advance_pc pc compressed pre) pc
      (pc + if compressed then 2 else 4))
      (jolt_jalr_target64 (pre.vregs trapHandlerVReg) 0#64) m inc).regs := by
  simp only [Step.setReg, SystemProofs.ecallPost, Step.preludeJolt,
    Step.preludeState, sailRegs, System.systemProject, System.setNextPCState, advance_pc, hr]
  apply Std.ExtDHashMap.ext_get?
  intro r
  by_cases hk : Register.PC = r ∨ Register.nextPC = r ∨ Register.mtvec = r ∨
      Register.mscratch = r ∨ Register.mepc = r ∨ Register.mcause = r ∨
      Register.mtval = r ∨ Register.mstatus = r ∨ Register.reservation_valid = r ∨
      Register.reservation_addr = r ∨ Register.reservation_width = r ∨
      Register.minstret = r ∨ Register.minstret_increment = r ∨ Register.pma_regions = r ∨
      Register.misa = r
  · rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst r
    all_goals simp [Std.ExtDHashMap.get?_insert, trapHandlerVReg, mscratchVReg,
      mepcVReg, mcauseVReg, mtvalVReg, mstatusVReg, reservationWReg, reservationDReg,
      inlineTmp0, riscvRegisterBase, riscvRegisterCount, inlineTmp, inlineRegisterBase,
      numReservedVirtualRegisters, Step.setReg, System.systemProject, sailRegs]
  · simp only [not_or] at hk
    obtain ⟨hPC, hnPC, htv, hscr, hepc, hcause, htval, hstatus,
      hvalid, haddr, hwidth, hm, hinc, hpma, hmisa⟩ := hk
    simp [*, Std.ExtDHashMap.get?_insert, Step.setReg, System.systemProject, sailRegs]

/-- An ECALL block enters the Machine-mode trap handler in one Sail step.
The system values and even PC are run invariants, and `hinputs` comes from
fetching and decoding; for example, ECALL at 16 saves 16 in mepc. -/
theorem block_simulates_ecall (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (hrow : b.row.instruction = .riscv .ECALL)
    (hsys : SystemInv b.pre) (hpcEven : b.row.address.getLsbD 0 = false)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ (inc : Bool) (w : BitVec 32),
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok (.F_Base w) (Step.setReg s .minstret_increment inc) ∧
        ext_decode w (Step.setReg s .minstret_increment inc) =
          .ok (.ECALL ()) (Step.setReg s .minstret_increment inc)) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  intro s hrel
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  obtain ⟨inc, w, hinc, hfetch, hdecode⟩ := hinputs s hrel pc m oldInc hnext hregs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  let js : SailJoltState := { b.pre with sail := s }
  have hproject : System.systemProject js = s := ghost_projects hrel
  have hpc : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have htry := RiscvInstruction.joltStep_eq_try_step_ecall 0 js
    (by rw [hproject]; exact hrel.inv) inc hinc pc hpc w
    (by simpa only [hproject] using hfetch) (by simpa only [hproject] using hdecode)
    hsys.mstatus_bits hsys.mtvec_mode
  rw [hproject] at htry
  let jp := Step.preludeJolt js inc pc 4
  let gp := SystemProofs.ecallPost jp pc (BitVec.addInt pc 4)
  let target := jolt_jalr_target64 (b.pre.vregs trapHandlerVReg) 0#64
  have hpj : jp.sail.regs.get? Register.PC = some pc := by
    simpa [jp, js, Step.preludeJolt, Step.preludeState, Step.setReg_get?_ne] using hpc
  have hnj : jp.sail.regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    simp [jp, Step.preludeJolt, Step.preludeState, Step.setReg]
  have hrun := SystemProofs.ecallProgram_run jp pc _ hpj hnj
  have hip : Step.StepInvariant (System.systemProject jp) := by
    rw [Step.systemProject_preludeJolt, hproject]
    exact hrel.inv.preludeState inc pc 4
  have hf := Step.execProgram_regFrame ecallProgram jp
  rw [hrun] at hf
  have hig : Step.StepInvariant (System.systemProject gp) := hip.systemProject_regFrame hf
  have htarget : (System.systemProject gp).regs.get? Register.nextPC = some target := by
    simp [gp, SystemProofs.ecallPost, System.setNextPCState, System.systemProject,
      jp, Step.preludeJolt, js, target, Step.setReg, Std.ExtDHashMap.get?_insert]
  let s' := Step.setReg (System.systemProject gp) Register.PC target
  have hfinish : Step.trapFinish (System.systemProject gp) = .ok false s' :=
    trapFinish_run _ hig target htarget
  have hpre : liftSail (Step.stepPrelude 4) js = .ok () jp := by
    unfold liftSail jp
    rw [Step.stepPrelude_run 4 s inc hinc pc hpc]
    rfl
  have hstep : try_step 0 false s = .ok false s' := by
    rw [← htry]
    unfold Step.joltEcallStep
    simp only [bind, EStateM.bind, hpre, hrun]
    exact (Step.overlayLocal_trapFinish.run gp).trans hfinish
  have hactual := block_program_run b.row b.start b.post ecallProgram
    (by simp [hrow, SourceInstruction.expand])
    (by simp [hrow, SourceInstruction.honestTracerAdvice]) rfl (hruns.executes_riscv hrow)
  have hpa : b.start.sail.regs.get? Register.PC = some pc := by
    simp [Block.start, advance_pc, hp, Std.ExtDHashMap.get?_insert]
  have hna : b.start.sail.regs.get? Register.nextPC =
      some (b.row.address + if b.row.is_compressed then 2 else 4) := by
    simp [Block.start, advance_pc, Std.ExtDHashMap.get?_insert]
  rw [SystemProofs.ecallProgram_run b.start pc _ hpa hna] at hactual
  have hpost : b.post = SystemProofs.ecallPost b.start pc
      (b.row.address + if b.row.is_compressed then 2 else 4) :=
    (EStateM.Result.ok.inj hactual).2.symm
  refine ⟨false, s', hstep, ?_⟩
  have hmem : s'.mem = s.mem := rfl
  have hmemJ : b.post.sail.mem = b.pre.sail.mem := by rw [hpost]; rfl
  have hdev : b.post.jolt_device = b.pre.jolt_device := by rw [hpost]; rfl
  refine
    { regs := ⟨target, m, inc, ?_, ?_⟩
      inv := hig.setReg Register.PC target (by simp [Step.invariantReg])
      htif := ?_
      ram := ?_
      present := ?_
      io := ?_
      panic := ?_
      layout := by rw [hdev]; exact hrel.layout
      outputs_size := by rw [hdev]; exact hrel.outputs_size }
  · simp [hpost, SystemProofs.ecallPost, System.setNextPCState, target,
      Block.start, advance_pc, Std.ExtDHashMap.get?_insert]
  · simpa only [s', gp, jp, js, target, hpost, Block.start, ← hp] using
      ecall_regs b.pre s pc m oldInc inc b.row.is_compressed hregs
  · simpa [s', gp, SystemProofs.ecallPost, jp, js, Step.preludeJolt, Step.preludeState,
      System.systemProject, System.setNextPCState, Step.setReg, Std.ExtDHashMap.get?_insert]
      using hrel.htif
  · intro a ha
    rw [hmem, hmemJ]
    exact hrel.ram a ha
  · intro a hlo hhi
    rw [hdev] at hlo hhi
    rw [hmem]
    exact hrel.present a hlo hhi
  · intro a hlo hhi hflag
    rw [hdev] at hlo hflag ⊢
    rw [hmem]
    exact hrel.io a hlo hhi hflag
  · rw [hdev]
    change b.pre.jolt_device.panic = true ↔ sailPanicWord b.pre.jolt_device s ≠ 0
    exact hrel.panic

private theorem ramAccess_of_sources (i : RiscvInstruction) (s t : SailJoltState)
    (h : ∀ r, sourceValue (.xreg r) t = sourceValue (.xreg r) s)
    (hr : RamAccess i s) : RamAccess i t := by
  cases i <;> simpa only [RamAccess, h] using hr

/-- Every RISC-V block before EBREAK is one Sail step, including trap entry, where Sail
decodes a non-ECALL encoding to `cast` and `cast` executes like the matching instruction
`ast`. This is `block_simulates` for a decoder whose result is not itself `ast`, such as a
compressed parcel; with `cast = ast` the bridge is trivial. The decoded instructions are
part of `hinputs`.
`hsys`, `hpc`, `hlayout` (from `Related`) are run invariants; `hheap` and `hram`
are platform premises, while offsets, instruction matching, width, fetch and
decode come from decoding; for example, LR.W and ECALL use the same conclusion. -/
theorem block_simulates_via (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hbreak : i ≠ .EBREAK) (hsys : SystemInv b.pre)
    (hpc : b.row.address.getLsbD 0 = false) (heven : i.EvenOffsets)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hram : RamAccess i b.start)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool, should_inc_minstret .Machine s = .ok inc s ∧
        (if i = .ECALL then
          ∃ w : BitVec 32,
            fetch () (Step.setReg s .minstret_increment inc) =
              .ok (.F_Base w) (Step.setReg s .minstret_increment inc) ∧
            ext_decode w (Step.setReg s .minstret_increment inc) =
              .ok (.ECALL ()) (Step.setReg s .minstret_increment inc)
        else
          fetch () (Step.setReg s .minstret_increment inc) =
            .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
          ∃ (ast cast : instruction), RiscvInstruction.Matches i ast ∧
          (∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) ∧
          encoding.decode (Step.setReg s .minstret_increment inc) =
            .ok cast (Step.setReg s .minstret_increment inc))) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  by_cases hecall : i = .ECALL
  · subst i
    apply block_simulates_ecall program b hruns hrow hsys hpc
    intro s hrel pc m oldInc hn hr
    obtain ⟨inc, hi, hd⟩ := hinputs s hrel pc m oldInc hn hr
    simp only [ite_true] at hd
    obtain ⟨w, hf, hd⟩ := hd
    exact ⟨inc, w, hi, hf, hd⟩
  have hlift : i.Lifted := by
    clear hinputs
    cases i <;> simp_all [RiscvInstruction.Lifted]
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes_riscv hrow
  have hraw := blockInstrs_run i b.row.address b.row.is_compressed b.start instrs
    (by simpa only [← hrow] using hblock)
  have hhonest : RiscvInstruction.joltRun (honestInstr i b.start) b.start =
      .ok RETIRE_SUCCESS b.post := hraw.symm.trans hrun
  have hdevice : b.post.jolt_device = b.pre.jolt_device :=
    joltRun_device_of_ram i hlift b.start b.post hram hhonest
  apply block_simulates_retire_via program b hruns i hrow hlift encoding hwidth hdevice
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hi, hdecode⟩ := hinputs s hrel pc m oldInc hn hr
  rw [if_neg hecall] at hdecode
  obtain ⟨hf, ast, cast, hm, hbridge, hd⟩ := hdecode
  have hp : pc = b.row.address := Option.some.inj (hn.symm.trans hruns.continues)
  let Gs := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  have hshadow : Shadow ((blockHelper% overlayRows) b.pre.vregs m inc b.start) Gs :=
    (blockHelper% prelude_shadow) b s pc m oldInc inc hp hr hrel.ram
  have hadvice : blockInstrs b.row Gs = blockInstrs b.row b.start := by
    have he := ((blockHelper% advice_shadow) i _ _ hshadow).trans
      ((blockHelper% advice_overlayRows) i b.pre.vregs m inc b.start)
    simp only [blockInstrs, hrow, he]
  have hpatched := (blockHelper% execProgram_overlayRows) (Program.seq instrs)
    b.pre.vregs m inc b.start b.post hrun
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hpatched] at hsync
  obtain ⟨ghostPost, hghost, _⟩ := hsync.ok_exists
  have hrawG := blockInstrs_run i b.row.address b.row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hlink : System.systemProject Gs = Gs.sail := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, ghost_projects hrel]
    rfl
  have hinv : Step.StepInvariant Gs.sail := hrel.inv.preludeState inc pc _
  have hramG : RamAccess i Gs := ramAccess_of_sources i b.start Gs
    (fun r => ((blockHelper% sourceValue_shadow) hshadow r).trans
      ((blockHelper% sourceValue_overlayRows) b.pre.vregs m inc b.start r)) hram
  obtain ⟨hb, ha⟩ := equivAssumptions_of_retire i hlift Gs (hsys.of_vregs rfl)
    hlink hinv hsys.mstatus_bits hrel.layout heven
    (by
      intro pc' hread
      have heq : pc' = pc := Option.some.inj (hread.symm.trans (by
        simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg_get?_ne,
          hr, sailRegs, System.systemProject, Step.setReg, Std.ExtDHashMap.get?_insert]))
      simpa only [heq, hp] using hpc)
    hheap
    (by simp [Gs, Step.preludeJolt, Step.preludeState, Step.setReg, hr,
      sailRegs, Std.ExtDHashMap.get?_insert])
    (by simpa [Gs, Step.preludeJolt, Step.preludeState, Step.setReg,
      Std.ExtDHashMap.get?_insert] using hrel.htif)
    hrel.present hramG ⟨ghostPost, hrawG.symm.trans hghost⟩
  exact ⟨inc, hi, hf, ast, cast, hm, hbridge, hd, hb, ha⟩

/-- Every RISC-V block before EBREAK is one Sail step, including trap entry.
`hsys`, `hpc`, `hlayout` (from `Related`) are run invariants; `hheap` and `hram`
are platform premises, while offsets, instruction matching, width, fetch and
decode come from decoding; for example, LR.W and ECALL use the same conclusion. -/
theorem block_simulates (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hbreak : i ≠ .EBREAK) (hsys : SystemInv b.pre)
    (hpc : b.row.address.getLsbD 0 = false) (heven : i.EvenOffsets)
    (hheap : b.pre.jolt_device.memory_layout.heap_end.toNat ≤ 2 ^ 64 - 8)
    (hram : RamAccess i b.start)
    (ast : instruction) (hm : RiscvInstruction.Matches i ast)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool, should_inc_minstret .Machine s = .ok inc s ∧
        (if i = .ECALL then
          ∃ w : BitVec 32,
            fetch () (Step.setReg s .minstret_increment inc) =
              .ok (.F_Base w) (Step.setReg s .minstret_increment inc) ∧
            ext_decode w (Step.setReg s .minstret_increment inc) =
              .ok (.ECALL ()) (Step.setReg s .minstret_increment inc)
        else
          fetch () (Step.setReg s .minstret_increment inc) =
            .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
          encoding.decode (Step.setReg s .minstret_increment inc) =
            .ok ast (Step.setReg s .minstret_increment inc))) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  refine block_simulates_via program b hruns i hrow hbreak hsys hpc heven hheap hram encoding
    hwidth ?_
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hinc, hd⟩ := hinputs s hrel pc m oldInc hn hr
  refine ⟨inc, hinc, ?_⟩
  by_cases hecall : i = .ECALL
  · simpa only [hecall, ite_true] using hd
  · simp only [hecall, ite_false] at hd ⊢
    exact ⟨hd.1, ast, ast, hm, fun _ _ => rfl, hd.2⟩

end WholeRun
