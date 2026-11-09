import JoltConstraints.WholeRun.Relation
import JoltConstraints.WholeRun.Bridge
import JoltConstraints.WholeRun.Ghost
import JoltConstraints.WholeRun.NonInterference
import JoltConstraints.layout_facts
import JoltBytecode.Step.Invariant

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- Overlay the fixed system-register values `cs`, retirement count `m`,
increment flag `inc`, and platform regions onto a Jolt state.
For example, zero reservation virtual registers give an invalid reservation,
and a zero mstatus virtual register gives Sail mstatus `0x1800`. -/
private def overlayRows (cs : BitVec 7 → BitVec 64) (m : BitVec 64) (inc : Bool)
    (js : SailJoltState) : SailJoltState :=
  withReg (withReg (withReg (withReg (withReg (withReg (withReg (withReg (withReg
    (withReg (withReg (withReg js
    .mtvec (cs trapHandlerVReg)) .mscratch (cs mscratchVReg)) .mepc (cs mepcVReg))
    .mcause (cs mcauseVReg)) .mtval (cs mtvalVReg)) .mstatus (cs mstatusVReg ||| 0x1800#64))
    .reservation_valid (cs reservationWReg != 0#64)) .reservation_addr (cs reservationWReg))
    .reservation_width (System.reservationWidth (cs reservationWReg) (cs reservationDReg)))
    .minstret m) .minstret_increment inc) .pma_regions platformPma

private theorem execProgram_overlayRows (p : Program) (cs : BitVec 7 → BitVec 64)
    (m : BitVec 64) (inc : Bool) (s t : SailJoltState) (v : ExecutionResult)
    (h : execProgram p s = .ok v t) :
    execProgram p (overlayRows cs m inc s) = .ok v (overlayRows cs m inc t) := by
  simp only [overlayRows,
    execProgram_withReg p .pma_regions (by trivial),
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
    execProgram_withReg p .mtvec (by trivial), h, mapState]

-- All register-map algebra below concerns this small set of keys.
local macro "overlay_keys" " => " finish:tactic : tactic =>
  `(tactic|
    (intro r
     by_cases hkey : Register.PC = r ∨ Register.nextPC = r ∨ Register.mtvec = r ∨
       Register.mscratch = r ∨ Register.mepc = r ∨ Register.mcause = r ∨
       Register.mtval = r ∨ Register.mstatus = r ∨ Register.reservation_valid = r ∨
       Register.reservation_addr = r ∨ Register.reservation_width = r ∨ Register.minstret = r ∨
       Register.minstret_increment = r ∨ Register.pma_regions = r
     · rcases hkey with he | he | he | he | he | he | he | he | he | he | he | he | he | he
       all_goals (subst r; $finish)
     · simp only [not_or] at hkey
       obtain ⟨hPC, hnPC, htv, hscr, hepc, hcause, htval, hstatus,
         hvalid, haddr, hwidth, hm, hinc, hpma⟩ := hkey
       $finish))

private theorem ghost_projects {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    System.systemProject { jt with sail := s } = s := by
  obtain ⟨pc, m, inc, _, hregs⟩ := h.regs
  have he : (System.systemProject { jt with sail := s }).regs = s.regs := by
    simp only [System.systemProject, hregs, sailRegs, Step.setReg]
    apply Std.ExtDHashMap.ext_get?
    overlay_keys => simp [*, Std.ExtDHashMap.get?_insert]
  cases s with
  | mk regs choice mem tags count output =>
    exact congrArg (fun r => (SequentialState.mk r choice mem tags count output : SailState)) he

private theorem prelude_shadow (b : Block) (s : SailState) (pc m : BitVec 64)
    (oldInc inc : Bool) (hp : pc = b.row.address)
    (hregs : s.regs = (sailRegs b.pre pc m oldInc).regs)
    (hram : ∀ a, RAM_START_ADDRESS ≤ a →
      Mmu.ram_byte s.mem a = Mmu.ram_byte b.pre.sail.mem a) :
    Shadow (overlayRows b.pre.vregs m inc b.start)
      (Step.preludeJolt { b.pre with sail := s } inc pc
        (if b.row.is_compressed then 2 else 4)) := by
  subst pc
  have hlen : BitVec.addInt b.row.address (if b.row.is_compressed then 2 else 4) =
      b.row.address + (if b.row.is_compressed then 2 else 4 : BitVec 64) := by
    cases b.row.is_compressed <;> rfl
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [Step.preludeJolt, Step.preludeState, hregs, sailRegs,
      overlayRows, withReg, Step.setReg, System.systemProject, Block.start, advance_pc]
    apply Std.ExtDHashMap.ext_get?
    overlay_keys => simp [*, Std.ExtDHashMap.get?_insert]
  · intro a ha
    change Mmu.ram_byte s.mem a = Mmu.ram_byte b.pre.sail.mem a
    exact hram a ha

private theorem sourceValue_overlayRows (cs : BitVec 7 → BitVec 64) (m : BitVec 64)
    (inc : Bool) (js : SailJoltState) (r : regidx) :
    sourceValue (.xreg r) (overlayRows cs m inc js) = sourceValue (.xreg r) js := by
  cases r
  simp [sourceValue, overlayRows, withReg, Step.setReg, Std.ExtDHashMap.get?_insert]

private theorem sourceValue_shadow {js g : SailJoltState} (h : Shadow js g) (r : regidx) :
    sourceValue (.xreg r) g = sourceValue (.xreg r) js := by
  cases r
  simp only [sourceValue, h.regs]

private theorem advice_shadow (i : RiscvInstruction) (js g : SailJoltState)
    (h : Shadow js g) :
    (SourceInstruction.riscv i).honestTracerAdvice g =
      (SourceInstruction.riscv i).honestTracerAdvice js := by
  cases i <;> simp only [SourceInstruction.honestTracerAdvice, sourceValue_shadow h]

private theorem advice_overlayRows (i : RiscvInstruction) (cs : BitVec 7 → BitVec 64)
    (m : BitVec 64) (inc : Bool) (js : SailJoltState) :
    (SourceInstruction.riscv i).honestTracerAdvice (overlayRows cs m inc js) =
      (SourceInstruction.riscv i).honestTracerAdvice js := by
  cases i <;> simp only [SourceInstruction.honestTracerAdvice, sourceValue_overlayRows]

private theorem honest_lifted (i : RiscvInstruction) (js : SailJoltState) (hi : i.Lifted) :
    (honestInstr i js).Lifted := by
  cases i <;> exact hi

private theorem honest_matches (i : RiscvInstruction) (js : SailJoltState)
    (ast : instruction) (hm : RiscvInstruction.Matches i ast) :
    RiscvInstruction.Matches (honestInstr i js) ast := by
  cases i <;> exact hm

/-- A fetched instruction's encoding and width.
For example, `base 0x00000013` is the four-byte ADDI encoding, while
`compressed 0x0001` is the two-byte compressed NOP encoding. -/
inductive BlockEncoding where
  | base (bits : BitVec 32)
  | compressed (bits : BitVec 16)

/-- Whether the fetched encoding occupies two bytes; for example, a base ADD
encoding returns false. -/
def BlockEncoding.isCompressed : BlockEncoding → Bool
  | .base _ => false
  | .compressed _ => true

/-- The encoding as a fetch result; for example, a base ADD is `F_Base`. -/
def BlockEncoding.fetched : BlockEncoding → FetchResult
  | .base w => .F_Base w
  | .compressed c => .F_RVC c

/-- The instruction bits supplied to Sail's retirement code, padded to 32 bits;
for example, compressed NOP has bits `0x00000001`. -/
def BlockEncoding.bits : BlockEncoding → BitVec 32
  | .base w => zero_extend (m := 32) w
  | .compressed c => zero_extend (m := 32) c

/-- Sail's decoder for the encoding, for example `ext_decode` on a base word. -/
def BlockEncoding.decode : BlockEncoding → SailM instruction
  | .base w => ext_decode w
  | .compressed c => ext_decode_compressed c

private theorem encoding_try_step (e : BlockEncoding) (s : SailState)
    (hinv : Step.StepInvariant s) (inc : Bool)
    (hinc : should_inc_minstret .Machine s = .ok inc s) (pc : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) (ast : instruction)
    (hf : fetch () (Step.setReg s .minstret_increment inc) =
      .ok e.fetched (Step.setReg s .minstret_increment inc))
    (hd : e.decode (Step.setReg s .minstret_increment inc) =
      .ok ast (Step.setReg s .minstret_increment inc)) :
    try_step 0 false s = Step.executeAndFinish ast e.bits
      (Step.preludeState s inc pc (if e.isCompressed then 2 else 4)) := by
  cases e with
  | base w => exact Step.try_step_base 0 s hinv inc hinc pc hpc w ast hf hd
  | compressed c => exact Step.try_step_compressed 0 s hinv inc hinc pc hpc c ast hf hd

/-- Executing a decoded instruction `cast` and executing the instruction `ast` it stands for
agree on every invariant state, so the finishing steps agree.
For example, a compressed C.MV and its ADD expansion retire the same way. -/
theorem executeAndFinish_congr (cast ast : instruction) (bits : BitVec 32) (s : SailState)
    (hs : Step.StepInvariant s)
    (h : ∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) :
    Step.executeAndFinish cast bits s = Step.executeAndFinish ast bits s := by
  unfold Step.executeAndFinish
  simp only [bind, EStateM.bind, h s hs]

private def finishState (s : SailState) (pc m : BitVec 64) (inc : Bool) : SailState :=
  if inc then Step.setReg (Step.setReg s .PC pc) .minstret (BitVec.addInt m 1)
  else Step.setReg s .PC pc

private theorem finish_run (s : SailState) (hinv : Step.StepInvariant s)
    (bits : BitVec 32) (pc m : BitVec 64) (inc : Bool)
    (hpc : s.regs.get? Register.nextPC = some pc)
    (hm : s.regs.get? Register.minstret = some m)
    (hi : s.regs.get? Register.minstret_increment = some inc) :
    Step.stepFinish (.Step_Execute (RETIRE_SUCCESS, bits)) s =
      .ok false (finishState s pc m inc) := by
  unfold Step.stepFinish tick_pc
  simp only [RETIRE_SUCCESS, get_config_rvfi, Bool.false_eq_true, ↓reduceIte]
  simp only [readReg_eq_of_get? _ s _ hinv.active, hart_is_active,
    LeanRV64D.sail_assert, Sail.ConcurrencyInterfaceV1.PreSail.sail_assert,
    bind, EStateM.bind, pure, EStateM.pure, ↓reduceIte]
  rw [readReg_eq_of_get? _ s _ hpc]
  simp only [Step.writeReg_run]
  have hpc' : (Step.setReg s .PC pc).regs.get? Register.PC = some pc := by
    simp [Step.setReg]
  have hm' : (Step.setReg s .PC pc).regs.get? Register.minstret = some m := by
    rwa [Step.setReg_get?_ne _ _ (by decide)]
  have hi' : (Step.setReg s .PC pc).regs.get? Register.minstret_increment = some inc := by
    rwa [Step.setReg_get?_ne _ _ (by decide)]
  simp only [andM, toBool, bind, EStateM.bind, EStateM.pure,
    readReg_eq_of_get? _ _ _ hpc', pc_write_callback,
    readReg_eq_of_get? _ _ _ hi']
  cases inc <;> simp only [Bool.false_eq_true, ↓reduceIte, readReg_eq_of_get? _ _ _ hm',
    Step.writeReg_run, EStateM.bind, EStateM.pure, finishState]

private theorem finish_regs (pre post ghost : SailJoltState) (m pc : BitVec 64)
    (inc : Bool) (h : Shadow (overlayRows pre.vregs m inc post) ghost) :
    (finishState (System.systemProject ghost) pc m inc).regs =
      (sailRegs post pc (if inc then BitVec.addInt m 1 else m) inc).regs := by
  have hr := h.regs
  have hv := h.vregs
  simp only [finishState, sailRegs, System.systemProject, hr, hv, overlayRows,
    withReg, Step.setReg]
  cases inc <;> apply Std.ExtDHashMap.ext_get?
  all_goals overlay_keys => simp [*, Std.ExtDHashMap.get?_insert]

private theorem projected_reads (pre post ghost : SailJoltState) (m : BitVec 64)
    (inc : Bool) (h : Shadow (overlayRows pre.vregs m inc post) ghost) :
    (System.systemProject ghost).regs.get? Register.nextPC = post.sail.regs.get? .nextPC ∧
    (System.systemProject ghost).regs.get? Register.minstret = some m ∧
    (System.systemProject ghost).regs.get? Register.minstret_increment = some inc := by
  have hr := h.regs
  simp [System.systemProject, hr, overlayRows, withReg, Step.setReg,
    Std.ExtDHashMap.get?_insert]

private theorem finish_mem (s : SailState) (pc m : BitVec 64) (inc : Bool) :
    (finishState s pc m inc).mem = s.mem := by
  cases inc <;> rfl

private theorem panicWord_eq {device : JoltDevice} {s t : SailState}
    (bound : device.memory_layout.panic.toNat + 8 ≤ RAM_START_ADDRESS)
    (h : ∀ a, a < RAM_START_ADDRESS → t.mem.get? a = s.mem.get? a) :
    sailPanicWord device t = sailPanicWord device s := by
  unfold sailPanicWord read_doubleword?
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A retiring lifted source block is one Sail `try_step`, where Sail decodes the fetched
encoding to `cast` and `cast` executes like the matching instruction `ast`.
This is `block_simulates_retire` for a decoder whose result is not itself `ast`, such as a
compressed parcel decoded to a compressed AST that runs as its base expansion; with
`cast = ast` the bridge is trivial. The decoded instructions come with the fetch, since
they are facts about the state Sail runs from.
The per-instruction hypotheses supply Sail's fetch and decode and the existing
equivalence assumptions after the prelude, with honest advice.
Retirement follows from `Block.Runs`, and the unchanged device preserves its
layout and output buffer.
For example, an ADD block uses the base encoding case and has no memory or
advice obligations beyond its existing instruction-equivalence assumptions. -/
theorem block_simulates_retire_via (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hi : i.Lifted)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hdevice : b.post.jolt_device = b.pre.jolt_device)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        ∃ (ast cast : instruction), RiscvInstruction.Matches i ast ∧
        (∀ t, Step.StepInvariant t → Step.executeFull cast t = Step.executeFull ast t) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok cast (Step.setReg s .minstret_increment inc) ∧
        ∃ h : RiscvInstruction.equivAssumptions
          (honestInstr i (Step.preludeJolt { b.pre with sail := s } inc pc
            (if b.row.is_compressed then 2 else 4)))
          (Step.preludeJolt { b.pre with sail := s } inc pc
            (if b.row.is_compressed then 2 else 4)),
          RiscvInstruction.AdviceHonest
            (honestInstr i (Step.preludeJolt { b.pre with sail := s } inc pc
              (if b.row.is_compressed then 2 else 4)))
            (Step.preludeJolt { b.pre with sail := s } inc pc
              (if b.row.is_compressed then 2 else 4)) h) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  intro s hrel
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  obtain ⟨inc, hinc, hfetch, ast, cast, hm, hbridge, hdecode, hequiv, hadv⟩ :=
    hinputs s hrel pc m oldInc hnext hregs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  let Gs := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  have hshadow : Shadow (overlayRows b.pre.vregs m inc b.start) Gs :=
    prelude_shadow b s pc m oldInc inc hp hregs hrel.ram
  obtain ⟨instrs, hblock, hrun⟩ := hruns.executes
  have hadvice : blockInstrs b.row Gs = blockInstrs b.row b.start := by
    have he := (advice_shadow i _ _ hshadow).trans
      (advice_overlayRows i b.pre.vregs m inc b.start)
    simp only [blockInstrs, hrow, he]
  have hpatched := execProgram_overlayRows (Program.seq instrs) b.pre.vregs m inc
    b.start b.post RETIRE_SUCCESS hrun
  have hsync := execProgram_shadow (Program.seq instrs) _ _ hshadow
  rw [hpatched] at hsync
  obtain ⟨ghostPost, hghost, hpost, _, hmem⟩ := hsync.ok_exists
  have hproject := blockInstrs_project i b.row.address b.row.is_compressed Gs instrs
    (by simpa only [← hrow] using hadvice.trans hblock)
  have hexec : execute ast (System.systemProject Gs) =
      .ok RETIRE_SUCCESS (System.systemProject ghostPost) := by
    rw [← RiscvInstruction.joltRun_eq_execute (honestInstr i Gs) (honest_lifted i Gs hi)
      ast (honest_matches i Gs ast hm) Gs hequiv hadv, ← hproject, hghost]
    rfl
  have hGp : System.systemProject Gs = Step.preludeState s inc pc
      (if b.row.is_compressed then 2 else 4) := by
    dsimp only [Gs]
    rw [Step.systemProject_preludeJolt, ghost_projects hrel]
  have hinvPre : Step.StepInvariant (System.systemProject Gs) := by
    rw [hGp]
    exact hrel.inv.preludeState inc pc _
  have hframe := Step.execProgram_regFrame (Program.seq instrs) Gs
  rw [hghost] at hframe
  change Step.RegFrame Gs ghostPost at hframe
  have hinvPost := hinvPre.systemProject_regFrame hframe
  obtain ⟨next, hnextGhost⟩ := (hinvPost.present Register.nextPC).exists_value
  obtain ⟨hn, hcount, hcountInc⟩ := projected_reads b.pre b.post ghostPost m inc hpost
  have hnextPost : b.post.sail.regs.get? Register.nextPC = some next := hn.symm.trans hnextGhost
  let s' := finishState (System.systemProject ghostPost) next m inc
  have hfinish := finish_run (System.systemProject ghostPost) hinvPost encoding.bits
    next m inc hnextGhost hcount hcountInc
  have hpc : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert,
      System.systemProject]
  have htry := encoding_try_step encoding s hrel.inv inc hinc pc hpc cast hfetch hdecode
  have hstep : try_step 0 false s = .ok false s' := by
    rw [htry]
    simp only [← hwidth]
    rw [← hGp, executeAndFinish_congr cast ast _ _ hinvPre hbridge]
    unfold Step.executeAndFinish Step.executeFull
    simp only [bind, EStateM.bind, hexec, RETIRE_SUCCESS, pure, EStateM.pure]
    exact hfinish
  refine ⟨false, s', hstep, ?_⟩
  have hmem' : s'.mem = ghostPost.sail.mem := finish_mem _ next m inc
  have hbelow : ∀ a, a < RAM_START_ADDRESS → s'.mem.get? a = s.mem.get? a := by
    intro a ha
    rw [hmem']
    exact hmem.below a ha
  have hhtif : (System.systemProject ghostPost).regs.get? Register.htif_tohost_base = some none := by
    rw [Step.systemProject_get?_of_not_overlaid _ (by simp [Step.Overlaid]),
      hframe.keep Register.htif_tohost_base (by simp [Step.JoltWritable])]
    change (Step.preludeState s inc pc _).regs.get? Register.htif_tohost_base = some none
    simpa [Step.preludeState, Step.setReg, Std.ExtDHashMap.get?_insert] using hrel.htif
  refine
    { regs := ⟨next, (if inc then BitVec.addInt m 1 else m), inc, hnextPost,
        finish_regs b.pre b.post ghostPost m next inc hpost⟩
      inv := hinvPost.stepFinish_retire encoding.bits hfinish
      htif := ?_
      ram := ?_
      present := ?_
      io := ?_
      panic := ?_
      layout := by rw [hdevice]; exact hrel.layout
      outputs_size := by rw [hdevice]; exact hrel.outputs_size }
  · change (finishState _ next m inc).regs.get? Register.htif_tohost_base = some none
    cases inc <;> simpa [finishState, Step.setReg, Std.ExtDHashMap.get?_insert] using hhtif
  · intro a ha
    rw [hmem']
    exact hpost.ram a ha
  · intro a hlo hhi
    rw [hdevice] at hlo hhi
    obtain ⟨byte, hb⟩ := hrel.present a hlo hhi
    have hs : (Gs.sail.mem.get? a).isSome := by
      change (s.mem.get? a).isSome
      rw [hb]
      rfl
    have hpresent := hmem.present a hs
    rw [← hmem'] at hpresent
    exact Option.isSome_iff_exists.mp hpresent
  · intro a hlo hhi hflag
    rw [hdevice] at hlo hflag ⊢
    exact (hbelow a hhi).trans (hrel.io a hlo hhi hflag)
  · rw [hdevice]
    obtain ⟨config, hconfig⟩ := hrel.layout
    obtain ⟨_, _, hterm, hend, hbound⟩ := new_io_geometry config _ hconfig
    rw [panicWord_eq (by omega) hbelow]
    exact hrel.panic

/-- A retiring lifted source block is one Sail `try_step`, for either a base
or compressed encoding.
The per-instruction hypotheses supply Sail's fetch and decode and the existing
equivalence assumptions after the prelude, with honest advice.
Retirement follows from `Block.Runs`, and the unchanged device preserves its
layout and output buffer.
For example, an ADD block uses the base encoding case and has no memory or
advice obligations beyond its existing instruction-equivalence assumptions. -/
theorem block_simulates_retire (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (i : RiscvInstruction) (hrow : b.row.instruction = .riscv i)
    (hi : i.Lifted) (ast : instruction) (hm : RiscvInstruction.Matches i ast)
    (encoding : BlockEncoding) (hwidth : b.row.is_compressed = encoding.isCompressed)
    (hdevice : b.post.jolt_device = b.pre.jolt_device)
    (hinputs : ∀ (s : SailState), Related b.pre s →
      ∀ (pc m : BitVec 64) (oldInc : Bool),
      b.pre.sail.regs.get? Register.nextPC = some pc →
      s.regs = (sailRegs b.pre pc m oldInc).regs →
      ∃ inc : Bool,
        should_inc_minstret .Machine s = .ok inc s ∧
        fetch () (Step.setReg s .minstret_increment inc) =
          .ok encoding.fetched (Step.setReg s .minstret_increment inc) ∧
        encoding.decode (Step.setReg s .minstret_increment inc) =
          .ok ast (Step.setReg s .minstret_increment inc) ∧
        ∃ h : RiscvInstruction.equivAssumptions
          (honestInstr i (Step.preludeJolt { b.pre with sail := s } inc pc
            (if b.row.is_compressed then 2 else 4)))
          (Step.preludeJolt { b.pre with sail := s } inc pc
            (if b.row.is_compressed then 2 else 4)),
          RiscvInstruction.AdviceHonest
            (honestInstr i (Step.preludeJolt { b.pre with sail := s } inc pc
              (if b.row.is_compressed then 2 else 4)))
            (Step.preludeJolt { b.pre with sail := s } inc pc
              (if b.row.is_compressed then 2 else 4)) h) :
    ∀ s, Related b.pre s → ∃ v s', try_step 0 false s = .ok v s' ∧ Related b.post s' := by
  refine block_simulates_retire_via program b hruns i hrow hi encoding hwidth hdevice ?_
  intro s hrel pc m oldInc hn hr
  obtain ⟨inc, hinc, hf, hd, h, hadv⟩ := hinputs s hrel pc m oldInc hn hr
  exact ⟨inc, hinc, hf, ast, ast, hm, fun _ _ => rfl, hd, h, hadv⟩

end WholeRun
