import JoltConstraints.WholeRun.InlineSoundness
import JoltConstraints.WholeRun.Top

/-!
# Sail plus a platform step for inline calls (R5)

Sail's RISC-V model has no instruction for Jolt's registered inlines: their words use the
custom-0 opcode `0x0B`, which Sail traps as illegal. This file runs Sail together with a
platform step for those words (decision D1 of the inline plan) and proves that Sail plus the
platform reproduces every run Jolt's soundness theorem accepts, for guests that call the twelve
registered inlines.

* `PlatformStep` is one step of the platform. When Sail's prelude and fetch find a base word that
  `InlineEncoding.register` accepts as the call `key rd, rs1, rs2`, the platform runs the call:
  it keeps the frame of the call's write set, and it meets the call's specification
  (`InlineKey.Spec`, copied from the per-call soundness theorems) when the call's precondition
  (`InlineKey.Pre`) holds and its inputs lie in RAM (`InlineKey.InputsInRam`). Sail's retiring
  finish then moves `PC` past the four-byte word. On every other word, the platform runs Sail's
  `try_step`.
* `PlatformRun n s s'` chains `n` platform steps.
* `PlatformConforms` is `BlockConforms` without its `riscv` field: a block may run a RISC-V row
  or an inline row, and an inline row's stores must land in RAM, outside the code.
* `HonestTrace.sail_reproduces_with_inlines` and `JoltInstance.sail_soundness_with_inlines`
  are `HonestTrace.sail_reproduces` and `JoltInstance.sail_soundness` with `PlatformRun` in
  place of `sailRun` and `PlatformConforms` in place of `BlockConforms`. Every block that
  satisfies `BlockConforms` satisfies `PlatformConforms` (`BlockConforms.platformConforms`).

The platform step reads the call's operands and memory through a Jolt view `J` of Sail's state:
`J.sail` is Sail's state after the prelude, and its virtual registers and device are any. The
specifications read memory through Jolt's loads, which read Sail's RAM bytes in RAM. The guard
`InlineKey.InputsInRam` asks every input buffer to lie in RAM, so where the guard holds the
specification reads only Sail's memory. The platform keeps Sail's registers and changes only
memory: it finishes from `J.sail` with the memory of the Jolt state `J'` after the call.

The results say nothing about a call whose precondition fails beyond the frame. They do not
say that a guest computes SHA-256 or verifies an ECDSA signature. The specifications keep the
gaps listed in `InlineContract.lean`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1 JoltISA.Inlines.FrameInstances

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-! ## Inline words -/

/-- Every registered inline key has opcode `0x0B`.
Example: `InlineKey.opcode .blake2 = 0x0B`. -/
theorem inlineKey_opcode (key : InlineKey) : key.opcode = 0x0b := by
  cases key <;> rfl

/-- The registry rejects every encoding whose opcode is not `0x0B`.
Example: the ADDI word `0x00100093` has opcode `0x13` and registers no inline. -/
theorem register_of_opcode_ne {encoding : InlineEncoding} (h : encoding.opcode ≠ 0x0b) :
    encoding.register = none := by
  have hfind : InlineKey.ofEncoding encoding.opcode encoding.funct3 encoding.funct7 = none := by
    unfold InlineKey.ofEncoding
    rw [List.find?_eq_none]
    intro key _
    simp only [inlineKey_opcode, Bool.and_eq_true, beq_iff_eq, not_and]
    intro hand _
    exact h hand.1.symm
  unfold InlineEncoding.register
  rw [hfind]

/-- Jolt's decoder decodes no word with opcode `0x0B`.
Example: `joltDecode 0x02B5050B advice = none`. -/
theorem joltDecode_opcode_ne {w : BitVec 32} {advice : BitVec 64} {i : RiscvInstruction}
    (h : Decode.joltDecode w advice = some i) : w.extractLsb 6 0 ≠ 0x0b := by
  intro h0
  have h11 : (w.extractLsb 6 0).toNat = 11 := by rw [h0]; rfl
  simp only [Decode.joltDecode, h11] at h
  simp at h

/-- A word Jolt decodes as a RISC-V instruction is not a registered inline.
Example: the ADDI word `0x00100093` registers no inline. -/
theorem register_none_of_joltDecode {w : BitVec 32} {advice : BitVec 64} {i : RiscvInstruction}
    (h : Decode.joltDecode w advice = some i) : (inlineEncodingOf w).register = none :=
  register_of_opcode_ne (joltDecode_opcode_ne h)

end WholeRun

/-! ## The guard on the inputs -/

namespace JoltISA.Inlines.InlineKey

open WholeRun

/-- The `n` bytes at the address in `r` lie in RAM and do not wrap.
Example: `InRam x11 64 s` holds when `x11` holds `0x80010000`. -/
def InRam (r : regidx) (n : Nat) (s : SailJoltState) : Prop :=
  RAM_START_ADDRESS ≤ (sourceValue (.xreg r) s).toNat ∧
    (sourceValue (.xreg r) s).toNat + n ≤ 2 ^ 64

/-- Every buffer the specification of `key rd, rs1, rs2` reads lies in RAM: the state and the
block of a hash, and the operands of a field operation. `SECP256K1_GLVR_ADV` reads no buffer.
Example: `blake2.InputsInRam x10 x11 s` says that the 64-byte state at `x10` and the 144-byte
message block, counter and flag at `x11` lie in RAM. -/
def InputsInRam : InlineKey → regidx → regidx → SailJoltState → Prop
  | .sha256, rs1, rs2, s => InRam rs1 32 s ∧ InRam rs2 64 s
  | .sha256Init, _, rs2, s => InRam rs2 64 s
  | .keccak256, rs1, _, s => InRam rs1 200 s
  | .keccak256AbsorbPermute, rs1, rs2, s => InRam rs1 200 s ∧ InRam rs2 136 s
  | .blake2, rs1, rs2, s => InRam rs1 64 s ∧ InRam rs2 144 s
  | .secp256k1Mulq, rs1, rs2, s => InRam rs1 32 s ∧ InRam rs2 32 s
  | .secp256k1Mulr, rs1, rs2, s => InRam rs1 32 s ∧ InRam rs2 32 s
  | .secp256k1Squareq, rs1, _, s => InRam rs1 32 s
  | .secp256k1Squarer, rs1, _, s => InRam rs1 32 s
  | .secp256k1Divq, rs1, rs2, s => InRam rs1 32 s ∧ InRam rs2 32 s
  | .secp256k1Divr, rs1, rs2, s => InRam rs1 32 s ∧ InRam rs2 32 s
  | .secp256k1GlvrAdv, _, _, _ => True

/-- No call writes an architectural register.
Example: `(blake2.writeSet x10 x11 x0).xregs = []`. -/
theorem writeSet_xregs (key : InlineKey) (rs1 rs2 rd : regidx) :
    (key.writeSet rs1 rs2 rd).xregs = [] := by
  cases key <;> simp only [writeSet] <;> (try split) <;> rfl

/-- Every call writes a pool of at most 80 virtual registers from `vr48` up.
Example: `(sha256.writeSet x10 x11 x12).vregs = poolVRegs 36`. -/
theorem writeSet_vregs (key : InlineKey) (rs1 rs2 rd : regidx) :
    ∃ n ≤ 80, (key.writeSet rs1 rs2 rd).vregs = poolVRegs n := by
  cases key <;> simp only [writeSet] <;> (try split) <;> exact ⟨_, by decide, rfl⟩

end JoltISA.Inlines.InlineKey

namespace WholeRun

/-- A pool register is at least `vr48`.
Example: `poolVRegs 2 = [vr48, vr49]`. -/
theorem le_of_mem_poolVRegs {n : Nat} (hn : n ≤ 80) {v : BitVec 7} (hv : v ∈ poolVRegs n) :
    48 ≤ v.toNat := by
  simp only [poolVRegs, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  simp only [BitVec.toNat_ofNat]
  omega

/-- A virtual register below `vr48` is outside every call's write set.
Example: the trap-handler register `vr34` keeps its value across a `BLAKE2` call. -/
theorem not_mem_writeSet_vregs (key : InlineKey) (rs1 rs2 rd : regidx) {v : BitVec 7}
    (hv : v.toNat < 48) : v ∉ (key.writeSet rs1 rs2 rd).vregs := by
  obtain ⟨n, hn, heq⟩ := key.writeSet_vregs rs1 rs2 rd
  rw [heq]
  intro hmem
  have := le_of_mem_poolVRegs hn hmem
  omega

/-! ## The platform -/

/-- Sail's prelude at `s` counts the instruction when `inc` holds, and Sail's fetch then
returns the four-byte word `w`.
Example: at a state whose `PC` names the word `0x02B5050B` in memory, `FetchesBase s inc
0x02B5050B` holds for the `inc` Sail's `should_inc_minstret` returns. -/
def FetchesBase (s : SailState) (inc : Bool) (w : BitVec 32) : Prop :=
  should_inc_minstret .Machine s = .ok inc s ∧
    fetch () (Step.setReg s .minstret_increment inc) =
      .ok (.F_Base w) (Step.setReg s .minstret_increment inc)

/-- The next instruction at `s` is not a registered inline: no four-byte word Sail fetches at
`s` registers as an inline call.
Example: a state whose `PC` names an ADDI word, or a compressed parcel, satisfies it. -/
def NotInlineAt (s : SailState) : Prop :=
  ∀ inc w, FetchesBase s inc w → (inlineEncodingOf w).register = none

/-- **One step of Sail plus the platform.**
* `sail`: the next instruction is not a registered inline, and Sail's `try_step` runs it.
* `inline`: Sail's prelude and fetch find a word `w` that registers as the call
  `key rd, rs1, rs2`. Let `J` be a Jolt view of Sail's state after the prelude
  (`J.sail = Step.preludeState s inc pc 4`). The call goes from `J` to some `J'` that keeps the
  frame of the call's write set, and meets the call's specification when its precondition holds
  and its inputs lie in RAM. Sail's retiring finish then runs from `J.sail` with `J'`'s memory.
  So the platform changes Sail's memory as the call does and keeps every Sail register but
  `PC` and `minstret`, which the finish advances.

Example: at a `SHA256` word with its state and block in RAM, the platform stores the
compression of the block into the state at `rs1` and moves `PC` four bytes on. -/
inductive PlatformStep : SailState → SailState → Prop where
  | sail {s s' : SailState} {v : Bool} (notInline : NotInlineAt s)
      (step : try_step 0 false s = .ok v s') : PlatformStep s s'
  | inline {s s' : SailState} {inc : Bool} {pc : BitVec 64} {w : BitVec 32}
      {key : InlineKey} {rs1 rs2 rd : regidx} {J J' : SailJoltState} {v : Bool}
      (pcAt : s.regs.get? Register.PC = some pc)
      (fetched : FetchesBase s inc w)
      (call : (inlineEncodingOf w).register = some (.inline key rs1 rs2 rd))
      (view : J.sail = Step.preludeState s inc pc 4)
      (frame : Frame (key.writeSet rs1 rs2 rd) J J')
      (spec : key.Pre rs1 rs2 rd J → key.InputsInRam rs1 rs2 J → key.Spec rs1 rs2 rd J J')
      (finish : Step.stepFinish (.Step_Execute (RETIRE_SUCCESS, w))
        { J.sail with mem := J'.sail.mem } = .ok v s') : PlatformStep s s'

/-- `PlatformRun n s s'`: `n` platform steps lead from `s` to `s'`.
Example: `PlatformRun 0 s s` for every `s`. -/
inductive PlatformRun : Nat → SailState → SailState → Prop where
  | done (s : SailState) : PlatformRun 0 s s
  | step {n : Nat} {s t u : SailState} (first : PlatformStep s t) (rest : PlatformRun n t u) :
      PlatformRun (n + 1) s u

/-- One block's Jolt step is matched by one platform step under `R`: from every Sail state
related to the block's first Jolt state, some platform step lands in a state related to the
block's last Jolt state.
Example: a conforming ADDI block simulates through a `try_step`. -/
def PlatformSimulates (R : SailJoltState → SailState → Prop) (b : Block) : Prop :=
  ∀ s, R b.pre s → ∃ s', PlatformStep s s' ∧ R b.post s'

/-- **Blocks chain into a platform run.** This is `sailRun_of_chain` for `PlatformRun`.
Example: two simulating blocks give a run of two platform steps. -/
theorem platformRun_of_chain (R : SailJoltState → SailState → Prop) :
    ∀ (bs : List Block), bs.IsChain (fun b c => b.post = c.pre) →
      (∀ b ∈ bs, PlatformSimulates R b) →
      ∀ (first : Block), bs.head? = some first →
      ∀ (s : SailState), R first.pre s →
      ∃ (last : Block) (s' : SailState), bs.getLast? = some last ∧
        PlatformRun bs.length s s' ∧ R last.post s'
  | [], _, _, _, hfirst, _, _ => by simp at hfirst
  | [b], _, hsim, first, hfirst, s, hs => by
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      subst hfirst
      obtain ⟨s', hstep, hs'⟩ := hsim b (by simp) s hs
      exact ⟨b, s', by simp, .step hstep (.done s'), hs'⟩
  | b :: c :: rest, hchain, hsim, first, hfirst, s, hs => by
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      subst hfirst
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hlink, hchain'⟩ := hchain
      obtain ⟨s', hstep, hs'⟩ := hsim b (by simp) s hs
      obtain ⟨last, s'', hlast, hrun, hrel⟩ :=
        platformRun_of_chain R (c :: rest) hchain'
          (fun d hd => hsim d (List.mem_cons_of_mem _ hd)) c rfl s' (hlink ▸ hs')
      refine ⟨last, s'', ?_, ?_, hrel⟩
      · simpa [List.getLast?_cons_cons] using hlast
      · simp only [List.length_cons] at hrun ⊢
        exact .step hstep hrun

/-! ## The relation depends only on registers and memory -/

/-- The step invariant depends only on the registers.
Example: changing memory keeps it. -/
theorem stepInvariant_of_regs {s t : SailState} (h : Step.StepInvariant s)
    (hr : t.regs = s.regs) : Step.StepInvariant t :=
  h.of_agree (fun r _ => by rw [hr]) (fun r => ⟨by rw [hr]; exact (h.present r).exists_value⟩)

/-- `Related` depends only on Sail's registers and memory.
Example: two Sail states that differ only in `cycleCount` are related to the same Jolt states. -/
theorem Related.of_regs_mem {jt : SailJoltState} {s t : SailState} (h : Related jt s)
    (hr : t.regs = s.regs) (hm : t.mem = s.mem) : Related jt t where
  regs := by
    obtain ⟨pc, m, inc, hn, hregs⟩ := h.regs
    exact ⟨pc, m, inc, hn, hr.trans hregs⟩
  inv := stepInvariant_of_regs h.inv hr
  htif := by rw [hr]; exact h.htif
  ram := by intro a ha; rw [hm]; exact h.ram a ha
  present := by intro a h1 h2; rw [hm]; exact h.present a h1 h2
  io := by intro a h1 h2 h3; rw [hm]; exact h.io a h1 h2 h3
  panic := by
    have he : sailPanicWord jt.jolt_device t = sailPanicWord jt.jolt_device s := by
      unfold sailPanicWord
      rw [hm]
    rw [he]
    exact h.panic
  layout := h.layout
  outputs_size := h.outputs_size

/-- The finish's registers depend only on the registers it starts from.
Example: two states with equal registers finish with equal registers. -/
theorem finishState_regs_congr {s t : SailState} (h : t.regs = s.regs) (pc m : BitVec 64)
    (inc : Bool) : (finishState t pc m inc).regs = (finishState s pc m inc).regs := by
  cases inc <;> simp only [finishState, Step.setReg, h, Bool.false_eq_true, ↓reduceIte]

/-! ## An inline block is one platform step -/

/-- A store footprint in RAM leaves the device unchanged: every device store is below RAM.
Example: a `BLAKE2` call whose state lies in RAM keeps the device. -/
theorem device_eq_of_footprint_ram {F : Nat → Prop} (hF : ∀ a, F a → RAM_START_ADDRESS ≤ a)
    {d d' : JoltDevice} (h : Relation.ReflTransGen (DeviceStoreAt F) d d') : d' = d := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨a, v, ha, hlt, -⟩ := hstep
    exact absurd (hF a ha) (by omega)

/-- **A block whose stores avoid the code keeps the code.** If a block keeps the frame of a
write set from `b.start` to `b.post`, and no byte of the write set's footprint is a code byte,
Jolt's memory still holds the code after the block.
Example: an inline call whose output buffer lies in the heap keeps the code. -/
theorem JoltCodeIntact.of_frame {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (hruns : b.Runs program) {ws : WriteSet} (hframe : Frame ws b.start b.post)
    (hno : ∀ a, ws.Footprint b.start a → ¬ IsCodeByte program a)
    (h : JoltCodeIntact program b.pre) : JoltCodeIntact program b.post := by
  refine ⟨by rw [hruns.layout_eq]; exact h.1, ?_⟩
  intro row hrow k hk byte hbyte
  rw [hframe.mem _ fun hf => hno _ hf ⟨row, hrow, k, hk, rfl⟩]
  exact h.2 row hrow k hk byte hbyte

/-- **An inline block is one platform step, and keeps the relation.** A block of a decoded
program whose row is the inline call `key rd, rs1, rs2`, and whose stores land in RAM outside
the code, is matched by one inline platform step that lands in the relation for the block's last
state.
The Jolt view of the step is Sail's state after the prelude with the block's virtual registers
and device. The block's rows, run from that view (`ghost_rows`), give the state `J'` after the
call, and the call's contract (`InlineKey.call_contract`) gives the frame and the
specification.
Example: a `SHA256` block whose state at `rs1` lies in the heap is one platform step that stores
the compression at `rs1`. -/
theorem inline_block_simulates {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) (hrows : program.RowsAligned) {b : Block}
    (hruns : b.Runs program) {key : InlineKey} {rs1 rs2 rd : regidx}
    (call : b.row.instruction = .inline key rs1 rs2 rd)
    (hstores : ∀ a, (key.writeSet rs1 rs2 rd).Footprint b.start a →
      RAM_START_ADDRESS ≤ a ∧ ¬ IsCodeByte program a) :
    PlatformSimulates (RunRel program) b := by
  rintro s ⟨hrel, hinv, hcode⟩
  obtain ⟨pc, m, oldInc, hnext, hregs⟩ := hrel.regs
  have hp : pc = b.row.address := Option.some.inj (hnext.symm.trans hruns.continues)
  obtain ⟨w, hc, hw, hlow, hreg⟩ := hdecoded.inlineDecoded hruns.row_mem call
  obtain ⟨inc, hinc⟩ := exists_should_inc s hrel.inv
  have hpc_s : s.regs.get? Register.PC = some pc := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have hpma_s : s.regs.get? Register.pma_regions = some platformPma := by
    simp [hregs, sailRegs, Step.setReg, Std.ExtDHashMap.get?_insert, System.systemProject]
  have hfetch := base_word_fetch program b.row hruns.row_mem w hc hw hlow
    (Step.setReg s .minstret_increment inc)
    (hrel.inv.setReg _ _ (by simp [Step.invariantReg]))
    (by rw [Step.setReg_get?_ne _ _ (by decide), hpc_s, hp]) (hruns.pc_even hrows)
    (by rw [Step.setReg_get?_ne _ _ (by decide)]; exact hpma_s)
    (by rw [Step.setReg_get?_ne _ _ (by decide)]; exact hrel.htif)
    (show CodeIntact program s from CodeIntact.of_related hrel hcode)
  -- The block's rows, and the device they keep.
  obtain ⟨accepted, values, hrun⟩ := hruns.inline_rows call
  have hcontract := hruns.inline_contract call
  have hdevice : b.post.jolt_device = b.pre.jolt_device :=
    device_eq_of_footprint_ram (fun a ha => (hstores a ha).1) hcontract.1.device
  -- The rows, run from the Jolt view of Sail's state.
  obtain ⟨ghostPost, next, hghost, hn, hcount, hcountInc, hinvPost, -, hrelPost⟩ :=
    ghost_rows program b hruns hdevice s hrel pc m oldInc inc hnext hregs _ hrun w
  let J := Step.preludeJolt { b.pre with sail := s } inc pc
    (if b.row.is_compressed then 2 else 4)
  obtain ⟨hframe, hspec⟩ := InlineKey.call_contract key rs1 rs2 rd accepted values hghost
  have hview : J.sail = Step.preludeState s inc pc 4 := by
    show Step.preludeState s inc pc _ = _
    rw [hc]
    rfl
  -- The call keeps every Sail register, so projecting `J'` changes no register of `J`.
  have hG : System.systemProject J = J.sail := by
    show System.systemProject (Step.preludeJolt _ inc pc _) = _
    rw [Step.systemProject_preludeJolt, ghost_projects hrel]
    rfl
  have hsail : ghostPost.sail.regs = J.sail.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro r
    refine hframe.sailRegs r fun ⟨i, hi, _⟩ => ?_
    rw [InlineKey.writeSet_xregs] at hi
    cases hi
  have hv : ∀ v : BitVec 7, v.toNat < 48 → ghostPost.vregs v = J.vregs v := fun v hv =>
    hframe.vregs v (not_mem_writeSet_vregs key rs1 rs2 rd hv)
  have hsys : (System.systemProject ghostPost).regs = J.sail.regs := by
    have hJ : (System.systemProject J).regs = J.sail.regs := by rw [hG]
    rw [← hJ]
    simp only [System.systemProject, hsail, hv trapHandlerVReg (by decide),
      hv mscratchVReg (by decide), hv mepcVReg (by decide), hv mcauseVReg (by decide),
      hv mtvalVReg (by decide), hv mstatusVReg (by decide), hv reservationWReg (by decide),
      hv reservationDReg (by decide)]
  -- The platform finishes from `J.sail` with the call's memory.
  let X : SailState := { J.sail with mem := ghostPost.sail.mem }
  have hX : X.regs = (System.systemProject ghostPost).regs := hsys.symm
  have hinvX : Step.StepInvariant X := stepInvariant_of_regs hinvPost hX
  have hfinish := finish_run X hinvX w next m inc
    (by show X.regs.get? _ = _; rw [hX]; exact hn)
    (by show X.regs.get? _ = _; rw [hX]; exact hcount)
    (by show X.regs.get? _ = _; rw [hX]; exact hcountInc)
  have hrelX : Related b.post (finishState X next m inc) :=
    hrelPost.of_regs_mem (finishState_regs_congr hX next m inc)
      (by rw [finish_mem, finish_mem]; rfl)
  refine ⟨finishState X next m inc,
    .inline hpc_s ⟨hinc, hfetch⟩ (by rw [hreg, call]) hview hframe
      (fun hpre _ => hspec hpre) hfinish,
    hrelX, RunInv.of_block hruns hrows hinv,
    JoltCodeIntact.of_frame hruns hcontract.1 (fun a ha => (hstores a ha).2) hcode⟩

/-! ## A RISC-V block is one platform step -/

/-- **A RISC-V row is not a registered inline.** At a Sail state related to the entry state of
a RISC-V block of a decoded image, with the code intact, Sail fetches the row's encoding, which
Jolt decodes as a RISC-V instruction, so no fetched word registers as an inline.
Example: at an ADDI block, Sail fetches the ADDI word, whose opcode is `0x13`. -/
theorem notInline_of_riscv (program : Rv64ProgramImage SourceInstruction) (b : Block)
    (hruns : b.Runs program) (himage : ImageDecoded program) {i : RiscvInstruction}
    (hrow : b.row.instruction = .riscv i) (hpc : b.row.address.getLsbD 0 = false)
    (hcode : ∀ t, Related b.pre t → CodeIntact program t) (s : SailState)
    (hrel : Related b.pre s) : NotInlineAt s := by
  rintro inc w ⟨hinc, hfetch⟩
  obtain ⟨e, hd⟩ := himage b.row hruns.row_mem i hrow
  obtain ⟨pc, m, oldInc, hn, hr⟩ := hrel.regs
  obtain ⟨inc', hinc', hf, -⟩ :=
    decoded_inputs program b hruns i e hd hpc (fun _ h => h.misa) hcode s hrel pc m oldInc hn hr
  have hsame : inc = inc' := by
    have h := hinc.symm.trans hinc'
    injection h
  subst hsame
  have hfe : FetchResult.F_Base w = e.fetched := by
    have h := hfetch.symm.trans hf
    injection h
  cases e with
  | base w' =>
    have hww : w = w' := by
      simp only [BlockEncoding.fetched] at hfe
      injection hfe
    subst hww
    obtain ⟨-, -, -, adv, hdec⟩ := hd
    exact register_none_of_joltDecode hdec
  | compressed h =>
    simp only [BlockEncoding.fetched] at hfe
    cases hfe

/-! ## Conforming blocks -/

/-- **What a block needs beyond the run invariants, with inline calls.** This is
`BlockConforms` without its `riscv` field: the row is a RISC-V instruction or a registered
inline call, and an inline call's stores land in RAM outside the code. The other fields are
`BlockConforms`'s and constrain only RISC-V rows.
Example: a `SHA256` block whose state at `rs1` lies in the heap satisfies every field, the
RISC-V fields trivially. -/
structure PlatformConforms (program : Rv64ProgramImage SourceInstruction) (b : Block) :
    Prop where
  /-- Scope: the row is a RISC-V instruction or a registered inline call. Jolt's own
  instructions (`SourceInstruction.jolt`) have no block theorem yet. -/
  supported : (∃ i, b.row.instruction = .riscv i) ∨
    ∃ key rs1 rs2 rd, b.row.instruction = .inline key rs1 rs2 rd
  /-- As in `BlockConforms`. -/
  no_code_store : NoCodeStore program b
  /-- As in `BlockConforms`. -/
  no_flag_word_load : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start →
    i.NoFlagWordLoad b.start
  /-- As in `BlockConforms`. -/
  no_zero_doubleword_load : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start →
    i.NoZeroDoublewordLoad b.start
  /-- As in `BlockConforms`. -/
  panic_store_nonzero : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start →
    i.PanicStoreNonzero b.start
  /-- As in `BlockConforms`. -/
  amo_no_flag_word : ∀ i, b.row.instruction = .riscv i → IoAmoAccess i b.start →
    i.AmoNoFlagWord b.start
  /-- An inline call's stores land in RAM and outside the code: every byte of the footprint of
  the call's write set, with the addresses read in `b.start`, is at or above
  `RAM_START_ADDRESS` and is no byte of an instruction row. The call's precondition
  (`InlineKey.Pre`) implies the first half. -/
  inline_stores : ∀ key rs1 rs2 rd, b.row.instruction = .inline key rs1 rs2 rd →
    ∀ a, (key.writeSet rs1 rs2 rd).Footprint b.start a →
      RAM_START_ADDRESS ≤ a ∧ ¬ IsCodeByte program a

/-- Every block that conforms in the RISC-V-only sense conforms with inline calls.
Example: a conforming ADDI block. -/
theorem BlockConforms.platformConforms {program : Rv64ProgramImage SourceInstruction}
    {b : Block} (h : BlockConforms program b) : PlatformConforms program b where
  supported := .inl h.riscv
  no_code_store := h.no_code_store
  no_flag_word_load := h.no_flag_word_load
  no_zero_doubleword_load := h.no_zero_doubleword_load
  panic_store_nonzero := h.panic_store_nonzero
  amo_no_flag_word := h.amo_no_flag_word
  inline_stores := by
    intro key rs1 rs2 rd call
    obtain ⟨i, hrow⟩ := h.riscv
    rw [hrow] at call
    cases call

/-- **A conforming block is one platform step, and keeps the relation.** A RISC-V block is a
`try_step` (`BlockConforms.simulates`) at a word that is not an inline; an inline block is an
inline platform step (`inline_block_simulates`).
Example: a conforming ADDI block and a `BLAKE2` block with its state in the heap both simulate. -/
theorem PlatformConforms.simulates {program : Rv64ProgramImage SourceInstruction}
    {elf : ElfSections} (hdecoded : program.DecodedFrom elf) (hrows : program.RowsAligned)
    {b : Block} (hruns : b.Runs program)
    (hconf : PlatformConforms program b)
    (hlow : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start → i.NoLowLoad b.start)
    (hbreak : b.row.instruction ≠ .riscv .EBREAK) :
    PlatformSimulates (RunRel program) b := by
  rcases hconf.supported with hriscv | ⟨key, rs1, rs2, rd, call⟩
  · have hbc : BlockConforms program b :=
      ⟨hriscv, hconf.no_code_store, hconf.no_flag_word_load, hconf.no_zero_doubleword_load,
        hconf.panic_store_nonzero, hconf.amo_no_flag_word⟩
    intro s hR
    obtain ⟨v, s', hstep, hR'⟩ := hbc.simulates hdecoded hrows hruns hlow hbreak s hR
    obtain ⟨i, hrow⟩ := hriscv
    exact ⟨s', .sail (notInline_of_riscv program b hruns hdecoded.imageDecoded hrow
      (hruns.pc_even hrows) (fun t ht => CodeIntact.of_related ht hR.2.2) s hR.1) hstep, hR'⟩
  · exact inline_block_simulates hdecoded hrows hruns call
      (hconf.inline_stores key rs1 rs2 rd call)

/-! ## The whole run -/

/-- **Sail plus the platform runs the halt prefix.** This is `HaltPrefix.sailRun` with
`PlatformRun` and `PlatformConforms`.
Example: an ADDI, a `BLAKE2` call and an EBREAK give two platform steps. -/
theorem HaltPrefix.platformRun {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {trace : HonestTrace joltInstance privateInputs}
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    (hconf : ∀ b ∈ pre, PlatformConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState), PlatformRun n (sailInit trace.initialState) s ∧
      RunRel joltInstance.program halt s := by
  have h₀ := RunRel.initial trace hheap
  cases pre with
  | nil => exact ⟨0, _, .done _, by rw [hp.empty rfl]; exact h₀⟩
  | cons first rest =>
    obtain ⟨l, s, hl, hrun, hrel⟩ := platformRun_of_chain (RunRel joltInstance.program)
      (first :: rest) hp.chain
      (fun b hb => PlatformConforms.simulates hdecoded hrows (hp.runs b hb).1
        (hconf b hb) (fun i hi hio => by
          obtain ⟨k, hk⟩ := hp.traced b hb
          apply Block.FirstRowAt.noLowLoad trace hk hcfg hi
          · exact (chain_layout joltInstance.program _ trace.initialState hp.chain
              (fun c hc => (hp.runs c hc).1) hp.first b hb).1
          · exact (hconf b hb).no_zero_doubleword_load i hi hio)
        (hp.runs b hb).2) first rfl (sailInit trace.initialState)
      (by rw [hp.first first rfl]; exact h₀)
    exact ⟨_, s, hrun, hp.last l hl ▸ hrel⟩

/-- **Sail plus the platform reproduces every conforming run of an honest trace, inline calls
included.** This is `HonestTrace.sail_reproduces` for guests that call registered inlines: in
place of `sailRun`, `PlatformRun` runs Sail's `try_step` on RISC-V words and the platform step
on inline words (`PlatformStep`), and in place of `BlockConforms`, the blocks of the halt prefix
satisfy `PlatformConforms`, which admits inline rows whose stores land in RAM outside the code.

For every honest trace and every halt prefix `pre` of it, if every block of `pre` conforms and
Jolt's prover accepts the trace, then `n` platform steps from `sailInit` of the trace's initial
state reach a Sail state `s` with:
* `s` is related to `halt` (`Related`);
* the output bytes of `s`, trailing zeros dropped, are those of the trace's final state;
* the panic word of `s` is nonzero exactly when the final state's panic flag is set;
* `s` has halted (`SailHalted`), or `halt` is the trace's final state.

At each inline call of the run, the platform step keeps the frame of the call's write set, and
meets the call's specification when the call's precondition holds and its inputs lie in RAM.

Premises, by class:
* prover acceptance: `hcfg`;
* platform: `hdecoded` (`DecodedFrom`, which now also fixes every inline row as the registered
  inline of its word), `hrows` (`RowsAligned`), `hheap` (`HeapNoWrap`);
* documented deviation: the deviation fields of `PlatformConforms` on the RISC-V blocks of `pre`;
* inline stores: the `inline_stores` field of `PlatformConforms` on the inline blocks of `pre`;
* scope: the `supported` field of `PlatformConforms` (no `SourceInstruction.jolt` row).

Example: a trace that calls `SHA256` on a state in the heap and then runs `ebreak` has `pre`
with one block, and `s` holds the compression at the state's address. -/
theorem HonestTrace.sail_reproduces_with_inlines {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, PlatformConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      PlatformRun n (sailInit trace.initialState) s ∧
      Related halt s ∧
      trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
        trimTrailingZeros final.jolt_device.outputs ∧
      (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ final.jolt_device.panic = true) ∧
      (SailHalted joltInstance.program s ∨ halt = final) := by
  obtain ⟨n, s, hrun, hrel⟩ := hp.platformRun hdecoded hrows hheap hcfg hconf
  have hlayout : halt.jolt_device.memory_layout = trace.initialState.jolt_device.memory_layout := by
    cases pre with
    | nil => rw [hp.empty rfl]
    | cons f rest =>
      obtain ⟨l, hl⟩ : ∃ l, (f :: rest).getLast? = some l :=
        ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
      rw [← hp.last l hl]
      exact (chain_layout joltInstance.program _ trace.initialState hp.chain
        (fun b hb => (hp.runs b hb).1) hp.first l (List.mem_of_mem_getLast? hl)).2
  refine ⟨n, s, hrun, hrel.1, ?_, ?_, ?_⟩
  · rw [← sailOutputs_congr hlayout, hrel.1.outputs, hp.device]
  · rw [← sailPanicWord_congr hlayout, ← hp.device]
    exact (hrel.1.panic).symm
  · rcases hp.stop with hn | hn
    · exact Or.inl (SailHalted.of_related hrel.1 hn)
    · exact Or.inr hn

end WholeRun

open WholeRun

/-- **Sail plus the platform reproduces every run that Jolt's soundness theorem accepts, inline
calls included (R5).** This is `JoltInstance.sail_soundness` for guests that call registered
inlines. Every instance that the constraints accept has an honest trace with the three
properties of `JoltInstance.InLanguage`. The trace has a halt prefix `pre`, the blocks before the
first EBREAK. If every block of `pre` satisfies `PlatformConforms`, then `n` platform steps
(`PlatformRun`: Sail's `try_step` on RISC-V words, the platform step on inline words), started
from `sailInit` of the trace's initial state, reach a Sail state `s` with these properties:
* `s` is related to the halt state (`Related`);
* its output bytes, trailing zeros dropped, are the instance's claimed outputs;
* its panic word is nonzero exactly when the instance claims a panic;
* it has halted (`SailHalted`), or `halt` is the trace's final state.

At each inline call, the platform step keeps the frame of the call's write set, and meets the
call's specification when the call's precondition holds and its inputs lie in RAM.

"Accepted" means that the witness satisfies `AllConstraints`, which checks every constraint
equation directly. The premises are those of `JoltInstance.sail_soundness`; `PlatformConforms`
replaces `BlockConforms` and is weaker on every RISC-V block (`BlockConforms.platformConforms`).
The theorem goes one way, stops in front of the first EBREAK, and compares outputs after
dropping trailing zero bytes. It does not say that a guest computes SHA-256 or verifies an
ECDSA signature.

Example: a guest that hashes a block in the heap with `SHA256`, writes the state to the output
region and ends with `ebreak` gives a platform run whose final memory holds the compression. -/
theorem JoltInstance.sail_soundness_with_inlines {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    (adviceBlockFits : joltInstance.UntrustedAdviceBlockFits)
    {params : WitnessParams} (untrustedAdvice : Nat → F)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance untrustedAdvice witness)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) :
    ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
      trace.matches_outputs joltInstance ∧
      (trace.prover_config joltInstance).isSome ∧
      trace.SpoilAssertsPass ∧
      ∃ (pre : List Block) (halt final : SailJoltState),
        HaltPrefix trace pre halt final ∧
        ((∀ b ∈ pre, PlatformConforms joltInstance.program b) →
          ∃ (n : Nat) (s : SailState),
            PlatformRun n (sailInit trace.initialState) s ∧
            Related halt s ∧
            trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
              trimTrailingZeros joltInstance.outputs ∧
            (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ joltInstance.panic = true) ∧
            (SailHalted joltInstance.program s ∨ halt = final)) := by
  obtain ⟨privateInputs, trace, hmo, hcfg, hspoil⟩ :=
    JoltInstance.soundness joltField joltInstance assumptions restrictions adviceBlockFits
      untrustedAdvice witness satisfied
  obtain ⟨pre, halt, final, hp⟩ := trace.haltPrefix
  refine ⟨privateInputs, trace, hmo, hcfg, hspoil, pre, halt, final, hp, fun hconf => ?_⟩
  obtain ⟨n, s, hrun, hrel, houts, hpanic, hstop⟩ :=
    trace.sail_reproduces_with_inlines hdecoded hrows hheap hcfg hp hconf
  obtain ⟨hmo_out, hmo_panic⟩ :=
    (trace.matches_outputs_halt final final hp.back rfl).1 hmo
  refine ⟨n, s, hrun, hrel, houts.trans hmo_out, ?_, hstop⟩
  rw [hpanic, hmo_panic]
