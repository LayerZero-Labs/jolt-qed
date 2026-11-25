import JoltConstraints.theorems.Soundness.soundness
import JoltConstraints.theorems.WholeRun.Halt
import JoltConstraints.theorems.WholeRun.CodeInv
import JoltConstraints.theorems.WholeRun.Elf
import JoltConstraints.theorems.Completeness
import JoltConstraints.theorems.Completeness.All
import JoltConstraints.theorems.Completeness.Helpers.LookupPextProofHelpers
import JoltConstraints.theorems.Completeness.Helpers.LookupShiftProofHelpers

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- Registers, shared memory, system state and code agree along a whole run.
For example, its initial instance uses Jolt's initialized byte map directly. -/
def RunRel (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState)
    (s : SailState) : Prop :=
  Related jt s ∧ RunInv program jt ∧ JoltCodeIntact program jt

/-- An honest trace starts in the whole-run relation.
For example, its Sail initial state uses the platform register overlay. -/
theorem RunRel.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (hheap : joltInstance.HeapNoWrap) :
    RunRel joltInstance.program trace.initialState (sailInit trace.initialState) :=
  ⟨related_sailInit joltInstance privateInputs _ trace.initialized,
    RunInv.initial trace hheap, JoltCodeIntact.initial trace⟩

/-- Per-block conditions supplied to the source-instruction simulation.
For example, an ADDI block needs only the RISC-V source classification.
Successful mapped-memory guards are derived from each block run. -/
structure BlockConforms (program : Rv64ProgramImage SourceInstruction) (b : Block) : Prop where
  riscv : ∃ i, b.row.instruction = .riscv i
  no_code_store : NoCodeStore program b
/-- A conforming non-EBREAK source block has one matching Sail step.
For example, an arithmetic block transports the register and shared-memory relation. -/
theorem BlockConforms.simulates {program : Rv64ProgramImage SourceInstruction}
    {elf : ElfSections} (hdecoded : program.DecodedFrom elf) (hrows : program.RowsAligned)
    {b : Block} (hruns : b.Runs program)
    (hconf : BlockConforms program b)
    (hbreak : b.row.instruction ≠ .riscv .EBREAK) :
    BlockSimulates (RunRel program) b := by
  obtain ⟨i, hrow⟩ := hconf.riscv
  have hi : i ≠ .EBREAK := fun h => hbreak (by rw [hrow, h])
  rintro s ⟨hrel, hinv, hcode⟩
  obtain ⟨v, s', hstep, hrel'⟩ := block_simulates_image program b hruns hdecoded.imageDecoded i
    hrow hi hinv.system (hruns.pc_even hrows) (fun _ hr => CodeIntact.of_related hr hcode)
    hinv.heap_no_wrap s hrel
  exact ⟨v, s', hstep, hrel', RunInv.of_block hruns hrows hinv,
    JoltCodeIntact.of_block hruns hconf.no_code_store hcode⟩

/-- Sail is about to execute the source halt of `kind`.
For example, EBREAK identifies a panic halt, while `jolt.success` identifies success. -/
def SailHalted (program : Rv64ProgramImage SourceInstruction) (s : SailState)
    (kind : JoltHaltKind) : Prop :=
  ∃ row : SourceInstructionRow SourceInstruction,
    s.regs.get? Register.PC = some row.address ∧
    rowAt program row.address = some row ∧
    row.instruction = haltSource kind

/-- Sail's PC is the next source address in the related Jolt state.
For example, both name the address of the next halt source. -/
theorem Related.pc_eq_nextPC {jt : SailJoltState} {s : SailState} (h : Related jt s)
    {pc : BitVec 64} (hnext : jt.sail.regs.get? Register.nextPC = some pc) :
    s.regs.get? Register.PC = some pc := by
  obtain ⟨pc', m, inc, hn, hregs⟩ := h.regs
  have : pc' = pc := Option.some.inj (hn.symm.trans hnext)
  subst this
  rw [hregs]
  unfold sailRegs
  rw [Step.setReg_get?_ne _ _ (by decide), Step.setReg_get?_ne _ _ (by decide),
    Step.setReg_get?_ne _ _ (by decide), Step.setReg_get?_ne _ _ (by decide)]
  exact Std.ExtDHashMap.get?_insert_self

/-- The register relation carries the next explicit halt to Sail's PC.
For example, a next EBREAK row gives a Sail panic-halt source. -/
theorem SailHalted.of_related {program : Rv64ProgramImage SourceInstruction} {jt : SailJoltState}
    {s : SailState} (h : Related jt s) (kind : JoltHaltKind) (hn : NextIsHalt program jt kind) : SailHalted program s kind := by
  obtain ⟨row, hnext, hat, hebreak⟩ := hn
  exact ⟨row, h.pc_eq_nextPC hnext, hat, hebreak⟩

/-- The trace's non-halting source blocks form a linked prefix ending at `halt`.
Its observation retains final memory, layout and the explicit halt claim.
For example, a trace beginning with `jolt.success` has an empty prefix. -/
structure HaltPrefix {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (pre : List Block) (halt final : SailJoltState) : Prop where
  back : trace.rows.back?.map (·.postState) = some final
  runs : ∀ b ∈ pre, b.Runs joltInstance.program ∧ ¬ ∃ kind, b.row.instruction = haltSource kind
  traced : ∀ b ∈ pre, ∃ k, b.FirstRowAt trace.toTrace k
  chain : pre.IsChain (fun b c => b.post = c.pre)
  first : ∀ first ∈ pre.head?, first.pre = trace.initialState
  last : ∀ last ∈ pre.getLast?, last.post = halt
  empty : pre = [] → halt = trace.initialState
  observation : HaltObservation joltInstance.program halt final

/-- Every honest trace supplies a halt-prefix certificate.
For example, an initial EBREAK gives an empty prefix and a panic observation. -/
theorem HonestTrace.haltPrefix {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ pre halt final, HaltPrefix trace pre halt final := by
  obtain ⟨pre, halt, final, h1, h2, h3, h4, h5, h6, h7, ht⟩ := HonestTrace.halt_prefix trace
  exact ⟨pre, halt, final, ⟨h1, h2, ht, h3, h4, h5, h6, h7⟩⟩

private theorem chain_layout (program : Rv64ProgramImage SourceInstruction) :
    ∀ (bs : List Block) (p : SailJoltState), bs.IsChain (fun b c => b.post = c.pre) →
      (∀ b ∈ bs, b.Runs program) → (∀ f ∈ bs.head?, f.pre = p) →
      ∀ b ∈ bs, b.pre.jolt_device.memory_layout = p.jolt_device.memory_layout ∧
        b.post.jolt_device.memory_layout = p.jolt_device.memory_layout
  | [], _, _, _, _, b, hb => by simp at hb
  | f :: rest, p, hchain, hruns, hfirst, b, hb => by
      have hf : f.pre = p := hfirst f rfl
      have hpost := (hruns f (by simp)).layout_eq.trans (congrArg
        (fun s : SailJoltState => s.jolt_device.memory_layout) hf)
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨congrArg (fun s : SailJoltState => s.jolt_device.memory_layout) hf, hpost⟩
      · obtain ⟨hlink, htail⟩ := List.isChain_cons.mp hchain
        have ih := chain_layout program rest f.post htail
          (fun c hc => hruns c (List.mem_cons_of_mem _ hc))
          (fun c hc => (hlink c hc).symm) b hb
        exact ⟨ih.1.trans hpost, ih.2.trans hpost⟩

/-- Simulate every conforming block in a halt prefix and chain its Sail steps.
For example, an ADDI before a halt contributes one successful Sail step. -/
theorem HaltPrefix.sailRun {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {trace : HonestTrace joltInstance privateInputs}
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState), sailRun n (sailInit trace.initialState) = .ok () s ∧
      RunRel joltInstance.program halt s := by
  have h₀ := RunRel.initial trace hheap
  cases pre with
  | nil => exact ⟨0, _, rfl, by rw [hp.empty rfl]; exact h₀⟩
  | cons first rest =>
    obtain ⟨l, s, hl, hrun, hrel⟩ := sailRun_of_chain (RunRel joltInstance.program)
      (first :: rest) hp.chain
      (fun b hb => BlockConforms.simulates hdecoded hrows (hp.runs b hb).1
        (hconf b hb)
        (fun ebreak => (hp.runs b hb).2 ⟨.panic, ebreak⟩)) first rfl (sailInit trace.initialState)
      (by rw [hp.first first rfl]; exact h₀)
    exact ⟨_, s, hrun, hp.last l hl ▸ hrel⟩

/-- Sail reproduces the non-halting blocks of an honest trace and extracts the
same final output bytes from shared memory.
The stopping alternative records the explicit halt kind and its panic claim;
for example, EBREAK records panic true without reading a flag word. -/
theorem HonestTrace.sail_reproduces {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap)
    (hcfg : (trace.prover_config joltInstance).isSome)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      WholeRun.sailRun n (sailInit trace.initialState) = .ok () s ∧
      Related halt s ∧
      trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
        trimTrailingZeros (final.jolt_device.outputsOf final.sail.mem) ∧
      ∃ kind, final.halted = some kind ∧
        final.jolt_device.panic = (kind == JoltHaltKind.panic) ∧
        (SailHalted joltInstance.program s kind ∨ halt = final) := by
  obtain ⟨n, s, hrun, hrel⟩ := hp.sailRun hdecoded hrows hheap hcfg hconf
  refine ⟨n, s, hrun, hrel.1, ?_, ?_⟩
  · rw [hrel.1.outputs]
    simp only [JoltDevice.outputsOf, hp.observation.1, hp.observation.2.1]
  · rcases hp.observation.2.2 with ⟨kind, next, recorded, claim⟩ | same
    · exact ⟨kind, recorded, claim, Or.inl (SailHalted.of_related hrel.1 kind next)⟩
    · obtain ⟨kind, recorded, claim⟩ := trace.final_halt final hp.back
      exact ⟨kind, recorded, claim, Or.inr same⟩

end WholeRun

open WholeRun

/-- Every accepted constraint witness has an honest trace and a Sail run through
its conforming non-halting prefix, with the claimed shared output bytes.
At an explicit halt, its kind determines the public panic claim.
For example, a panic-ending trace is covered with public panic true.
Jolt at `ff6fc6568`: `rv64_trace_constraints` halt lane and `Cpu::halt`. -/
theorem JoltInstance.sail_soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (givenInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance givenInputs witness)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) :
    ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
      trace.matches_outputs joltInstance ∧
      (trace.prover_config joltInstance).isSome ∧
      trace.SpoilAssertsPass ∧
      ∃ (pre : List Block) (halt final : SailJoltState),
        HaltPrefix trace pre halt final ∧
        ((∀ b ∈ pre, BlockConforms joltInstance.program b) →
          ∃ (n : Nat) (s : SailState),
            sailRun n (sailInit trace.initialState) = .ok () s ∧
            Related halt s ∧
            trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
              trimTrailingZeros joltInstance.outputs ∧
            ∃ kind, final.halted = some kind ∧
              joltInstance.panic = (kind == JoltHaltKind.panic) ∧
              (SailHalted joltInstance.program s kind ∨ halt = final)) := by
  obtain ⟨privateInputs, trace, hmo, hcfg, hspoil⟩ :=
    JoltInstance.soundness joltField joltInstance assumptions restrictions givenInputs witness
      satisfied
  obtain ⟨pre, halt, final, hp⟩ := trace.haltPrefix
  refine ⟨privateInputs, trace, hmo, hcfg, hspoil, pre, halt, final, hp, fun hconf => ?_⟩
  obtain ⟨n, s, hrun, hrel, houts, hstop⟩ :=
    trace.sail_reproduces hdecoded hrows hheap hcfg hp hconf
  obtain ⟨hmo_out, hmo_panic⟩ :=
    (trace.matches_outputs_final final hp.back).1 hmo
  refine ⟨n, s, hrun, hrel, houts.trans hmo_out, ?_⟩
  obtain ⟨kind, recorded, claim, stop⟩ := hstop
  exact ⟨kind, recorded, hmo_panic.symm.trans claim, stop⟩
