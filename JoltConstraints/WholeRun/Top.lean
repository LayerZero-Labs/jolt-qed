import JoltConstraints.Soundness.soundness
import JoltConstraints.WholeRun.Halt
import JoltConstraints.WholeRun.CodeInv
import JoltConstraints.WholeRun.Decoded
import JoltConstraints.WholeRun.Init
import JoltConstraints.WholeRun.RunInv

/-!
# The top theorem: Sail reproduces every run Jolt's soundness theorem accepts

`JoltInstance.soundness` says an instance accepted by the constraints is in Jolt's language: some
private inputs give an honest trace with the claimed outputs. `JoltInstance.sail_soundness`
strengthens it: for that same trace, Sail's emulator loop started from `sailInit` of the trace's
initial state runs to the trace's halt and reports the same outputs and panic flag.

The proof chains the per-block theorem `block_simulates_image` along the halt prefix of the trace
(`HonestTrace.halt_prefix`). The relation it carries (`RunRel`) is `Related` together with the run
invariants `RunInv` and `JoltCodeIntact`, which hold initially and are kept by every block that
runs. What a block needs beyond the invariants is collected in `BlockConforms`; the top theorem
asks for it of the blocks of the trace's own prefix, so the deviations are checked on the run
that actually happens.

`docs/riscv-alignment.md` section 2 asks whether the prover's acceptance of the trace implies
`NoLowLoad`. It does not follow directly: `ProverConfig` is derived from the trace's recorded
`ram_address` values (`HonestTrace.prover_config_addresses_ok`), and `HonestTrace.blocks` does not
tie the blocks to those rows, so `NoLowLoad` stays a field of `BlockConforms`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-! ## The relation of the run -/

/-- **The relation the whole-run chain carries.** Sail's state is related to Jolt's, Jolt's state
satisfies the run invariants (legal system values, the heap bound) and Jolt's memory still holds the
program's code.
For example, `sailInit` of an honest trace's initial state is related to it in this sense
(`RunRel.initial`). -/
def RunRel (program : Rv64ProgramImage SourceInstruction) (jt : SailJoltState)
    (s : SailState) : Prop :=
  Related jt s ∧ RunInv program jt ∧ JoltCodeIntact program jt

/-- **The run starts in the relation.** Sail's `sailInit` of an honest trace's initial state is
related to it, given the platform premise on the heap. -/
theorem RunRel.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (hheap : joltInstance.HeapNoWrap) :
    RunRel joltInstance.program trace.initialState (sailInit trace.initialState) :=
  ⟨related_sailInit joltInstance privateInputs _ trace.initialized,
    RunInv.initial trace hheap, JoltCodeIntact.initial trace⟩

/-! ## The per-block conditions -/

/-- **What a block needs beyond the run invariants.** Every field is a scope restriction or a
documented deviation (`docs/riscv-alignment.md`, sections 2, 5 and 7), checked on the block's own
instruction and entry state.
For example, a block running `ADDI` satisfies every field but `riscv` trivially, and a block running
`SB` into the output region satisfies `no_code_store`, and the I/O fields when its store keeps the
panic word nonzero. -/
structure BlockConforms (program : Rv64ProgramImage SourceInstruction) (b : Block) : Prop where
  /-- Scope: the row is a RISC-V instruction. Jolt's own instructions (`SourceInstruction.jolt`,
  `docs/riscv-alignment.md` section 7) have no block theorem yet. -/
  riscv : ∃ i, b.row.instruction = .riscv i
  /-- Deviation: the block stores into no byte of the program's code (`NoCodeStore`). -/
  no_code_store : NoCodeStore program b
  /-- Deviation, for an I/O access: no load reads the panic or termination word
  (`NoFlagWordLoad`). -/
  no_flag_word_load : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start →
    i.NoFlagWordLoad b.start
  /-- Deviation, for an I/O access: no load reads below the lowest address Jolt's prover accepts
  (`NoLowLoad`). -/
  no_low_load : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start → i.NoLowLoad b.start
  /-- Deviation, for an I/O access: a store touching the panic doubleword leaves Sail's panic word
  nonzero (`PanicStoreNonzero`). -/
  panic_store_nonzero : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start →
    i.PanicStoreNonzero b.start
  /-- Deviation, for an atomic on the I/O window: no byte of its doubleword is the panic or
  termination word (`AmoNoFlagWord`). -/
  amo_no_flag_word : ∀ i, b.row.instruction = .riscv i → IoAmoAccess i b.start →
    i.AmoNoFlagWord b.start

/-- **Documented deviation: no row of the image holds the reserved parcel `0x6001`.** This is
`NotReservedParcel` stated once on the image instead of on each block. For example, an image
compiled from ordinary RISC-V code never contains it. -/
def ImageNoReservedParcel (program : Rv64ProgramImage SourceInstruction) : Prop :=
  ∀ row ∈ program.instructions, imageParcel? program row.address.toNat ≠ some 0x6001#16

theorem ImageNoReservedParcel.block {program : Rv64ProgramImage SourceInstruction}
    (h : ImageNoReservedParcel program) {b : Block} (hruns : b.Runs program) :
    NotReservedParcel program b :=
  h b.row hruns.row_mem

/-- **A conforming block simulates, and keeps the relation.** Every block that runs, is not
EBREAK and conforms is matched by one Sail step that lands in the relation for the block's last
state. -/
theorem BlockConforms.simulates {program : Rv64ProgramImage SourceInstruction}
    (himage : ImageDecoded program) (hrows : program.RowsAligned)
    (hreserved : ImageNoReservedParcel program) {b : Block} (hruns : b.Runs program)
    (hconf : BlockConforms program b) (hbreak : b.row.instruction ≠ .riscv .EBREAK) :
    BlockSimulates (RunRel program) b := by
  obtain ⟨i, hrow⟩ := hconf.riscv
  have hi : i ≠ .EBREAK := fun h => hbreak (by rw [hrow, h])
  rintro s ⟨hrel, hinv, hcode⟩
  obtain ⟨v, s', hstep, hrel'⟩ := block_simulates_image program b hruns himage i hrow hi
    hinv.system (hruns.pc_even hrows) (fun _ hr => CodeIntact.of_related hr hcode)
    hinv.heap_no_wrap (hreserved.block hruns)
    (hconf.no_flag_word_load i hrow) (hconf.no_low_load i hrow) (hconf.panic_store_nonzero i hrow)
    (hconf.amo_no_flag_word i hrow) s hrel
  exact ⟨v, s', hstep, hrel', RunInv.of_block hruns hrows hinv,
    JoltCodeIntact.of_block hruns hconf.no_code_store hcode⟩

/-! ## Where the run stops -/

/-- **Sail has halted.** Its `PC` is the address of an image row whose instruction is EBREAK, so the
next `try_step` would run the halting instruction (`docs/riscv-alignment.md`, section 4). -/
def SailHalted (program : Rv64ProgramImage SourceInstruction) (s : SailState) : Prop :=
  ∃ row : SourceInstructionRow SourceInstruction,
    s.regs.get? Register.PC = some row.address ∧
    rowAt program row.address = some row ∧
    row.instruction = .riscv .EBREAK

/-- Sail's `PC` in a related state is Jolt's `nextPC`. -/
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

/-- A state related to one that is about to run an EBREAK has halted. -/
theorem SailHalted.of_related {program : Rv64ProgramImage SourceInstruction} {jt : SailJoltState}
    {s : SailState} (h : Related jt s) (hn : NextIsEbreak program jt) : SailHalted program s := by
  obtain ⟨row, hnext, hat, hebreak⟩ := hn
  exact ⟨row, h.pc_eq_nextPC hnext, hat, hebreak⟩

/-- **The halt prefix of an honest trace.** `pre` is the chain of blocks before the first EBREAK
block, starting at the trace's initial state and ending at `halt` (the initial state if `pre` is
empty). Either the next instruction at `halt` is an EBREAK, or the trace ended without one and
`halt` is its final state `final`; `halt` and `final` have the same device. This is the content of
`HonestTrace.halt_prefix` as one predicate. -/
structure HaltPrefix {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (pre : List Block) (halt final : SailJoltState) : Prop where
  /-- `final` is the state after the trace's last row. -/
  back : trace.rows.back?.map (·.postState) = some final
  /-- Each block of the prefix runs (`Block.Runs`) and does not run EBREAK. Since a block's last
  state is a function of its first, the chain from the initial state is the trace's own. -/
  runs : ∀ b ∈ pre, b.Runs joltInstance.program ∧ b.row.instruction ≠ .riscv .EBREAK
  /-- Each block starts where the previous one ended. -/
  chain : pre.IsChain (fun b c => b.post = c.pre)
  /-- The first block starts at the trace's initial state. -/
  first : ∀ first ∈ pre.head?, first.pre = trace.initialState
  /-- The last block ends at `halt`. -/
  last : ∀ last ∈ pre.getLast?, last.post = halt
  /-- An empty prefix halts at the initial state. -/
  empty : pre = [] → halt = trace.initialState
  /-- The run stops at an EBREAK, or the trace ends at `halt`. -/
  stop : NextIsEbreak joltInstance.program halt ∨ halt = final
  /-- `halt` and the final state have the same device. -/
  device : halt.jolt_device = final.jolt_device

theorem HonestTrace.haltPrefix {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    ∃ pre halt final, HaltPrefix trace pre halt final := by
  obtain ⟨pre, halt, final, h1, h2, h3, h4, h5, h6, h7, h8⟩ := HonestTrace.halt_prefix trace
  exact ⟨pre, halt, final, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- The memory layout is the same at the start and the end of a chain of blocks that run. -/
private theorem chain_layout (program : Rv64ProgramImage SourceInstruction) :
    ∀ (bs : List Block), bs.IsChain (fun b c => b.post = c.pre) →
      (∀ b ∈ bs, b.Runs program) →
      ∀ f ∈ bs.head?, ∀ l ∈ bs.getLast?,
        l.post.jolt_device.memory_layout = f.pre.jolt_device.memory_layout
  | [], _, _, f, hf, _, _ => by simp at hf
  | [b], _, hruns, f, hf, l, hl => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hl
      subst hf; subst hl
      exact (hruns _ (by simp)).layout_eq
  | b :: c :: rest, hchain, hruns, f, hf, l, hl => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
      subst hf
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hlink, hchain'⟩ := hchain
      have ih := chain_layout program (c :: rest) hchain'
        (fun d hd => hruns d (List.mem_cons_of_mem _ hd)) c rfl l
        (by simpa only [List.getLast?_cons_cons] using hl)
      rw [ih, ← hlink]
      exact (hruns _ (by simp)).layout_eq

/-- `sailOutputs` and `sailPanicWord` read the device only through its memory layout. -/
theorem sailOutputs_congr {d d' : JoltDevice} (h : d.memory_layout = d'.memory_layout)
    (s : SailState) : sailOutputs d s = sailOutputs d' s := by
  simp only [sailOutputs, h]

theorem sailPanicWord_congr {d d' : JoltDevice} (h : d.memory_layout = d'.memory_layout)
    (s : SailState) : sailPanicWord d s = sailPanicWord d' s := by
  simp only [sailPanicWord, h]

/-- **Sail runs the halt prefix.** If every block of the prefix conforms, `sailRun` from `sailInit`
of the initial state reaches a Sail state in the relation for `halt`. -/
theorem HaltPrefix.sailRun {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {trace : HonestTrace joltInstance privateInputs}
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (himage : ImageDecoded joltInstance.program) (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) (hreserved : ImageNoReservedParcel joltInstance.program)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState), sailRun n (sailInit trace.initialState) = .ok () s ∧
      RunRel joltInstance.program halt s := by
  have h₀ := RunRel.initial trace hheap
  cases pre with
  | nil => exact ⟨0, _, rfl, by rw [hp.empty rfl]; exact h₀⟩
  | cons first rest =>
    obtain ⟨l, s, hl, hrun, hrel⟩ := sailRun_of_chain (RunRel joltInstance.program)
      (first :: rest) hp.chain
      (fun b hb => BlockConforms.simulates himage hrows hreserved (hp.runs b hb).1
        (hconf b hb) (hp.runs b hb).2) first rfl (sailInit trace.initialState)
      (by rw [hp.first first rfl]; exact h₀)
    exact ⟨_, s, hrun, hp.last l hl ▸ hrel⟩

/-- **Sail reproduces every conforming run of an honest trace.** For every honest trace and every
halt prefix `pre` of it (the blocks before the first EBREAK, ending at `halt`), if every block of
`pre` conforms (`BlockConforms`), then `sailRun` from `sailInit` of the trace's initial state takes `n`
successful steps to a Sail state `s` that satisfies four things:
* `s` is related to `halt` (`Related`): Sail's registers, PC, CSRs and memory are Jolt's;
* the output bytes of `s`, trailing zeros dropped, are those of the trace's final state;
* the panic word of `s` is nonzero exactly when the final state's panic flag is set;
* `s` has halted (`SailHalted`), or `halt` is the trace's final state.

Premises, by class:
* platform: `himage` (`ImageDecoded`), `hrows` (`RowsAligned`), `hheap` (`HeapNoWrap`);
* documented deviation: `hreserved` (`ImageNoReservedParcel`), and the deviation fields of
  `BlockConforms` on the blocks of `pre`;
* scope: the `riscv` field of `BlockConforms`.

For example, a trace that runs `addi a0, a0, 1` and then `ebreak` has `pre` with one block, `halt`
the state before the `ebreak`, and `s` with `a0` one larger than at the start and `PC` at the
`ebreak`. -/
theorem HonestTrace.sail_reproduces {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (himage : ImageDecoded joltInstance.program) (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) (hreserved : ImageNoReservedParcel joltInstance.program)
    {pre : List Block} {halt final : SailJoltState} (hp : HaltPrefix trace pre halt final)
    (hconf : ∀ b ∈ pre, BlockConforms joltInstance.program b) :
    ∃ (n : Nat) (s : SailState),
      WholeRun.sailRun n (sailInit trace.initialState) = .ok () s ∧
      Related halt s ∧
      trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
        trimTrailingZeros final.jolt_device.outputs ∧
      (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ final.jolt_device.panic = true) ∧
      (SailHalted joltInstance.program s ∨ halt = final) := by
  obtain ⟨n, s, hrun, hrel⟩ := hp.sailRun himage hrows hheap hreserved hconf
  have hlayout : halt.jolt_device.memory_layout = trace.initialState.jolt_device.memory_layout := by
    cases pre with
    | nil => rw [hp.empty rfl]
    | cons f rest =>
      obtain ⟨l, hl⟩ : ∃ l, (f :: rest).getLast? = some l :=
        ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
      rw [← hp.last l hl, chain_layout joltInstance.program _ hp.chain
        (fun b hb => (hp.runs b hb).1) f rfl l hl, hp.first f rfl]
  refine ⟨n, s, hrun, hrel.1, ?_, ?_, ?_⟩
  · rw [← sailOutputs_congr hlayout, hrel.1.outputs, hp.device]
  · rw [← sailPanicWord_congr hlayout, ← hp.device]
    exact (hrel.1.panic).symm
  · rcases hp.stop with hn | hn
    · exact Or.inl (SailHalted.of_related hrel.1 hn)
    · exact Or.inr hn

end WholeRun

open WholeRun

/-- **Sail reproduces every run that Jolt's soundness theorem accepts.**
Every instance that the constraints accept has an honest trace with the three properties of
`JoltInstance.InLanguage`, and Sail's emulator reproduces that trace's run up to the halt.
The halt is the trace's prefix `pre` before the first EBREAK (`HaltPrefix`).
If every block of `pre` conforms (`BlockConforms`), then `sailRun`, started from `sailInit` of the
trace's initial state, takes `n` successful steps to a Sail state `s` with these properties:
* `s` is related to the halt state (`Related`);
* its output bytes, trailing zeros dropped, are the instance's claimed outputs;
* its panic word is nonzero exactly when the instance claims a panic;
* it has halted (`SailHalted`), or `halt` is the trace's final state.

The trace is the one `JoltInstance.soundness` extracts from the witness.
Conformance has to be checked on that trace, or argued from Jolt's determinism when the trace is
unique for the given inputs.
For a trace given in advance, `HonestTrace.sail_reproduces` states the same for every honest trace
and every halt prefix of it.

Premises, by class:
* soundness's own premises: `joltField`, `assumptions` (`SoundnessAssumptions`), `restrictions`
  (`TemporaryRestrictions`), and a witness that satisfies `AllConstraints`.
* platform: `himage` (`ImageDecoded`: the committed bytecode is what Jolt's decoder makes of the
  image), `hrows` (`RowsAligned`: every row's address is even), `hheap` (`HeapNoWrap`: the heap ends
  eight bytes below `2^64`).
* documented deviation: `hreserved` (`ImageNoReservedParcel`). It covers the reserved parcel
  `0x6001`, which Jolt runs as a no-op and Sail rejects; it is discharged once a16z/jolt#2381 is in
  the pin. On the blocks of the prefix there are five more:
  * `NoCodeStore`: no store into the code;
  * `NoFlagWordLoad`: no read of the panic or termination word;
  * `NoLowLoad`: no load below the lowest address Jolt's prover accepts;
  * `PanicStoreNonzero`: a store into the panic word leaves it nonzero;
  * `AmoNoFlagWord`: no atomic on the I/O window touches the panic or termination word.
* scope: every block of the prefix runs a RISC-V row; Jolt's own instructions
  (`SourceInstruction.jolt`) have no block theorem yet.

For example, take a guest that sums its input, stores the sum in the output region and ends with
`ebreak`. Its `ebreak` row is at `halt`, so Sail's `PC` names that row. -/
theorem JoltInstance.sail_soundness {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (givenInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance givenInputs witness)
    (himage : ImageDecoded joltInstance.program) (hrows : joltInstance.program.RowsAligned)
    (hheap : joltInstance.HeapNoWrap) (hreserved : ImageNoReservedParcel joltInstance.program) :
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
            trimTrailingZeros (sailOutputs trace.initialState.jolt_device s) =
              trimTrailingZeros joltInstance.outputs ∧
            (sailPanicWord trace.initialState.jolt_device s ≠ 0 ↔ joltInstance.panic = true) ∧
            (SailHalted joltInstance.program s ∨ halt = final)) := by
  obtain ⟨privateInputs, trace, hmo, hcfg, hspoil⟩ :=
    JoltInstance.soundness joltField joltInstance assumptions restrictions givenInputs witness
      satisfied
  obtain ⟨pre, halt, final, hp⟩ := trace.haltPrefix
  refine ⟨privateInputs, trace, hmo, hcfg, hspoil, pre, halt, final, hp, fun hconf => ?_⟩
  obtain ⟨n, s, hrun, hrel, houts, hpanic, hstop⟩ :=
    trace.sail_reproduces himage hrows hheap hreserved hp hconf
  obtain ⟨hmo_out, hmo_panic⟩ :=
    (trace.matches_outputs_halt final final hp.back rfl).1 hmo
  refine ⟨n, s, hrun, hrel, houts.trans hmo_out, ?_, hstop⟩
  rw [hpanic, hmo_panic]
