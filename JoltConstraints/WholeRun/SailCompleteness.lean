import JoltConstraints.WholeRun.Platform
import JoltConstraints.WholeRun.TraceOfBlocks
import JoltConstraints.Completeness.completeness

/-!
# Completeness from Sail: every Sail run that Jolt follows is accepted

`JoltInstance.sail_soundness_with_inlines` goes from Jolt to Sail: a run that Jolt's constraints
accept is a run of Sail plus the platform. This file goes the other way.
`JoltInstance.sail_completeness` takes a run of Sail plus the platform (`PlatformStep`) from
`sailInit` of the instance's initial state, which stops at Jolt's termination convention (a
stable self-jump, `SailStalls`). If Jolt follows each step of the run (`JoltFollows`), the run's
rows fit Jolt's maximum trace length and the guest stays inside Jolt's memory map, then Jolt's
tracer has an honest trace with the run's outputs and panic flag, and the witness Jolt's prover
builds from it satisfies `AllConstraints`.

The proof has three parts.
* The backward step (`JoltStep.lands`): a block that Jolt runs from a state related to Sail's
  ends in a state related to Sail's next state. For a RISC-V block this follows from
  `PlatformConforms.simulates` and the determinism of `try_step`. For an inline call, the
  platform may store any result that meets the call's specification, so `JoltStep.inline_lands`
  asks for it.
* The chain (`blocks_of_run`): the blocks of the steps form a chain from the initial state, and
  `HonestTrace.ofBlocks` turns them into an honest trace.
* The composition: the trace has the run's outputs, its rows pass their assertions
  (`expand_instruction_no_spoil`), Jolt's prover accepts it (`prover_config_some`), and
  `JoltInstance.completeness` gives `AllConstraints`.

`docs/whole-run-theorem.md` lists every premise of the theorem and what it does not say.

Example: a guest that sums its input, writes the sum to the output region and ends in
`jal x0, 0` has a Sail run that stops at that self-jump, and Jolt's trace of it has the same
outputs.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltConstraints.Soundness

set_option autoImplicit false

noncomputable section

namespace WholeRun

open private initial_image_facts from JoltConstraints.WholeRun.CodeInv

/-! ## The start of the run -/

/-- Jolt's initial state has `nextPC` at the program's entry.
Example: an ELF with entry `0x80000000` starts with `nextPC = 0x80000000`. -/
theorem initialized_nextPC {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {init : SailJoltState}
    (initialized : joltInstance.initial_state privateInputs = some init) :
    init.sail.regs.get? Register.nextPC = some joltInstance.program.entry_address := by
  have built := initialized
  unfold JoltInstance.initial_state at built
  cases layout : joltInstance.memory_layout with
  | none => simp only [layout, bind, Option.bind] at built; cases built
  | some value =>
    simp only [layout, bind, Option.bind] at built
    split_ifs at built
    have stateEq := Option.some.inj built
    rw [← stateEq]
    exact init_state_register _ _ _ _ _ Register.nextPC

/-- **The run starts in the relation.** `RunRel.initial` for an initial state that is not yet
the start of a trace: Sail's `sailInit` of Jolt's initial state is related to it.
Example: the initial state of any instance whose heap ends below `2^64 - 8`. -/
theorem RunRel.ofInitialized {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {init : SailJoltState}
    (initialized : joltInstance.initial_state privateInputs = some init)
    (hheap : joltInstance.HeapNoWrap) :
    RunRel joltInstance.program init (sailInit init) := by
  refine ⟨related_sailInit joltInstance privateInputs init initialized, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨ram, device, tape, he⟩ := initial_state_spec joltInstance privateInputs _ initialized
    rw [he]
    exact SystemInv.init_state _ _ _ _
  · exact hheap _ (initial_state_device joltInstance privateInputs init initialized).1
  · obtain ⟨hend, hbytes⟩ := initial_image_facts joltInstance privateInputs _ initialized
    exact ⟨hend, fun _ _ _ _ b hb => hbytes _ b hb⟩

/-! ## Where the run stops -/

/-- **Sail stalls.** The step from `s` to `s'` leaves `PC` at the address of an image row, and the
last row of that instruction's Jolt expansion would jump there again if re-run
(`JoltInstructionRow.selfJumpRepeats`). This is Jolt's termination convention: its tracer stops
after such a step.
Example: Sail running `jal x0, 0` stalls. -/
def SailStalls (program : Rv64ProgramImage SourceInstruction) (s s' : SailState) : Prop :=
  ∃ (pc : BitVec 64) (row : SourceInstructionRow SourceInstruction),
    s.regs.get? Register.PC = some pc ∧ s'.regs.get? Register.PC = some pc ∧
    rowAt program pc = some row ∧
    ∀ rows, expand_instruction row = some rows → ∀ last ∈ rows.getLast?,
      last.selfJumpRepeats = true

/-- **Sail is at a jump.** The image row at Sail's `PC` expands to rows whose last one is a jump.
Jolt's prover accepts only a trace whose last row is a jump.
Example: Sail at `jal x0, 0` is at a jump; Sail at `beq x0, x0, 0` is not. -/
def SailAtJump (program : Rv64ProgramImage SourceInstruction) (s : SailState) : Prop :=
  ∃ (pc : BitVec 64) (row : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (last : JoltInstructionRow),
    s.regs.get? Register.PC = some pc ∧ rowAt program pc = some row ∧
    expand_instruction row = some rows ∧ rows.getLast? = some last ∧
    last.instruction.is_jump = true

/-- A related Jolt state has a `nextPC`, and it is Sail's `PC`. -/
theorem Related.nextPC_some {jt : SailJoltState} {s : SailState} (h : Related jt s) :
    ∃ pc, jt.sail.regs.get? Register.nextPC = some pc ∧ s.regs.get? Register.PC = some pc := by
  obtain ⟨pc, m, inc, hn, -⟩ := h.regs
  exact ⟨pc, hn, h.pc_eq_nextPC hn⟩

/-- A block that runs between two related states stalls exactly when Sail's step between them
stalls.
Example: a `jal x0, 0` block and Sail's step over it both stall. -/
theorem Block.stalls_iff {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) {s s' : SailState} (hpre : Related b.pre s)
    (hpost : Related b.post s') : b.Stalls ↔ SailStalls program s s' := by
  have hs : s.regs.get? Register.PC = some b.row.address := hpre.pc_eq_nextPC runs.continues
  obtain ⟨next, hnext, hs'⟩ := hpost.nextPC_some
  unfold Block.Stalls SailStalls
  constructor
  · rintro ⟨stall, repeats⟩
    rw [stall] at hnext
    cases hnext
    exact ⟨b.row.address, b.row, hs, hs', runs.at_row, repeats⟩
  · rintro ⟨pc, row, hpc, hpc', hrow, repeats⟩
    rw [hs] at hpc
    cases hpc
    rw [runs.at_row] at hrow
    cases hrow
    rw [hs'] at hpc'
    cases hpc'
    exact ⟨hnext, repeats⟩

/-! ## The backward step -/

/-- Two platform steps from a state whose next instruction is not an inline call end in the
same state: both are `try_step`, which is a function.
Example: two platform steps over an ADDI. -/
theorem PlatformStep.eq_of_notInline {s t u : SailState} (notInline : NotInlineAt s)
    (first : PlatformStep s t) (second : PlatformStep s u) : t = u := by
  cases first with
  | sail _ step₁ =>
    cases second with
    | sail _ step₂ =>
      rw [step₁] at step₂
      cases step₂
      rfl
    | inline _ fetched call =>
      have := notInline _ _ fetched
      rw [call] at this
      cases this
  | inline _ fetched call =>
    have := notInline _ _ fetched
    rw [call] at this
    cases this

/-- **What Jolt does at one step of a Sail run.** Jolt's block `b` starts at the Jolt state `jt`
related to Sail's state before the step, and `s'` is Sail's state after the step.
* `runs`: Jolt's tracer runs the block (`Block.Runs`).
* `accesses`: every RAM access of the block's rows lies in Jolt's memory map
  (`Block.AccessesInMap`): it is at least the layout's lowest address `lowest`.
* `conforms`, `no_low_load`, `not_ebreak`: the conditions of `PlatformConforms.simulates`, the
  same as for soundness.
* `inline_lands`: an inline call's last state is related to Sail's state after the step. The
  platform may store any result that meets the call's specification, and this field says that it
  stored Jolt's.

Example: an ADDI block whose `rs1` is in range has `JoltStep` from every related state. -/
structure JoltStep (program : Rv64ProgramImage SourceInstruction) (lowest : Nat)
    (jt : SailJoltState) (s' : SailState) (b : Block) : Prop where
  pre : b.pre = jt
  runs : b.Runs program
  accesses : b.AccessesInMap lowest
  conforms : PlatformConforms program b
  no_low_load : ∀ i, b.row.instruction = .riscv i → i.IoAccess b.start → i.NoLowLoad b.start
  not_ebreak : b.row.instruction ≠ .riscv .EBREAK
  inline_lands : ∀ key rs1 rs2 rd, b.row.instruction = .inline key rs1 rs2 rd →
    RunRel program b.post s'

/-- **The backward step.** If Sail plus the platform steps from `s` to `s'`, Jolt's state `jt` is
related to `s`, and Jolt runs block `b` from `jt` (`JoltStep`), then `b`'s last state is related to
`s'`.
Example: Sail's step over an ADDI and Jolt's ADDI block end in related states. -/
theorem JoltStep.lands {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) (hrows : program.RowsAligned) {lowest : Nat}
    {jt : SailJoltState} {s s' : SailState} {b : Block} (step : PlatformStep s s')
    (hrel : RunRel program jt s) (h : JoltStep program lowest jt s' b) :
    RunRel program b.post s' := by
  rcases h.conforms.supported with ⟨i, hrow⟩ | ⟨key, rs1, rs2, rd, call⟩
  · have hR : RunRel program b.pre s := by rw [h.pre]; exact hrel
    obtain ⟨s'', step', hR'⟩ :=
      h.conforms.simulates hdecoded hrows h.runs h.no_low_load h.not_ebreak s hR
    have notInline : NotInlineAt s := notInline_of_riscv program b h.runs hdecoded.imageDecoded
      hrow (h.runs.pc_even hrows) (fun t ht => CodeIntact.of_related ht hR.2.2) s hR.1
    rw [← PlatformStep.eq_of_notInline notInline step' step]
    exact hR'
  · exact h.inline_lands key rs1 rs2 rd call

/-- Jolt's embedded `misa` holds a value with the C bit set. Jolt's initial state has one, and Jolt's
rows keep it (`MisaC.of_runs`). -/
def MisaC (jt : SailJoltState) : Prop :=
  ∃ misa : RegisterType Register.misa,
    jt.sail.regs.get? Register.misa = some misa ∧ _get_Misa_C misa = 1#1

/-- A Jolt program that runs keeps the embedded `misa`. -/
theorem execProgram_keeps_misa (p : JoltISA.Program) (s t : SailJoltState)
    {r : ExecutionResult} (h : JoltISA.execProgram p s = .ok r t) :
    t.sail.regs.get? Register.misa = s.sail.regs.get? Register.misa := by
  induction p generalizing s t with
  | done result =>
    simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    rw [h.2]
  | instr i rest ih =>
    simp only [JoltISA.execProgram, bind, EStateM.bind] at h
    cases hi : JoltISA.execInstr i s with
    | error e s' => simp [hi] at h
    | ok result s' =>
      have step := JoltConstraints.Soundness.execInstr_keeps_misa i s s' result hi
      simp only [hi] at h
      cases result with
      | Retire_Success u => exact (ih s' t h).trans step.symm
      | _ =>
        simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
        rw [← h.2]
        exact step.symm

/-- A block that runs keeps `MisaC`. -/
theorem MisaC.of_runs {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) (h : MisaC b.pre) : MisaC b.post := by
  obtain ⟨_, _, _, _, executed⟩ := runs.executes
  rw [MisaC, execProgram_keeps_misa _ _ _ executed, Block.start,
    JoltConstraints.Soundness.advance_pc_misa]
  exact h

/-- Jolt's initial state satisfies `MisaC`. -/
theorem MisaC.initial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {init : SailJoltState}
    (initialized : joltInstance.initial_state privateInputs = some init) : MisaC init :=
  ⟨_, JoltConstraints.Soundness.initial_state_misa joltInstance privateInputs init initialized,
    by decide⟩

/-- **Jolt follows the Sail run.** At each of the first `n` steps of `run`, from every Jolt state
related to Sail's state whose embedded `misa` has the C bit set (`MisaC`), Jolt runs a block that
meets `JoltStep`.
Example: a run of RISC-V instructions whose accesses stay in RAM, on a conforming guest. -/
def JoltFollows (program : Rv64ProgramImage SourceInstruction) (lowest : Nat)
    (run : Nat → SailState) (n : Nat) : Prop :=
  ∀ k < n, ∀ jt, RunRel program jt (run k) → MisaC jt →
    ∃ b, JoltStep program lowest jt (run (k + 1)) b

/-- **The blocks of a Sail run.** If Jolt follows the first `n` steps of a run from a state
related to Jolt's `init`, then for every `m ≤ n` a chain of `m` blocks starts at `init`, block `k`
goes from a state related to Sail's state `k` to one related to Sail's state `k + 1`, and the
chain ends in a state related to Sail's state `m`.
Example: a run of two ADDI steps gives two ADDI blocks. -/
theorem blocks_of_run {program : Rv64ProgramImage SourceInstruction} {elf : ElfSections}
    (hdecoded : program.DecodedFrom elf) (hrows : program.RowsAligned) {lowest : Nat}
    {run : Nat → SailState} {n : Nat} {init : SailJoltState}
    (start : RunRel program init (run 0)) (startMisa : MisaC init)
    (steps : ∀ k < n, PlatformStep (run k) (run (k + 1)))
    (follows : JoltFollows program lowest run n) :
    ∀ m ≤ n, ∃ blocks : List Block, blocks.length = m ∧
      (∀ b ∈ blocks, b.Runs program ∧ b.AccessesInMap lowest ∧ PlatformConforms program b) ∧
      blocks.IsChain (fun b c => b.post = c.pre) ∧
      (∀ f ∈ blocks.head?, f.pre = init) ∧
      RunRel program ((blocks.getLast?.map (·.post)).getD init) (run m) ∧
      MisaC ((blocks.getLast?.map (·.post)).getD init) ∧
      ∀ k (hk : k < blocks.length),
        RunRel program blocks[k].pre (run k) ∧ RunRel program blocks[k].post (run (k + 1)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], rfl, by simp, List.isChain_nil, by simp, start, startMisa,
      fun k hk => absurd hk (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨blocks, len, props, chain, first, endRel, endMisa, each⟩ := ih (by omega)
    obtain ⟨b, hb⟩ := follows m (by omega) _ endRel endMisa
    have post := hb.lands hdecoded hrows (steps m (by omega)) endRel
    refine ⟨blocks ++ [b], by simp [len], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact props c hc
      · rw [List.mem_singleton] at hc
        subst hc
        exact ⟨hb.runs, hb.accesses, hb.conforms⟩
    · refine List.IsChain.append chain (List.isChain_singleton b) ?_
      intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hb.pre, hx]
      rfl
    · intro f hf
      cases blocks with
      | nil =>
        simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hf
        subst hf
        rw [hb.pre]
        rfl
      | cons x xs =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hf
        subst hf
        exact first _ rfl
    · simpa only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.map_some, Option.getD_some] using post
    · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.map_some, Option.getD_some]
      exact MisaC.of_runs hb.runs (hb.pre ▸ endMisa)
    · intro k hk
      by_cases early : k < blocks.length
      · rw [List.getElem_append_left early]
        exact each k early
      · have last : k = blocks.length := by simp at hk; omega
        subst last
        rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        refine ⟨?_, ?_⟩
        · rw [hb.pre, len]
          exact endRel
        · rw [len]
          exact post

/-! ## Rows that pass their assertions -/

/-- An equality assertion with a nonzero immediate: Jolt's spoil assert, which a run reaching it
must satisfy.
Example: `VirtualAssertEQ x1 x2 1` is a spoil assert; `VirtualAssertEQ x1 x2 0` is not. -/
def _root_.JoltISA.Instr.isSpoilAssert : JoltISA.Instr → Bool
  | .VirtualAssertEQ _ _ imm => imm != 0
  | _ => false

/-- Rewriting a native row's destination (`Instr.rewriteNative`) keeps whether it is a spoil
assert.
Example: `ADD x0, x1, x2` becomes the canonical no-op, and neither is a spoil assert. -/
theorem rewriteNative_isSpoilAssert (x : JoltISA.Instr) :
    x.rewriteNative.isSpoilAssert = x.isSpoilAssert := by
  unfold JoltISA.Instr.rewriteNative
  split
  all_goals try rfl
  split
  all_goals try rfl
  split
  · cases x <;> simp_all [JoltISA.Instr.destination?, JoltISA.Instr.isSpoilAssert,
      JoltISA.Instr.canonicalNoOp]
  · rfl

/-- A RISC-V instruction's native row is not a spoil assert.
Example: ADDI's native row is an ADDI. -/
theorem riscv_native_not_spoil (i : RiscvInstruction) (x : JoltISA.Instr)
    (h : (SourceInstruction.riscv i).expand = some (.native x)) : x.isSpoilAssert = false := by
  cases i <;> simp only [SourceInstruction.expand, ExpandedSource.ofNative,
    ExpandedSource.ofProgram, ExpandedSource.ofPureProgram, Option.some.injEq,
    ExpandedSource.native.injEq, reduceCtorEq] at h
  all_goals first
    | (subst h; rw [rewriteNative_isSpoilAssert]; rfl)
    | (split at h
       · cases h; rfl
       · cases h)

/-- **RISC-V instructions and inline calls expand to no spoil assert.** Only Jolt's own
`VirtualAssertEQ` source instruction is one.
Example: DIV's nine rows contain zero-immediate assertions only. -/
theorem expand_instruction_no_spoil (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows)
    (supported : (∃ i, source.instruction = .riscv i) ∨
      ∃ key rs1 rs2 rd, source.instruction = .inline key rs1 rs2 rd) :
    ∀ row ∈ rows, row.instruction.isSpoilAssert = false := by
  have checks := ExpansionFacts.expand_instruction_checks source rows expanded
  have mapped : ∀ instr ∈ rows.map (·.instruction), instr.isSpoilAssert = false := by
    cases shape : source.instruction.expand with
    | none => simp only [shape] at checks
    | some result =>
      cases result with
      | native instruction =>
        simp only [shape] at checks
        rw [checks.1]
        intro instr hm
        rw [List.mem_singleton] at hm
        subst hm
        rcases supported with ⟨i, hi⟩ | ⟨key, rs1, rs2, rd, hi⟩
        · rw [hi] at shape
          exact riscv_native_not_spoil i _ shape
        · rw [hi] at shape
          simp only [SourceInstruction.expand] at shape
          split at shape <;> cases shape
      | sequence instructions =>
        simp only [shape] at checks
        rw [checks.1]
        have none := ExpansionFacts.sequenceOk_noSpoilAsserts instructions checks.2.1
        intro instr hm
        have each := List.all_eq_true.mp
          (by simpa only [ExpansionFacts.noSpoilAsserts] using none) instr hm
        cases instr <;> simp_all [JoltISA.Instr.isSpoilAssert]
  intro row hrow
  exact mapped _ (List.mem_map_of_mem hrow)

/-! ## Prover acceptance -/

/-- **Jolt's prover accepts a trace** that starts from the instance's initial state, ends in a
jump, fits the maximum trace length, records only RAM addresses in Jolt's memory map, and whose
instance has ordered verifier RAM bounds.
Example: a 300-row trace ending in `jal x0, 0` pads to 512 rows. -/
theorem prover_config_some (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (trace : Trace)
    (initialized : joltInstance.initial_state privateInputs = some trace.initialState)
    (endsInJump : ∀ last ∈ trace.rows.back?,
      trace.bytecode[last.rowIndex].instruction.is_jump = true)
    (fits : ∃ padded, ProverConfig.checkedTraceLength trace.rows.size = some padded ∧
      padded ≤ joltInstance.max_padded_trace_length.toNat)
    (inMap : ∀ r ∈ trace.rows,
      RowInMap trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat r)
    (ramBounds : ∃ minimum maximum,
      joltInstance.verifier_ram_bounds = some (minimum, maximum) ∧ minimum ≤ maximum) :
    ∃ config, trace.prover_config joltInstance = some config := by
  let layout := trace.initialState.jolt_device.memory_layout
  obtain ⟨padded, paddedComputed, paddedFits⟩ := fits
  obtain ⟨touched, touchedComputed, touchedBound⟩ := JoltInstance.checked_touched_of_address_bounds
    (trace.rows.toList.filterMap (·.ram_address)) layout (by
      intro address member
      obtain ⟨r, hr, haddress⟩ := List.mem_filterMap.mp member
      exact ⟨TraceRow.ram_address_lt r address haddress,
        inMap r (Array.mem_toList_iff.mp hr) address haddress⟩)
  obtain ⟨minimum, maximum, bounds, ordered⟩ := ramBounds
  have layoutBuilt := (initial_state_device joltInstance privateInputs trace.initialState
    initialized).1
  unfold JoltInstance.verifier_ram_bounds at bounds
  rw [layoutBuilt] at bounds
  simp only [bind_some_iff, Option.some.injEq] at bounds
  obtain ⟨_, rfl, minSize, minimumComputed, maxSize, maximumComputed, result⟩ := bounds
  have pairEq : (minSize, maxSize) = (minimum, maximum) := Option.some.inj result
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
  obtain ⟨start, finish, remapped, added, finishBound⟩ :=
    JoltInstance.verifier_ram_image_end_bounded joltInstance.program layout minSize maxSize
      minimumComputed maximumComputed ordered
  have sentinelFits : finish + 1 < 2 ^ 64 := by omega
  have totalBound : max (touched + 1) (finish + 1) ≤ 2 ^ 62 := by omega
  have roundedBound : 2 ^ Nat.clog 2 (max (touched + 1) (finish + 1)) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow totalBound)
  have roundedFits : 2 ^ Nat.clog 2 (max (touched + 1) (finish + 1)) < 2 ^ 64 := by omega
  have ramComputed : ProverConfig.checkedRamSize trace.execution_dimensions layout
      (min_bytecode_address joltInstance.program.memory_init)
      (program_image_len_words joltInstance.program.memory_init) =
      some (2 ^ Nat.clog 2 (max (touched + 1) (finish + 1))) := by
    simp only [ProverConfig.checkedRamSize, bind_some_iff]
    refine ⟨touched, touchedComputed, start, remapped, finish, added, finish + 1, ?_, ?_⟩
    · simp only [MemoryLayout.checkedAdd, ite_eq_left_of_eq_true _ _ (eq_true sentinelFits)]
    · simp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo,
        ite_eq_left_of_eq_true _ _ (eq_true roundedFits)]
  have jump : trace.execution_dimensions.trace_length = 0 ∨
      trace.execution_dimensions.ends_in_jump = true := by
    by_cases empty : trace.rows.size = 0
    · exact Or.inl empty
    · right
      obtain ⟨last, hlast⟩ : ∃ last, trace.rows.back? = some last :=
        ⟨_, by rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_getElem (by omega)⟩
      show trace.rows.back?.any _ = true
      rw [hlast]
      exact endsInJump last hlast
  have lengthComputed : ProverConfig.checkedTraceLength trace.execution_dimensions.trace_length =
      some padded := paddedComputed
  refine ⟨{ trace_length := padded, ram_K := 2 ^ Nat.clog 2 (max (touched + 1) (finish + 1)) }, ?_⟩
  have guardJump : (guard (trace.execution_dimensions.trace_length = 0 ∨
      trace.execution_dimensions.ends_in_jump = true) : Option Unit) = some () := by
    unfold guard
    exact ite_eq_left_of_eq_true _ _ (eq_true jump)
  have guardFits : (guard (padded ≤ joltInstance.max_padded_trace_length.toNat) : Option Unit) =
      some () := by
    unfold guard
    exact ite_eq_left_of_eq_true _ _ (eq_true paddedFits)
  unfold Trace.prover_config ProverConfig.deriveFromDimensions
  rw [guardJump]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [lengthComputed]
  simp only [Option.bind_some]
  rw [ramComputed]
  simp only [Option.bind_some]
  rw [guardFits]
  rfl

/-! ## The run's length -/

/-- The number of Jolt rows of the image row at Sail's `PC` (0 if there is none).
Example: at a DIV, nine. -/
def rowCountAt (program : Rv64ProgramImage SourceInstruction) (s : SailState) : Nat :=
  match s.regs.get? Register.PC with
  | some pc => (((rowAt program pc).bind expand_instruction).map List.length).getD 0
  | none => 0

/-- **The number of Jolt rows of a Sail run**: the rows of the image rows at the first `n`
states. Jolt's trace of the run has this many rows, before padding.
Example: a run of an ADDI and a DIV has ten rows. -/
def sailRowCount (program : Rv64ProgramImage SourceInstruction) (run : Nat → SailState)
    (n : Nat) : Nat :=
  ((List.range n).map fun k => rowCountAt program (run k)).sum

/-- A block that runs from a state related to Sail's has as many rows as the image row at Sail's
`PC`. -/
theorem Block.rowCount_eq {program : Rv64ProgramImage SourceInstruction} {b : Block}
    (runs : b.Runs program) {s : SailState} (hpre : Related b.pre s) :
    b.rowCount = rowCountAt program s := by
  unfold rowCountAt Block.rowCount
  rw [hpre.pc_eq_nextPC runs.continues]
  simp only [runs.at_row, Option.bind_some]

end WholeRun

open WholeRun in
/-- **Completeness from Sail.** Let a run of Sail plus the platform go from `sailInit` of the
instance's initial state `init` through the states `run 0, ..., run n`, and stop at Jolt's
termination convention. If Jolt follows every step of the run and the run fits Jolt's limits,
then Jolt's tracer has an honest trace from `init` with the run's outputs and panic flag, its
rows pass their assertions, Jolt's prover accepts it, and the witness the prover builds from it
satisfies `AllConstraints`. The trace's inline advice words are those its inline calls record.

Premises, by class:
* the instance: `assumptions` (`CompletenessAssumptions`), `initialized` (`init` is Jolt's initial
  state for `privateInputs`), `accepted` (Jolt's preprocessing builds the bytecode), `valid`
  (`validate_inputs`), `ramBounds` (the verifier's RAM bounds exist and are ordered);
* platform, as for soundness: `hdecoded` (`DecodedFrom`), `hrows` (`RowsAligned`), `hheap`
  (`HeapNoWrap`);
* the run: `start` and `steps` (a run of `PlatformStep` from `sailInit init`);
* termination: `stops` (the last step is a stable self-jump, `SailStalls`, at an instruction whose
  last Jolt row is a jump, `SailAtJump`) and `runsUntilStop` (no earlier step stalls). A run that
  reaches an EBREAK is excluded through `JoltStep.not_ebreak`;
* length: `fits` (the run's row count, padded, fits `max_padded_trace_length`);
* Jolt follows the run (`JoltFollows`): at every step, Jolt runs a block from the related state
  (`Block.Runs`), the block's RAM accesses lie at or above the layout's lowest address
  (`Block.AccessesInMap`), the block conforms (`PlatformConforms`, `NoLowLoad`, not EBREAK), and an
  inline call stores Jolt's result (`JoltStep.inline_lands`). This premise covers Jolt's tracer
  not faulting where Sail does not, including the I/O gap and the store checks of
  `docs/riscv-alignment.md` section 3;
* the claim: `claimsOutputs` and `claimsPanic` (the instance claims the run's outputs and panic
  flag, trailing zero bytes dropped).

The conclusion inherits the sorries of `JoltInstance.completeness`.
`docs/whole-run-theorem.md` lists what the theorem does not say.

For example, a guest that writes its input's sum to the output region and ends in `jal x0, 0`
has a Sail run that stops at the self-jump, and Jolt's witness for that run satisfies
`AllConstraints`. -/
theorem JoltInstance.sail_completeness {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (privateInputs : JoltPrivateInputs) {init : SailJoltState}
    (initialized : joltInstance.initial_state privateInputs = some init)
    (accepted : joltInstance.bytecode.isSome) (valid : joltInstance.validate_inputs = true)
    (ramBounds : ∃ minimum maximum,
      joltInstance.verifier_ram_bounds = some (minimum, maximum) ∧ minimum ≤ maximum)
    {elf : ElfSections} (hdecoded : joltInstance.program.DecodedFrom elf)
    (hrows : joltInstance.program.RowsAligned) (hheap : joltInstance.HeapNoWrap)
    (run : Nat → SailState) (n : Nat) (start : run 0 = sailInit init)
    (steps : ∀ k < n, PlatformStep (run k) (run (k + 1)))
    (stops : 0 < n ∧ SailStalls joltInstance.program (run (n - 1)) (run n) ∧
      SailAtJump joltInstance.program (run (n - 1)))
    (runsUntilStop : ∀ k, k + 1 < n → ¬ SailStalls joltInstance.program (run k) (run (k + 1)))
    (fits : ∃ padded,
      ProverConfig.checkedTraceLength (sailRowCount joltInstance.program run n) = some padded ∧
      padded ≤ joltInstance.max_padded_trace_length.toNat)
    (follows : JoltFollows joltInstance.program
      init.jolt_device.memory_layout.get_lowest_address.toNat run n)
    (claimsOutputs : trimTrailingZeros (sailOutputs init.jolt_device (run n)) =
      trimTrailingZeros joltInstance.outputs)
    (claimsPanic : sailPanicWord init.jolt_device (run n) ≠ 0 ↔ joltInstance.panic = true) :
    ∃ (words : Array (BitVec 64))
      (trace : HonestTrace joltInstance { privateInputs with inline_advice := words })
      (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config),
      trace.initialState = init ∧ trace.matches_outputs joltInstance ∧ trace.SpoilAssertsPass ∧
      JoltConstraints.AllConstraints joltInstance
        (JoltConstraints.adviceBlockWords trace.initialState.jolt_device.memory_layout
          (TraceWitness.initialRamWord trace))
        (HonestTrace.honestWitness (F := F) (trace.witness_params config proverAccepts) trace) := by
  have start' : RunRel joltInstance.program init (run 0) := by
    rw [start]
    exact RunRel.ofInitialized initialized hheap
  obtain ⟨blocks, len, props, chain, first, endRel, -, each⟩ :=
    blocks_of_run hdecoded hrows start' (MisaC.initial initialized) steps follows n le_rfl
  obtain ⟨npos, lastStall, lastJump⟩ := stops
  have stallIff : ∀ k (hk : k < blocks.length),
      blocks[k].Stalls ↔ SailStalls joltInstance.program (run k) (run (k + 1)) :=
    fun k hk => Block.stalls_iff (props _ (List.getElem_mem hk)).1 (each k hk).1.1 (each k hk).2.1
  have nonempty : blocks ≠ [] := by
    intro empty
    rw [empty] at len
    simp only [List.length_nil] at len
    omega
  obtain ⟨bytecode, expanded⟩ : ∃ bytecode, expand_program joltInstance.program = some bytecode := by
    cases h : expand_program joltInstance.program with
    | none =>
      unfold JoltInstance.bytecode at accepted
      simp [h] at accepted
    | some value => exact ⟨value, rfl⟩
  have firstOk : ∀ f ∈ blocks.head?, f.row.address = joltInstance.program.entry_address ∧
      f.pre = init := by
    intro f hf
    have pre := first f hf
    refine ⟨?_, pre⟩
    have cont := (props f (List.mem_of_mem_head? hf)).1.continues
    rw [pre, initialized_nextPC initialized] at cont
    exact (Option.some.inj cont).symm
  have lastIndex : n - 1 < blocks.length := by omega
  let final := blocks[n - 1]'lastIndex
  have hfinal : blocks.getLast? = some final := by
    rw [List.getLast?_eq_getElem?, len]
    exact List.getElem?_eq_getElem _
  have stopsOk : ∀ l ∈ blocks.getLast?, l.Stalls := by
    intro l hl
    rw [hfinal] at hl
    simp only [Option.mem_def, Option.some.injEq] at hl
    subst hl
    have stall := (stallIff (n - 1) lastIndex).mpr
    rw [show n - 1 + 1 = n by omega] at stall
    exact stall lastStall
  have noStallOk : ∀ b ∈ blocks.dropLast, ¬ b.Stalls := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_dropLast]
    simp only [List.length_dropLast] at hk
    intro stall
    exact runsUntilStop k (by omega) ((stallIff k (by omega)).mp stall)
  obtain ⟨words, trace, initEq, size, lastFacts, members⟩ := HonestTrace.ofBlocks initialized
    accepted valid expanded blocks nonempty (fun b hb => (props b hb).1) chain firstOk stopsOk
    noStallOk
  have finalMem : final ∈ blocks := List.mem_of_getLast? hfinal
  have finalRel : RunRel joltInstance.program final.post (run n) := by
    have rel := endRel
    rw [hfinal] at rel
    exact rel
  have layoutEq : final.post.jolt_device.memory_layout = init.jolt_device.memory_layout :=
    (chain_layout joltInstance.program blocks init chain (fun b hb => (props b hb).1) first final
      finalMem).2
  obtain ⟨lastRow, hlastRow⟩ : ∃ r, trace.rows.back? = some r :=
    ⟨_, by
      rw [Array.back?_eq_getElem?]
      exact Array.getElem?_eq_getElem (by have := trace.nonempty; omega)⟩
  obtain ⟨lastPost, lastSegment⟩ := lastFacts lastRow hlastRow final hfinal
  have outputsMatch : trace.matches_outputs joltInstance := by
    unfold Trace.matches_outputs
    have back : trace.toTrace.rows.back? = some lastRow := hlastRow
    simp only [back, Option.map_some, Option.getD_some, lastPost]
    refine ⟨?_, ?_⟩
    · rw [← finalRel.1.outputs, sailOutputs_congr layoutEq]
      exact claimsOutputs
    · rw [Bool.eq_iff_iff, finalRel.1.panic, sailPanicWord_congr layoutEq]
      exact claimsPanic
  have spoil : trace.SpoilAssertsPass := by
    intro row hrow lhs rhs imm hinstr himm
    exfalso
    obtain ⟨b, hb, ⟨segment, emits, member⟩, -⟩ := members row hrow
    have none := expand_instruction_no_spoil b.row segment emits (props b hb).2.2.supported _ member
    rw [hinstr] at none
    simp only [JoltISA.Instr.isSpoilAssert, bne_eq_false_iff_eq] at none
    exact himm none
  have endsInJump : ∀ last ∈ trace.toTrace.rows.back?,
      trace.toTrace.bytecode[last.rowIndex].instruction.is_jump = true := by
    intro last hl
    have back : trace.toTrace.rows.back? = some lastRow := hlastRow
    rw [back] at hl
    simp only [Option.mem_def, Option.some.injEq] at hl
    subst hl
    obtain ⟨pc, row, rows, lastOf, hpc, hrow, hexp, hgl, hjump⟩ := lastJump
    have finalRuns := (props final finalMem).1
    have pcEq := (each (n - 1) lastIndex).1.1.pc_eq_nextPC finalRuns.continues
    rw [hpc] at pcEq
    cases pcEq
    rw [finalRuns.at_row] at hrow
    cases hrow
    have getLast := lastSegment rows hexp
    rw [hgl] at getLast
    cases getLast
    exact hjump
  have rowSum : (blocks.map Block.rowCount).sum = sailRowCount joltInstance.program run n := by
    unfold sailRowCount
    congr 1
    apply List.ext_getElem (by simp [len])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map] at h1
    exact Block.rowCount_eq (props _ (List.getElem_mem h1)).1 (each k h1).1.1
  have inMap : ∀ r ∈ trace.toTrace.rows,
      RowInMap trace.toTrace.initialState.jolt_device.memory_layout.get_lowest_address.toNat r := by
    intro r hr
    obtain ⟨b, hb, -, access⟩ := members r hr
    have initEq' : trace.toTrace.initialState = init := initEq
    rw [initEq']
    exact access _ (props b hb).2.1
  obtain ⟨config, proverAccepts⟩ := prover_config_some joltInstance _ trace.toTrace
    trace.initialized endsInJump (by
      have size' : trace.toTrace.rows.size = (blocks.map Block.rowCount).sum := size
      rw [size', rowSum]
      exact fits) inMap ramBounds
  exact ⟨words, trace, config, proverAccepts, initEq, outputsMatch, spoil,
    JoltInstance.completeness joltInstance assumptions _ trace outputsMatch spoil config proverAccepts⟩
