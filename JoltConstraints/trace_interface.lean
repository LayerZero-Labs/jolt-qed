/-
The facts the completeness proofs used to take as fields of the old trace
(trace.lean and program.lean, deleted; see git d044e63), each one proved here for the
honest trace. Names and shapes match the old ones, so the proofs that use them
change as little as possible. The facts about what `expand` emits are one sorried
theorem, `expand_program_rows_valid`, until `expand` is defined.
-/
import JoltConstraints.ProgramLayout
import JoltConstraints.execution_facts
import JoltConstraints.layout_facts
import JoltConstraints.register_encoding

set_option autoImplicit false

-- The length of row i's source instruction: 2 bytes if compressed, else 4.
def sourceLength (bytecode : Array JoltInstructionRow) (i : Fin bytecode.size) : Nat :=
  if source_is_compressed bytecode i then 2 else 4

-- Move the PC to the start of row i's source instruction, as Rust's tick does: PC is
-- the instruction's address and nextPC is its length further on.
-- See : jolt/tracer/src/emulator/cpu.rs:628-632 (tick_operate)
noncomputable def prepareSource (bytecode : Array JoltInstructionRow) (i : Fin bytecode.size)
    (state : SailJoltState) : SailJoltState :=
  let address := bytecode[i].address
  let regs := (state.sail.regs.insert Register.PC address).insert Register.nextPC
    (address + BitVec.ofNat 64 (sourceLength bytecode i))
  { state with sail := { state.sail with regs := regs } }

-- prepareSource is the honest trace's advance_pc at the row's source address.
theorem prepareSource_eq_advance_pc (bytecode : Array JoltInstructionRow)
    (i : Fin bytecode.size) (state : SailJoltState) :
    prepareSource bytecode i state =
      advance_pc bytecode[i].address (source_is_compressed bytecode i) state := by
  unfold prepareSource advance_pc sourceLength
  cases source_is_compressed bytecode i <;> rfl

-- The Sail facts the completeness proofs need at each row's pre-state.
structure TraceAssumptions (js : SailJoltState) : Prop where
  xRegReadable : ∀ r, Assumptions.XRegReadable r js.sail

-- Every row of an honest trace starts with every register readable.
theorem HonestTrace.rowAssumptions {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.rows.size) : TraceAssumptions trace.rows[i].preState :=
  ⟨readable_of_present _
    (trace.registers_present i.val _ (Array.getElem?_eq_getElem i.isLt))⟩

-- Every register, real or virtual, starts at 0.
theorem HonestTrace.initialRegistersZero {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (src : JoltISA.Src) : JoltISA.sourceValue src trace.initialState = 0 :=
  initial_state_sourceValue joltInstance privateInputs trace.initialState trace.initialized src

-- The instance's initial state has PC at the program's entry address.
-- See : jolt/tracer/src/lib.rs:364-408 (create_emulator)
theorem initial_state_pc {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) :
    initialState.sail.regs.get? Register.PC = some joltInstance.program.entry_address := by
  unfold JoltInstance.initial_state at built
  rw [bind_some_iff] at built
  obtain ⟨layout, _, built⟩ := built
  dsimp only at built
  -- create_emulator's three size checks
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the state init_state builds
  cases built
  rw [init_state_register]
  rfl

-- The trace starts at an instruction's first row, at the address PC holds initially.
theorem HonestTrace.startsAtEntry {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (h : 0 < trace.rows.size) :
    trace.bytecode[(trace.rows[0]'h).rowIndex].starts_source = true ∧
      trace.initialState.sail.regs.get? Register.PC =
        some trace.bytecode[(trace.rows[0]'h).rowIndex].address := by
  obtain ⟨entryAddress, starts, _⟩ :=
    trace.starts (trace.rows[0]'h) (Array.getElem?_eq_getElem h)
  refine ⟨starts, ?_⟩
  rw [entryAddress]
  exact initial_state_pc joltInstance privateInputs trace.initialState trace.initialized

-- The first row starts from the initial state with the PC moved to its instruction.
theorem HonestTrace.startsAtInitial {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (h : 0 < trace.rows.size) :
    (trace.rows[0]'h).preState =
      prepareSource trace.bytecode (trace.rows[0]'h).rowIndex trace.initialState := by
  obtain ⟨entryAddress, _, startState⟩ :=
    trace.starts (trace.rows[0]'h) (Array.getElem?_eq_getElem h)
  rw [prepareSource_eq_advance_pc, entryAddress]
  exact startState

-- How a row's state carries into the next row: unchanged inside an instruction, and
-- with the PC moved to the next instruction at its start.
theorem HonestTrace.linkedState {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (currentExists : i < trace.rows.size) (nextExists : i + 1 < trace.rows.size) :
    (trace.rows[i + 1]'nextExists).preState =
      if trace.bytecode[(trace.rows[i]'currentExists).rowIndex].continues then
        (trace.rows[i]'currentExists).postState
      else prepareSource trace.bytecode (trace.rows[i + 1]'nextExists).rowIndex
        (trace.rows[i]'currentExists).postState := by
  have link := trace.linked i _ _ (Array.getElem?_eq_getElem currentExists)
    (Array.getElem?_eq_getElem nextExists)
  unfold JoltInstructionRow.continues
  split at link
  · rename_i notLast
    rw [if_pos (bne_iff_ne.mpr notLast)]
    exact link.2
  · rename_i isLast
    rw [if_neg (by rw [bne_iff_ne]; exact isLast)]
    obtain ⟨address, _, sameAddress, _, startState⟩ := link
    rw [prepareSource_eq_advance_pc, sameAddress]
    exact startState

-- Which row comes next: the next row of the same instruction, or the first row of the
-- instruction at nextPC, which is a different address (Rust stops at a self-jump).
theorem HonestTrace.successor {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (currentExists : i < trace.rows.size) (nextExists : i + 1 < trace.rows.size) :
    if trace.bytecode[(trace.rows[i]'currentExists).rowIndex].continues then
      (trace.rows[i + 1]'nextExists).rowIndex.val = (trace.rows[i]'currentExists).rowIndex.val + 1
    else
      (trace.rows[i]'currentExists).postState.sail.regs.get? Register.nextPC =
        some trace.bytecode[(trace.rows[i + 1]'nextExists).rowIndex].address ∧
      trace.bytecode[(trace.rows[i + 1]'nextExists).rowIndex].starts_source = true ∧
      trace.bytecode[(trace.rows[i + 1]'nextExists).rowIndex].address ≠
        trace.bytecode[(trace.rows[i]'currentExists).rowIndex].address := by
  have link := trace.linked i _ _ (Array.getElem?_eq_getElem currentExists)
    (Array.getElem?_eq_getElem nextExists)
  unfold JoltInstructionRow.continues
  split at link
  · rename_i notLast
    rw [if_pos (bne_iff_ne.mpr notLast)]
    exact link.1
  · rename_i isLast
    rw [if_neg (by rw [bne_iff_ne]; exact isLast)]
    obtain ⟨address, nextPC, sameAddress, starts, _⟩ := link
    have moves := trace.runs_until_stop i _ _ (Array.getElem?_eq_getElem currentExists)
      (Array.getElem?_eq_getElem nextExists) (by simpa only [ne_eq, not_not] using isLast)
    refine ⟨by rw [sameAddress]; exact nextPC, starts, fun same => moves ?_⟩
    rw [nextPC, ← sameAddress, same]

-- A HostIO row leaves PC unchanged.
def JoltISA.Instr.HostIOPCFrame (instruction : JoltISA.Instr)
    (preState postState : SailJoltState) : Prop :=
  match instruction with
  | .VirtualHostIO .. =>
      postState.sail.regs.get? Register.PC = preState.sail.regs.get? Register.PC
  | _ => True

-- A HostIO row carries no runtime advice, so it runs exactly as it is in the bytecode.
theorem withRuntimeAdvice_hostIO {instruction : JoltISA.Instr}
    (advice : instruction.RuntimeAdvice) (first : JoltISA.Dst) (second : JoltISA.Src)
    (third : BitVec 64) (isHostIO : instruction = .VirtualHostIO first second third) :
    instruction.withRuntimeAdvice advice = .VirtualHostIO first second third := by
  subst isHostIO
  rfl

-- In an honest trace, a HostIO row leaves PC unchanged: HostIO keeps the Sail state.
theorem HonestTraceRow.hostIOPreservesPC {bytecode : Array JoltInstructionRow}
    (row : HonestTraceRow bytecode) :
    bytecode[row.rowIndex].instruction.HostIOPCFrame row.preState row.postState := by
  unfold JoltISA.Instr.HostIOPCFrame
  split
  · rename_i first second third isHostIO
    have runs := row.executes
    rw [withRuntimeAdvice_hostIO row.runtimeAdvice first second third isHostIO] at runs
    simp only [JoltISA.execInstr] at runs
    rw [execHostIO_keeps_sail _ _ _ runs]
  · trivial

-- A destination other than x0.
def JoltISA.Dst.NotX0 (dst : JoltISA.Dst) : Prop :=
  match dst with
  | .xreg rd => JoltISA.isX0 rd = false
  | .vreg _ => True

-- What every row Rust's expansions emit satisfies: a jump writes a real register and
-- is the last row of its instruction, and a write to x0 is the canonical no-op.
structure JoltInstructionRow.Valid (row : JoltInstructionRow) : Prop where
  jumpDestinationWritable :
    match row.instruction with
    | .JAL dst _ => dst.NotX0
    | .JALR dst _ _ => dst.NotX0
    | _ => True
  jumpAtSourceEnd :
    match row.instruction with
    | .JAL .. | .JALR .. => row.continues = false
    | _ => True
  x0DestinationIsNoOp :
    ∀ rd, row.instruction.destination? = some (.xreg rd) →
      JoltISA.isX0 rd = true →
      row.instruction = JoltISA.Instr.canonicalNoOp

theorem JoltInstructionRow.Valid.jal {row : JoltInstructionRow} (valid : row.Valid)
    {dst : JoltISA.Dst} {imm : BitVec 64} (isJal : row.instruction = .JAL dst imm) :
    dst.NotX0 := by
  have writable := valid.jumpDestinationWritable
  rw [isJal] at writable
  exact writable

theorem JoltInstructionRow.Valid.jalr {row : JoltInstructionRow} (valid : row.Valid)
    {dst : JoltISA.Dst} {base : JoltISA.Src} {imm : BitVec 64}
    (isJalr : row.instruction = .JALR dst base imm) : dst.NotX0 := by
  have writable := valid.jumpDestinationWritable
  rw [isJalr] at writable
  exact writable

-- A row that is not the last of its instruction leaves the pending nextPC unchanged,
-- so the next row still belongs to the same instruction.
def NoEarlyNextPCChange (bytecode : Array JoltInstructionRow) : Prop :=
  ∀ i : Fin bytecode.size, bytecode[i].continues = true →
    ∀ advice : bytecode[i].instruction.RuntimeAdvice,
      ∀ preState postState : SailJoltState,
        JoltISA.execInstr (bytecode[i].instruction.withRuntimeAdvice advice) preState =
            .ok (.Retire_Success ()) postState →
          postState.sail.regs.get? Register.nextPC = preState.sail.regs.get? Register.nextPC

-- The facts about the rows Rust's expansions emit that the completeness proofs use.
structure ExpansionRowsValid (bytecode : Array JoltInstructionRow) : Prop where
  rowValid : ∀ i : Fin bytecode.size, bytecode[i].Valid
  noEarlyNextPCChange : NoEarlyNextPCChange bytecode
  registerOperandsCanonical : ∀ i : Fin bytecode.size,
    JoltRegisterEncoding.instructionIsCanonical bytecode[i].instruction = true

-- TODO: prove once SourceInstruction.expand is defined: these are facts about the
-- instructions Rust's expansions emit.
-- See : jolt/crates/jolt-program/src/expand/
theorem expand_program_rows_valid (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ExpansionRowsValid bytecode := by
  sorry

theorem HonestTrace.rowValid {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.bytecode.size) : trace.bytecode[i].Valid :=
  (expand_program_rows_valid _ _ trace.expands).rowValid i

theorem HonestTrace.noEarlyNextPCChange {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    NoEarlyNextPCChange trace.bytecode :=
  (expand_program_rows_valid _ _ trace.expands).noEarlyNextPCChange

theorem HonestTrace.registerOperandsCanonical {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.bytecode.size) :
    JoltRegisterEncoding.instructionIsCanonical trace.bytecode[i].instruction = true :=
  (expand_program_rows_valid _ _ trace.expands).registerOperandsCanonical i
