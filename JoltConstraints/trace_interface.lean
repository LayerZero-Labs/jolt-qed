/-
Execution and program-layout facts derived from the honest trace's certificates.
These facts are not assumptions on the general trace in `trace.lean`.
The facts about what `expand` emits come from `expansion_facts.lean`.
-/
import JoltConstraints.ProgramLayout
import JoltConstraints.execution_facts
import JoltConstraints.layout_facts
import JoltConstraints.register_encoding
import JoltConstraints.nextpc_frame
import JoltConstraints.expansion_facts

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
-- is the last row of its instruction, a write to x0 is the canonical no-op, and a
-- branch is its own native row with a 13-bit offset (no expansion or inline emits a
-- branch; Rust decodes the offset from 13 bits and sign-extends it).
-- See : jolt/tracer/src/instruction/format/format_b.rs:18-27 (FormatB::parse)
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
  branchAtSourceEnd :
    match row.instruction with
    | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => row.continues = false
    | _ => True
  branchOffsetSmall :
    match row.instruction with
    | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm | .BGE _ _ imm
    | .BLTU _ _ imm | .BGEU _ _ imm => ∃ offset : BitVec 13, imm = offset.signExtend 128
    | _ => True

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

-- A branch row ends its instruction and has a 13-bit offset.
theorem JoltInstructionRow.Valid.branch {row : JoltInstructionRow} (valid : row.Valid)
    {lhs rhs : JoltISA.Src} {imm : BitVec 128}
    (isBranch : row.instruction = .BEQ lhs rhs imm ∨ row.instruction = .BNE lhs rhs imm ∨
      row.instruction = .BLT lhs rhs imm ∨ row.instruction = .BGE lhs rhs imm ∨
      row.instruction = .BLTU lhs rhs imm ∨ row.instruction = .BGEU lhs rhs imm) :
    row.continues = false ∧ ∃ offset : BitVec 13, imm = offset.signExtend 128 := by
  have ends := valid.branchAtSourceEnd
  have small := valid.branchOffsetSmall
  rcases isBranch with isBranch | isBranch | isBranch | isBranch | isBranch | isBranch
  all_goals
    rw [isBranch] at ends small
    exact ⟨ends, small⟩

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

namespace ExpansionRows

open ExpansionFacts

-- What every expanded row satisfies, read off its instruction and whether more rows
-- of its source instruction follow.
structure RowOk (row : JoltInstructionRow) : Prop where
  x0 : x0Ok row.instruction = true
  canonical : JoltRegisterEncoding.instructionIsCanonical row.instruction = true
  branchOffset : BranchOffsetOk row.instruction
  ordinaryIfContinues : row.continues = true → ordinary row.instruction = true
  immShift : immShiftOk row.instruction = true

theorem regidx_zero_of_isX0 {rd : regidx} (isZero : JoltISA.isX0 rd = true) :
    rd = regidx.Regidx 0 := by
  cases rd with
  | Regidx bits =>
    unfold JoltISA.isX0 at isZero
    have zero : bits.toNat = 0 := of_decide_eq_true isZero
    rw [BitVec.eq_of_toNat_eq (y := 0) zero]

theorem canonicalNoOp_of_isCanonicalNoOp (instruction : JoltISA.Instr)
    (noOp : isCanonicalNoOp instruction = true) :
    instruction = JoltISA.Instr.canonicalNoOp := by
  unfold isCanonicalNoOp at noOp
  split at noOp
  · rename_i dst src imm
    simp only [Bool.and_eq_true, beq_iff_eq] at noOp
    obtain ⟨⟨dstZero, srcZero⟩, immZero⟩ := noOp
    rw [regidx_zero_of_isX0 dstZero, regidx_zero_of_isX0 srcZero, immZero]
    rfl
  · cases noOp

-- A destination an expanded row writes is not x0, unless the row is the no-op.
theorem notX0_of_x0Ok (instruction : JoltISA.Instr) (dst : JoltISA.Dst)
    (isDest : instruction.destination? = some dst)
    (notNoOp : isCanonicalNoOp instruction = false) (ok : x0Ok instruction = true) :
    dst.NotX0 := by
  unfold x0Ok at ok
  rw [isDest] at ok
  cases dst with
  | xreg rd =>
    simp only [notNoOp, Bool.or_false, Bool.not_eq_eq_eq_not, Bool.not_true] at ok
    exact ok
  | vreg _ => trivial

theorem branchOffsetOk_of_not_branch (instruction : JoltISA.Instr)
    (notBranch : JoltMetadata.instructionFlag instruction .Branch = false) :
    BranchOffsetOk instruction := by
  unfold BranchOffsetOk
  split
  all_goals first
    | exact True.intro
    | (simp only [JoltMetadata.instructionFlag, Bool.true_eq_false] at notBranch)

theorem branchNotTaken_of_not_branch (instruction : JoltISA.Instr) (state : SailJoltState)
    (notBranch : JoltMetadata.instructionFlag instruction .Branch = false) :
    JoltNextPCFrame.BranchTaken instruction state = false := by
  unfold JoltNextPCFrame.BranchTaken
  split
  all_goals first
    | rfl
    | (simp only [JoltMetadata.instructionFlag, Bool.true_eq_false] at notBranch)

theorem ordinary_parts (instruction : JoltISA.Instr) (isOrdinary : ordinary instruction = true) :
    JoltMetadata.opcodeFlag instruction .Jump = false ∧
      JoltMetadata.instructionFlag instruction .Branch = false := by
  simp only [ordinary, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at isOrdinary
  exact ⟨isOrdinary.1.1, isOrdinary.1.2⟩

theorem hostIOFrame_of_ordinary (instruction : JoltISA.Instr) (preState postState : SailJoltState)
    (isOrdinary : ordinary instruction = true) :
    JoltNextPCFrame.HostIOFrame instruction preState postState := by
  unfold JoltNextPCFrame.HostIOFrame
  split
  · simp only [ordinary, Bool.and_false, Bool.false_eq_true] at isOrdinary
  · trivial

-- Runtime advice only patches VirtualAdvice, which is ordinary.
theorem ordinary_withRuntimeAdvice (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice) (isOrdinary : ordinary instruction = true) :
    ordinary (instruction.withRuntimeAdvice advice) = true := by
  unfold JoltISA.Instr.withRuntimeAdvice
  split
  · rfl
  · exact isOrdinary

-- An ordinary instruction leaves the pending nextPC unchanged.
theorem nextPC_unchanged_of_ordinary (instruction : JoltISA.Instr)
    (preState postState : SailJoltState) (isOrdinary : ordinary instruction = true)
    (runs : JoltISA.execInstr instruction preState = .ok (.Retire_Success ()) postState) :
    postState.sail.regs.get? Register.nextPC = preState.sail.regs.get? Register.nextPC :=
  JoltNextPCFrame.instruction instruction preState postState
    (ordinary_parts instruction isOrdinary).1
    (branchNotTaken_of_not_branch instruction preState (ordinary_parts instruction isOrdinary).2)
    (hostIOFrame_of_ordinary instruction preState postState isOrdinary) runs

theorem RowOk.ends {row : JoltInstructionRow} (ok : RowOk row)
    (notOrdinary : ordinary row.instruction = false) : row.continues = false := by
  cases continues : row.continues
  · rfl
  · rw [ok.ordinaryIfContinues continues] at notOrdinary
    cases notOrdinary

theorem RowOk.valid {row : JoltInstructionRow} (ok : RowOk row) : row.Valid where
  jumpDestinationWritable := by
    split
    · next dst imm isJal =>
      exact notX0_of_x0Ok _ dst (by rw [isJal]; rfl) (by rw [isJal]; rfl) ok.x0
    · next dst base imm isJalr =>
      exact notX0_of_x0Ok _ dst (by rw [isJalr]; rfl) (by rw [isJalr]; rfl) ok.x0
    · trivial
  jumpAtSourceEnd := by
    split
    all_goals first
      | trivial
      | next isJump => exact ok.ends (by rw [isJump]; rfl)
  x0DestinationIsNoOp := by
    intro rd isDest isZero
    have x0 := ok.x0
    unfold x0Ok at x0
    simp only [isDest, isZero, Bool.not_true, Bool.false_or] at x0
    exact canonicalNoOp_of_isCanonicalNoOp _ x0
  branchAtSourceEnd := by
    split
    all_goals first
      | trivial
      | next isBranch => exact ok.ends (by rw [isBranch]; rfl)
  branchOffsetSmall := ok.branchOffset

theorem RowOk.nextPC_unchanged {row : JoltInstructionRow} (ok : RowOk row)
    (continues : row.continues = true) (advice : row.instruction.RuntimeAdvice)
    (preState postState : SailJoltState)
    (runs : JoltISA.execInstr (row.instruction.withRuntimeAdvice advice) preState =
      .ok (.Retire_Success ()) postState) :
    postState.sail.regs.get? Register.nextPC = preState.sail.regs.get? Register.nextPC :=
  nextPC_unchanged_of_ordinary _ preState postState
    (ordinary_withRuntimeAdvice _ advice (ok.ordinaryIfContinues continues)) runs

-- Row k of a checked sequence is a checked row, and ordinary unless it is the last.
theorem rowsOk_rows : ∀ (instructions : List JoltISA.Instr),
    rowsOk instructions = true → ∀ (k : Nat) (inRange : k < instructions.length),
      sequenceRowOk instructions[k] = true ∧
        (k + 1 < instructions.length → ordinary instructions[k] = true)
  | [], _, _, inRange => absurd inRange (Nat.not_lt_zero _)
  | [last], ok, 0, _ => ⟨ok, fun later => absurd later (by simp)⟩
  | [_], _, _ + 1, inRange => absurd inRange (by simp)
  | row :: next :: rest, ok, 0, _ => by
    have unfolded : rowsOk (row :: next :: rest) =
        (sequenceRowOk row && ordinary row && rowsOk (next :: rest)) := rfl
    simp only [unfolded, Bool.and_eq_true] at ok
    exact ⟨ok.1.1, fun _ => ok.1.2⟩
  | row :: next :: rest, ok, k + 1, inRange => by
    have unfolded : rowsOk (row :: next :: rest) =
        (sequenceRowOk row && ordinary row && rowsOk (next :: rest)) := rfl
    simp only [unfolded, Bool.and_eq_true] at ok
    simp only [List.length_cons] at inRange
    have later := rowsOk_rows (next :: rest) ok.2 k (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ, List.length_cons]
    exact ⟨later.1, fun more => later.2 (by simp only [List.length_cons]; omega)⟩

-- In a checked pair list each row's immediate mask is a bitmask, and a register
-- shift reads the mask the row before it writes.
theorem shiftPairsOk_rows : ∀ (previous : JoltISA.Instr) (rest : List JoltISA.Instr),
    shiftPairsOk previous rest = true → ∀ (k : Nat) (inRange : k < rest.length),
      immShiftOk rest[k] = true ∧
        (isRegisterShift rest[k] = true →
          masksFed ((previous :: rest)[k]'(by simp only [List.length_cons]; omega)) rest[k] =
            true)
  | _, [], _, _, inRange => absurd inRange (Nat.not_lt_zero _)
  | previous, current :: rest, ok, 0, _ => by
    simp only [shiftPairsOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at ok
    refine ⟨ok.1.1, fun isShift => ?_⟩
    rcases ok.1.2 with notShift | fed
    · rw [List.getElem_cons_zero, notShift] at isShift
      cases isShift
    · exact fed
  | _, current :: rest, ok, k + 1, inRange => by
    simp only [shiftPairsOk, Bool.and_eq_true] at ok
    exact shiftPairsOk_rows current rest ok.2 k
      (by simp only [List.length_cons] at inRange; omega)

theorem shiftsOk_rows (instructions : List JoltISA.Instr) (ok : shiftsOk instructions = true)
    (k : Nat) (inRange : k < instructions.length) :
    immShiftOk instructions[k] = true ∧
      (isRegisterShift instructions[k] = true →
        ∃ j, ∃ before : j + 1 = k,
          masksFed (instructions[j]'(by omega)) instructions[k] = true) := by
  cases instructions with
  | nil => exact absurd inRange (Nat.not_lt_zero _)
  | cons first rest =>
    simp only [shiftsOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ok
    cases k with
    | zero =>
      refine ⟨ok.1.1, fun isShift => ?_⟩
      rw [List.getElem_cons_zero, ok.1.2] at isShift
      cases isShift
    | succ j =>
      have pair := shiftPairsOk_rows first rest ok.2 j
        (by simp only [List.length_cons] at inRange; omega)
      exact ⟨pair.1, fun isShift => ⟨j, rfl, pair.2 isShift⟩⟩

theorem sequenceRow_rowOk (instruction : JoltISA.Instr)
    (ok : sequenceRowOk instruction = true) :
    x0Ok instruction = true ∧
      JoltRegisterEncoding.instructionIsCanonical instruction = true ∧
      BranchOffsetOk instruction := by
  simp only [sequenceRowOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ok
  exact ⟨ok.1.1, ok.2, branchOffsetOk_of_not_branch _ ok.1.2⟩

theorem stamp_sequence_rowOk (address : BitVec 64) (isCompressed : Bool)
    (instructions : List JoltISA.Instr) (ok : sequenceOk instructions = true) :
    ∀ row ∈ stamp_sequence address isCompressed instructions, RowOk row := by
  intro row isRow
  obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp isRow
  have inInstructions : k < instructions.length := by
    simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using inRange
  simp only [sequenceOk, Bool.and_eq_true] at ok
  obtain ⟨rowOk, notLast⟩ := rowsOk_rows instructions ok.1 k inInstructions
  obtain ⟨x0, canonical, branchOffset⟩ := sequenceRow_rowOk _ rowOk
  simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  refine ⟨x0, canonical, branchOffset, ?_, (shiftsOk_rows instructions ok.2 k inInstructions).1⟩
  intro continues
  apply notLast
  by_contra last
  have zero : instructions.length - k - 1 = 0 := by omega
  simp [JoltInstructionRow.continues, zero] at continues

theorem expand_instruction_rowOk (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    ∀ row ∈ rows, RowOk row := by
  unfold expand_instruction at expanded
  split at expanded
  · cases expanded
  · rename_i instruction isNative
    cases expanded
    have ok := expand_ok _ _ isNative
    obtain ⟨nativeOk, branchOffset⟩ := ok
    simp only [nativeRowOk, Bool.and_eq_true] at nativeOk
    intro row isRow
    rw [List.mem_singleton] at isRow
    subst isRow
    refine ⟨nativeOk.1.1.1, nativeOk.1.1.2, branchOffset, ?_, nativeOk.1.2⟩
    intro continues
    simp [JoltInstructionRow.continues] at continues
  · split at expanded
    · cases expanded
    · rename_i instructions isSequence _
      cases expanded
      exact stamp_sequence_rowOk _ _ instructions (expand_ok _ _ isSequence)

theorem expand_program_rowOk (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ∀ row ∈ bytecode.toList, RowOk row := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none =>
    rw [mapped] at expanded
    cases expanded
  | some instructions =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    subst expanded
    intro row isRow
    rw [List.toList_toArray] at isRow
    obtain ⟨rows, inInstructions, inRows⟩ := List.mem_flatten.mp isRow
    obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp inInstructions
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ instructions mapped
    exact expand_instruction_rowOk _ _ (steps k (by omega) inRange) _ inRows

-- Each register shift row comes right after the row that writes its mask, inside the
-- same source instruction.
def ShiftPairs (rows : List JoltInstructionRow) : Prop :=
  ∀ (k : Nat) (inRange : k < rows.length), isRegisterShift rows[k].instruction = true →
    ∃ j, ∃ before : j + 1 = k,
      masksFed (rows[j]'(by omega)).instruction rows[k].instruction = true ∧
        rows[k].starts_source = false

theorem stamp_sequence_shiftPairs (address : BitVec 64) (isCompressed : Bool)
    (instructions : List JoltISA.Instr) (ok : shiftsOk instructions = true) :
    ShiftPairs (stamp_sequence address isCompressed instructions) := by
  intro k inRange isShift
  have inInstructions : k < instructions.length := by
    simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using inRange
  simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at isShift ⊢
  obtain ⟨j, before, fed⟩ := (shiftsOk_rows instructions ok k inInstructions).2 isShift
  subst before
  exact ⟨j, rfl, fed, by simp [JoltInstructionRow.starts_source]⟩

theorem expand_instruction_shiftPairs (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow) (expanded : expand_instruction source = some rows) :
    ShiftPairs rows := by
  unfold expand_instruction at expanded
  split at expanded
  · cases expanded
  · rename_i instruction isNative
    cases expanded
    obtain ⟨nativeOk, _⟩ := expand_ok _ _ isNative
    simp only [nativeRowOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at nativeOk
    intro k inRange isShift
    have zero : k = 0 := by simpa using inRange
    subst zero
    simp [nativeOk.2] at isShift
  · split at expanded
    · cases expanded
    · rename_i instructions isSequence _
      cases expanded
      have ok : sequenceOk instructions = true := expand_ok _ _ isSequence
      simp only [sequenceOk, Bool.and_eq_true] at ok
      exact stamp_sequence_shiftPairs _ _ instructions ok.2

theorem shiftPairs_append (front back : List JoltInstructionRow) (frontOk : ShiftPairs front)
    (backOk : ShiftPairs back) : ShiftPairs (front ++ back) := by
  intro k inRange isShift
  rw [List.length_append] at inRange
  by_cases inFront : k < front.length
  · rw [List.getElem_append_left inFront] at isShift
    obtain ⟨j, before, fed, notStart⟩ := frontOk k inFront isShift
    refine ⟨j, before, ?_, ?_⟩
    · rw [List.getElem_append_left (by omega), List.getElem_append_left inFront]
      exact fed
    · rw [List.getElem_append_left inFront]
      exact notStart
  · rw [List.getElem_append_right (by omega)] at isShift
    obtain ⟨j, before, fed, notStart⟩ := backOk (k - front.length) (by omega) isShift
    refine ⟨front.length + j, by omega, ?_, ?_⟩
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using fed
    · rw [List.getElem_append_right (by omega)]
      exact notStart

theorem flatten_shiftPairs : ∀ (instructions : List (List JoltInstructionRow)),
    (∀ rows ∈ instructions, ShiftPairs rows) → ShiftPairs instructions.flatten
  | [], _ => fun _ inRange => absurd inRange (by simp)
  | rows :: rest, each => by
    rw [List.flatten_cons]
    exact shiftPairs_append _ _ (each rows List.mem_cons_self)
      (flatten_shiftPairs rest (fun later member => each later (List.mem_cons_of_mem _ member)))

theorem expand_program_shiftPairs (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ShiftPairs bytecode.toList := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none =>
    rw [mapped] at expanded
    cases expanded
  | some instructions =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    subst expanded
    rw [List.toList_toArray]
    apply flatten_shiftPairs
    intro rows inInstructions
    obtain ⟨k, inRange, rfl⟩ := List.mem_iff_getElem.mp inInstructions
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ instructions mapped
    exact expand_instruction_shiftPairs _ _ (steps k (by omega) inRange)

end ExpansionRows

-- Every row Rust's expansions emit is valid: these are facts about the instructions
-- in SourceInstruction.expand (expansions.lean), checked in expansion_facts.lean.
-- See : jolt/crates/jolt-program/src/expand/
theorem expand_program_rows_valid (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    ExpansionRowsValid bytecode :=
  have rowOk (i : Fin bytecode.size) : ExpansionRows.RowOk bytecode[i] :=
    ExpansionRows.expand_program_rowOk image bytecode expanded _ (Array.getElem_mem_toList _)
  { rowValid := fun i => (rowOk i).valid
    noEarlyNextPCChange := fun i => (rowOk i).nextPC_unchanged
    registerOperandsCanonical := fun i => (rowOk i).canonical }

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

-- Every immediate shift in an honest trace's bytecode has a right-shift bitmask, and
-- there are no rotates.
theorem HonestTrace.immShiftOk {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.bytecode.size) :
    ExpansionFacts.immShiftOk trace.bytecode[i].instruction = true :=
  (ExpansionRows.expand_program_rowOk _ _ trace.expands _ (Array.getElem_mem_toList _)).immShift

-- A register shift row comes right after the row that writes its mask, in the same
-- source instruction.
theorem HonestTrace.shiftPairs {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Fin trace.bytecode.size)
    (isShift : ExpansionFacts.isRegisterShift trace.bytecode[i].instruction = true) :
    ∃ j : Fin trace.bytecode.size, j.val + 1 = i.val ∧
      ExpansionFacts.masksFed trace.bytecode[j].instruction trace.bytecode[i].instruction =
        true ∧
      trace.bytecode[i].starts_source = false := by
  obtain ⟨j, before, fed, notStart⟩ := ExpansionRows.expand_program_shiftPairs _ _
    trace.expands i.val (by simp) (by simpa using isShift)
  exact ⟨⟨j, by omega⟩, before, by simpa using fed, by simpa using notStart⟩

-- A row that does not start its instruction runs right after the previous bytecode
-- row, from the state that row left.
theorem HonestTrace.previous_row {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (inBounds : n < trace.rows.size)
    (notStart : trace.bytecode[trace.rows[n].rowIndex].starts_source = false) :
    ∃ m, ∃ before : m + 1 = n,
      trace.rows[m].rowIndex.val + 1 = trace.rows[n].rowIndex.val ∧
        trace.rows[n].preState = trace.rows[m].postState := by
  cases n with
  | zero =>
    have first := (trace.starts trace.rows[0] (Array.getElem?_eq_getElem inBounds)).2.1
    rw [notStart] at first
    cases first
  | succ m =>
    have link := trace.linked m trace.rows[m] trace.rows[m + 1]
      (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem inBounds)
    split at link
    · exact ⟨m, rfl, link.1.symm, link.2⟩
    · obtain ⟨_, _, _, starts, _⟩ := link
      rw [notStart] at starts
      cases starts
