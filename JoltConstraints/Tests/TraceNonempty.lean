import JoltConstraints.execution_conditions
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas

set_option autoImplicit false

/-! A concrete one-row trace: source `jal x0, 0` at the RAM start, run from
`init_state`. It checks that the `JoltTrace` premises are satisfiable, so the
constraint theorems quantified over traces are not vacuous. Rust stops this
program after one row because the jump leaves PC at its own address. -/

namespace TraceNonemptyChecks

open JoltISA LeanRV64D.Functions

/-- Every architectural register is readable when every Sail register is present. -/
theorem xRegReadable_of_present {s : SailState} (v : (r : Register) → RegisterType r)
    (hv : ∀ r, s.regs.get? r = some (v r)) (r : regidx) :
    Assumptions.XRegReadable r s := by
  refine ⟨?_⟩
  obtain ⟨i⟩ := r
  unfold rX_bits rX regval_from_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind, pure, EStateM.pure]
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp only [h]
    exact ⟨_, rfl⟩
  all_goals
    simp only [h]
    rw [readReg_eq_of_get? _ s _ (hv _)]
    exact ⟨_, rfl⟩

section

variable (io : JoltDevice) (tape : JoltAdviceTape)

def jalRow : JoltProgramRow :=
  { inputInstruction := .JAL (.xreg (.Regidx 0)) 0
    registerOperandsCanonical := by decide
    isBytecodeTemplate := True.intro
    address := 0x80000000
    virtualSequenceRemaining := none
    isFirstInSequence := false
    isCompressed := false }

noncomputable def jalProgram : JoltProgram :=
  { expandedBytecode := #[jalRow]
    initialState := init_state 0x80000000 #[] io tape }

def firstRow : Fin (jalProgram io tape).expandedBytecode.size := ⟨0, Nat.one_pos⟩

theorem eq_firstRow (i : Fin (jalProgram io tape).expandedBytecode.size) :
    i = firstRow io tape :=
  Fin.ext (Nat.lt_one_iff.mp i.isLt)

-- Rust rewrites the `x0` destination of a native JAL to the first inline temporary.
theorem firstRow_instruction :
    (jalProgram io tape).expandedBytecode[firstRow io tape].expandedInstruction =
      .JAL (.vreg rdZeroRewriteVReg) 0 :=
  rfl

theorem jalLayout : (jalProgram io tape).SequenceLayout where
  endInBounds i := by
    obtain rfl := eq_firstRow io tape i
    exact Nat.one_pos
  addressAdvanceNoWrap i := by
    obtain rfl := eq_firstRow io tape i
    simp [jalProgram, jalRow, firstRow]
  ordinary i _ := by
    obtain rfl := eq_firstRow io tape i
    rfl
  firstEntry _ := Or.inl rfl
  afterEnd i j hj _ := by
    obtain rfl := eq_firstRow io tape i
    obtain rfl := eq_firstRow io tape j
    simp [firstRow] at hj
  next i j hj _ := by
    obtain rfl := eq_firstRow io tape i
    obtain rfl := eq_firstRow io tape j
    simp [firstRow] at hj
  addressSequenceUnique i j _ _ := by
    rw [eq_firstRow io tape i, eq_firstRow io tape j]

noncomputable def jalPre : SailJoltState :=
  (jalProgram io tape).prepareSource (jalLayout io tape) (firstRow io tape)
    (jalProgram io tape).initialState

theorem jalPre_get?_of_ne (r : Register) (hPC : r ≠ Register.PC)
    (hnext : r ≠ Register.nextPC) :
    (jalPre io tape).sail.regs.get? r =
      (init_state 0x80000000 #[] io tape).sail.regs.get? r := by
  simp [jalPre, JoltProgram.prepareSource, jalProgram, Std.ExtDHashMap.get?_insert,
    Ne.symm hPC, Ne.symm hnext]

theorem jalPre_nextPC :
    (jalPre io tape).sail.regs.get? Register.nextPC = some 0x80000004 := by
  simp [jalPre, JoltProgram.prepareSource, JoltProgram.sourceLength, jalProgram, jalRow,
    firstRow]

theorem jalPre_PC :
    (jalPre io tape).sail.regs.get? Register.PC = some 0x80000000 := by
  simp [jalPre, JoltProgram.prepareSource, jalProgram, jalRow, firstRow,
    Std.ExtDHashMap.get?_insert]

theorem jalPre_present (r : Register) :
    ∃ v, (jalPre io tape).sail.regs.get? r = some v := by
  by_cases hPC : r = Register.PC
  · subst hPC
    exact ⟨_, jalPre_PC io tape⟩
  by_cases hnext : r = Register.nextPC
  · subst hnext
    exact ⟨_, jalPre_nextPC io tape⟩
  rw [jalPre_get?_of_ne io tape r hPC hnext, init_state_register]
  exact ⟨_, rfl⟩

theorem jalPre_assumptions : TraceAssumptions (jalPre io tape) where
  xRegReadable :=
    xRegReadable_of_present (fun r => (jalPre_present io tape r).choose)
      (fun r => (jalPre_present io tape r).choose_spec)

/-- No memory windows: the row does not access RAM. -/
def noOperands : AssumptionOperands :=
  { memoryWindows := fun _ => False
    mtvecWrites := fun _ => False
    mepcReads := fun _ => False
    mepcWrites := fun _ => False
    mstatusWrites := fun _ _ => False }

/-- The source-equivalence bundle `all_assumptions` fails at this pre-state.
Its `MstatusMppMachine` conjunct needs MPP = Machine in the virtual `mstatus`
register, which `init_state` zeroes as Rust's `Cpu::new` does. Requiring that
bundle on trace rows made every `JoltTrace` empty. -/
example : ¬ all_assumptions (jalPre io tape) noOperands := by
  intro h
  have hmpp : Assumptions.MstatusMppMachine (jalPre io tape) :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hzero : (jalPre io tape).vregs mstatusVReg = 0 := rfl
  have := hmpp.value_eq
  rw [hzero] at this
  revert this
  decide

noncomputable def jalPost : SailJoltState :=
  let pre := jalPre io tape
  { pre with
    vregs := fun r => if r = rdZeroRewriteVReg then 0x80000004 else pre.vregs r
    sail := { pre.sail with regs := pre.sail.regs.insert Register.nextPC 0x80000000 } }

theorem jal_executes :
    execInstr (.JAL (.vreg rdZeroRewriteVReg) 0) (jalPre io tape) =
      .ok (.Retire_Success ()) (jalPost io tape) := by
  have hnext : liftSail (Sail.readReg Register.nextPC) (jalPre io tape) =
      .ok 0x80000004 (jalPre io tape) := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC _ _ (jalPre_nextPC io tape)]
  have hpc : liftSail (Sail.readReg Register.PC) (jalPre io tape) =
      .ok 0x80000000 (jalPre io tape) := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC _ _ (jalPre_PC io tape)]
  simp only [execInstr, bind, EStateM.bind, hnext, hpc]
  rfl

noncomputable def jalTraceRow : JoltTraceRow (jalProgram io tape) where
  rowIndex := firstRow io tape
  validProgramRow :=
    { jumpDestinationWritable := by
        rw [firstRow_instruction]
        trivial
      jumpAtSourceEnd := by
        rw [firstRow_instruction]
        rfl
      x0DestinationIsNoOp := by
        intro rd h
        rw [firstRow_instruction] at h
        simp [Instr.destination?] at h }
  runtimeAdvice := ()
  preState := jalPre io tape
  postState := jalPost io tape
  executes := jal_executes io tape
  storeMemoryPresent := True.intro

noncomputable def jalTrace : JoltTrace (jalProgram io tape) where
  rows := #[jalTraceRow io tape]
  rowAssumptions i := by
    obtain rfl : i = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    exact jalPre_assumptions io tape
  sequenceLayout := jalLayout io tape
  initialized := ⟨_, _, _, _, _, rfl⟩
  noEarlyNextPCChange i hcontinues := by
    obtain rfl := eq_firstRow io tape i
    exact (Bool.false_ne_true hcontinues).elim
  startsAtEntry _ := ⟨Or.inl rfl, init_state_register _ _ _ _ _ _⟩
  startsAtInitial _ := rfl
  linked i _ nextExists := by
    exfalso
    simp at nextExists
  successor i _ nextExists := by
    exfalso
    simp at nextExists

/-- The trace is a complete Rust run: one row, ending where it started. -/
theorem jalTrace_terminated : (jalTrace io tape).Terminated where
  nonempty := Nat.one_pos
  atSourceEnd := rfl
  repeatedPC := by
    show (jalPost io tape).sail.regs.get? Register.nextPC = some 0x80000000
    simp [jalPost]

end

-- No `sorryAx`: the row and trace supply `validProgramRow` and
-- `noEarlyNextPCChange` instead of the `sorry` defaults. The Sail axioms come
-- from `execInstr`, as in the constraint theorems.
/--
info: 'TraceNonemptyChecks.jalTrace_terminated' depends on axioms: [propext,
 sys_enable_experimental_extensions,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms jalTrace_terminated

end TraceNonemptyChecks
