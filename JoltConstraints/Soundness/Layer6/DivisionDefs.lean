import JoltConstraints.Soundness.Layer6.PlainRow
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

/-! Staged reconstruction of a whole division expansion with honest advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- The eight source operations implemented by division expansions.
For example, `rem` selects the nine-row signed remainder program even when
the divisor is zero and its quotient advice is not unique. -/
inductive DivisionKind where
  | div | divu | divw | divuw | rem | remu | remw | remuw

/-- The source instruction with architectural destination `rd`, dividend `rs1`,
divisor `rs2`, and bytecode advice placeholder `q`.
For example, `rem.source a0 a1 zero 5` describes the REM source whose runtime
advice will later be replaced independently of the placeholder. -/
def DivisionKind.source (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) : SourceInstruction :=
  .riscv (match kind with
    | .div => .DIV rd rs1 rs2 q
    | .divu => .DIVU rd rs1 rs2 q
    | .divw => .DIVW rd rs1 rs2 q
    | .divuw => .DIVUW rd rs1 rs2 q
    | .rem => .REM rd rs1 rs2 q
    | .remu => .REMU rd rs1 rs2 q
    | .remw => .REMW rd rs1 rs2 q
    | .remuw => .REMUW rd rs1 rs2 q)

/-- The generated program for a division kind, using runtime advice `q`.
For example, `rem.program a0 a1 zero 5` is the same generated REM program
used by `remProgram_sound`, with quotient magnitude 5. -/
def DivisionKind.program (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) : Program :=
  match kind with
  | .div => divProgramAuto rd rs1 rs2 q
  | .divu => divuProgramAuto rd rs1 rs2 q
  | .divw => divwProgramAuto rd rs1 rs2 q
  | .divuw => divuwProgramAuto rd rs1 rs2 q
  | .rem => remProgramAuto rd rs1 rs2 q
  | .remu => remuProgramAuto rd rs1 rs2 q
  | .remw => remwProgramAuto rd rs1 rs2 q
  | .remuw => remuwProgramAuto rd rs1 rs2 q

/-- The architectural result for dividend `lhs` and divisor `rhs`, including
RV64 word sign extension and division-by-zero conventions.
For example, `rem.result 7 0 = 7`, independently of quotient advice. -/
def DivisionKind.result (kind : DivisionKind) (lhs rhs : BitVec 64) : BitVec 64 :=
  match kind with
  | .div => sail_div_value lhs rhs false
  | .divu => sail_div_value lhs rhs true
  | .divw => sail_divw_value lhs rhs false
  | .divuw => sail_divw_value lhs rhs true
  | .rem => sail_rem_value lhs rhs false
  | .remu => sail_rem_value lhs rhs true
  | .remw => sail_remw_value lhs rhs false
  | .remuw => sail_remw_value lhs rhs true

/-- Read the single honest advice word from the existing tracer-advice definition.
The placeholder zero is irrelevant to that definition.
For example, REM with divisor zero gets quotient magnitude zero.
See jolt/tracer/src/instruction/rem.rs (`RISCVTrace::trace`) at 5def437f. -/
def DivisionKind.honestAdvice (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (pre : SailJoltState) : BitVec 64 :=
  ((kind.source rd rs1 rs2 0).honestTracerAdvice pre).headD 0

/-- The instruction list in the stamped expansion starting at `first`.
For example, a nonzero-destination REM contributes its nine instructions,
including the bytecode's placeholder VirtualAdvice instruction. -/
def expansionInstructions (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) : List Instr :=
  ((bytecode.extract first.val
    (first.val + expansionRowCount bytecode first)).toList).map (·.instruction)

/-- Replace a VirtualAdvice value by `q`, leaving every other instruction alone.
This is the instruction-list form of `Instr.withRuntimeAdvice`.
For example, replacing REM's placeholder with 5 leaves its MUL row unchanged. -/
def patchAdviceWord (q : BitVec 64) : Instr → Instr
  | .VirtualAdvice dst _ imm => .VirtualAdvice dst q imm
  | instruction => instruction

/-- A straight-line family obtained by patching the one advice row in `rows`.
Every row has a division arithmetic kind and every instruction temporary is
written before its first read; no incoming temporary value is required.
For example, the nine REM rows form this family with either quotient 5 or 0.
The final `Program.seq` result is successful retirement, not an arbitrary
`Program.done` result. -/
structure ArithmeticAdviceSequence (rows : List Instr)
    (program : BitVec 64 → Program) : Prop where
  program_eq : ∀ q, program q = Program.seq (rows.map (patchAdviceWord q))
  singleAdvice : (rows.filter (fun row => row.adviceValue?.isSome)).length = 1
  arithmetic : ∀ row ∈ rows, DivisionArithmeticRow row
  temporaries : ExpansionTempLiveness.tempsReadAfterWrite rows = true

/-- Identify an advice-bearing source and its generated instruction family.
Successful preprocessing supplies address uniqueness for `instructionAt`;
`starts` and the expansion certificate locate the whole source, not merely
an arbitrary row with the same address.
For example, the first REM row identifies a nonzero destination and all nine
generated rows, irrespective of the bytecode's advice placeholder.
See jolt/crates/jolt-program/src/expand/mod.rs
(`expand_source_instruction_with_provider`) and division/rem.rs (`expand_rem`)
at 5def437f. -/
theorem division_expansion_layout
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (preprocessed : ∃ slots, preprocess bytecode = some slots)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (hasAdvice : ExpansionHasAdvice bytecode first) :
    ∃ (kind : DivisionKind) (rd rs1 rs2 : regidx) (placeholder : BitVec 64),
      rd ≠ .Regidx 0 ∧
      image.instructionAt bytecode[first].address =
        some (kind.source rd rs1 rs2 placeholder) ∧
      (expansionInstructions bytecode first).length = expansionRowCount bytecode first ∧
      ArithmeticAdviceSequence (expansionInstructions bytecode first)
        (kind.program rd rs1 rs2) := by
  sorry

/-- The word encoded by a witness write at a natural-number cycle, or zero
if the cycle is absent or its field value encodes no word.
For example, a range-checked advice write of 5 returns the word 5. -/
private noncomputable def witnessWord {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (cycle : Nat) : BitVec 64 := by
  classical
  exact if bound : cycle < params.traceLength then
    if encoded : ∃ value : BitVec 64, witness.RdWriteValue ⟨cycle, bound⟩ = (value.toNat : F)
    then encoded.choose else 0
  else 0

private theorem witnessWord_of_encoded {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    (cycle : Fin params.traceLength) (value : BitVec 64)
    (encoded : witness.RdWriteValue cycle = (value.toNat : F)) :
    witnessWord witness cycle.val = value := by
  unfold witnessWord
  rw [dif_pos cycle.isLt, dif_pos ⟨value, encoded⟩]
  apply BitVec.eq_of_toNat_eq
  apply natCast_injective_below_char (F := F)
  · have bound := two_pow_64_lt_char (two_pow_127_lt_char joltField)
    exact Nat.lt_trans (BitVec.isLt _) bound
  · exact Nat.lt_trans value.isLt (two_pow_64_lt_char (two_pow_127_lt_char joltField))
  · exact (Exists.choose_spec (show ∃ v : BitVec 64,
        witness.RdWriteValue cycle = (v.toNat : F) from ⟨value, encoded⟩)).symm.trans encoded

/-- A sequence with one advice-bearing instruction has a unique index for it.
For example, the VirtualAdvice instruction in REM's expansion is the sole index. -/
theorem single_advice_index (rows : List Instr)
    (single : (rows.filter fun row => row.adviceValue?.isSome).length = 1) :
    ∃ (index : Nat) (bound : index < rows.length), rows[index].adviceValue?.isSome = true ∧
      ∀ (other : Nat) (inRows : other < rows.length),
        rows[other].adviceValue?.isSome = true → other = index := by
  induction rows with
  | nil => simp at single
  | cons row rest ih =>
    by_cases advice : row.adviceValue?.isSome = true
    · have empty : (rest.filter fun row => row.adviceValue?.isSome) = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.filter_cons, advice, ↓reduceIte, List.length_cons] at single
        omega
      refine ⟨0, by simp, advice, ?_⟩
      intro other inRows present
      cases other with
      | zero => rfl
      | succ other =>
        have member := List.getElem_mem (l := rest) (n := other) (by simpa using inRows)
        have absent := List.filter_eq_nil_iff.mp empty _ member
        exact False.elim (absent present)
    · have remaining : (rest.filter fun row => row.adviceValue?.isSome).length = 1 := by
        simpa only [List.filter_cons, advice, ↓reduceIte] using single
      obtain ⟨index, bound, present, unique⟩ := ih remaining
      refine ⟨index + 1, by simp; omega, present, ?_⟩
      intro other inRows hasAdvice
      cases other with
      | zero => exact False.elim (advice hasAdvice)
      | succ other => exact congrArg (· + 1) (unique other (by simpa using inRows) hasAdvice)


/-- Runtime advice that records word `q` patches an instruction to the same
VirtualAdvice value as `patchAdviceWord`; a non-advice row stays unchanged.
For example, REM's VirtualAdvice with runtime quotient 5 becomes its 5-patched row. -/
theorem patchAdviceWord_runtime (instruction : Instr)
    (advice : instruction.RuntimeAdvice) (q : BitVec 64)
    (encoded : ∀ v ∈ (instruction.withRuntimeAdvice advice).adviceValue?, v = q) :
    instruction.withRuntimeAdvice advice = patchAdviceWord q instruction := by
  by_cases noAdvice : instruction.adviceValue? = none
  · rw [withRuntimeAdvice_eq_of_noAdvice instruction advice noAdvice]
    unfold patchAdviceWord
    split
    · cases noAdvice
    · rfl
  · have shape : ∃ destination placeholder imm, instruction = Instr.VirtualAdvice destination placeholder imm := by
      unfold Instr.adviceValue? at noAdvice
      split at noAdvice
      · exact ⟨_, _, _, rfl⟩
      · exact False.elim (noAdvice rfl)
    obtain ⟨destination, placeholder, imm, rfl⟩ := shape
    exact congrArg (fun value => Instr.VirtualAdvice destination value imm) (encoded advice rfl)

/-- Patching runtime advice preserves whether an instruction has an advice slot.
For example, REM's VirtualAdvice still has one slot, and its MUL still has none. -/
theorem runtime_advice_isSome (instruction : Instr) (advice : instruction.RuntimeAdvice) :
    (instruction.withRuntimeAdvice advice).adviceValue?.isSome = instruction.adviceValue?.isSome := by
  unfold Instr.withRuntimeAdvice
  split <;> rfl

/-- A division arithmetic row ignores the tape answer, so its relaxed execution
is its ordinary execution. For example, REM's MUL has the same result for tape
answers zero and five. -/
theorem arithmetic_exec_eq (instruction : Instr) (arithmetic : DivisionArithmeticRow instruction)
    (answer : BitVec 64) : execWithTapeAnswer instruction answer = execInstr instruction := by
  unfold execWithTapeAnswer
  split
  · exact False.elim arithmetic
  · rfl

/-- A row inside an expansion is the instruction at the same list offset.
For example, offset two of REM's bytecode expansion is its third program row. -/
theorem expansionInstructions_at (bytecode : Array JoltInstructionRow)
    (first : Fin bytecode.size) (offset : Nat)
    (inside : offset < expansionRowCount bytecode first)
    (count : (expansionInstructions bytecode first).length = expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + offset]? = some row) :
    (expansionInstructions bytecode first)[offset]'(by omega) = row.instruction := by
  unfold expansionInstructions
  simp only [List.getElem_map, Array.getElem_toList, Array.getElem_extract]
  have bound := (Array.getElem?_eq_some_iff.mp atRow).1
  have same := (Array.getElem?_eq_some_iff.mp atRow).2
  exact congrArg (·.instruction) same

private theorem arithmetic_advice_row_run {F : Type} [Field F] {params : WitnessParams}
    (joltField : JoltField F) (witness : WitnessType F params)
    (rows : List Instr) (adviceOffset : Nat)
    (unique : ∀ (offset : Nat) (inside : offset < rows.length),
      rows[offset].adviceValue?.isSome = true → offset = adviceOffset)
    (startCycle done : Nat) (inside : done < rows.length)
    (cycle : Fin params.traceLength) (position : cycle.val = startCycle + done)
    (bytecode : Array JoltInstructionRow) (step : TraceRow bytecode) (answer : BitVec 64)
    (atInstruction : rows[done] = bytecode[step.rowIndex].instruction)
    (arithmetic : DivisionArithmeticRow bytecode[step.rowIndex].instruction)
    (encoded : ∀ value ∈ step.someTracerAdvice?, witness.RdWriteValue cycle = (value.toNat : F))
    (executes : execWithTapeAnswer
      (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice) answer step.preState =
        .ok RETIRE_SUCCESS step.postState) :
    execInstr (patchAdviceWord (witnessWord witness (startCycle + adviceOffset)) rows[done]) step.preState =
      .ok RETIRE_SUCCESS step.postState := by
  let q := witnessWord witness (startCycle + adviceOffset)
  have adviceIs : ∀ v ∈ (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice).adviceValue?, v = q := by
    intro value hasValue
    have patchedSome : (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice).adviceValue?.isSome = true := by
      rw [show (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice).adviceValue? = some value from hasValue]
      rfl
    rw [runtime_advice_isSome] at patchedSome
    have originalSome : (rows[done]'inside).adviceValue?.isSome = true := by
      rw [atInstruction]
      exact patchedSome
    have advicePosition := unique done inside originalSome
    have word := witnessWord_of_encoded joltField witness cycle value (encoded value hasValue)
    simpa only [position, advicePosition] using word.symm
  have runtimeKind : DivisionArithmeticRow
      (bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice) := by
    unfold Instr.withRuntimeAdvice
    split
    · exact True.intro
    · exact arithmetic
  rw [arithmetic_exec_eq _ runtimeKind] at executes
  rw [patchAdviceWord_runtime _ step.runtimeAdvice q adviceIs] at executes
  simpa only [atInstruction] using executes

private theorem arithmetic_advice_suffix_run {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (first : Fin context.bytecode.size)
    (count : (expansionInstructions context.bytecode first).length = expansionRowCount context.bytecode first)
    (arithmetic : ∀ row ∈ expansionInstructions context.bytecode first, DivisionArithmeticRow row)
    (adviceOffset : Nat)
    (unique : ∀ (offset : Nat) (inside : offset < (expansionInstructions context.bytecode first).length),
      (expansionInstructions context.bytecode first)[offset].adviceValue?.isSome = true → offset = adviceOffset)
    (startCycle done : Nat) (run : UntrustedAnswerRun joltInstance privateInputs)
    (state : ExpansionState witness context run first done)
    (position : run.rows.size = startCycle + done) :
    ∃ (pre : SailJoltState) (candidate : UntrustedAnswerRun joltInstance privateInputs),
      (done < expansionRowCount context.bytecode first →
        ∃ next : Fin run.bytecode.size, next.val = first.val + done ∧
          RawRowEntry run next pre ∧ AllRegistersPresent pre.sail) ∧
      (done = expansionRowCount context.bytecode first → pre = TraceWitness.finalTraceState run.toTrace) ∧
      RunExtends run candidate ∧
      candidate.rows.size = run.rows.size + (expansionRowCount context.bytecode first - done) ∧
      ExpansionState witness context candidate first (expansionRowCount context.bytecode first) ∧
      Program.Run (Program.seq (((expansionInstructions context.bytecode first).drop done).map
        (patchAdviceWord (witnessWord witness (startCycle + adviceOffset)))))
        pre (TraceWitness.finalTraceState candidate.toTrace) := by
  generalize left : expansionRowCount context.bytecode first - done = remaining
  induction remaining generalizing done run with
  | zero =>
    have done_le := state.done_le
    have completed : done = expansionRowCount context.bytecode first := by omega
    subst done
    refine ⟨TraceWitness.finalTraceState run.toTrace, run, ?_, fun _ => rfl,
      RunExtends.refl run, by omega, state, ?_⟩
    · intro impossible
      omega
    · rw [List.drop_eq_nil_of_le (by omega)]
      rfl
  | succ remaining ih =>
    have unfinished : done < expansionRowCount context.bytecode first := by omega
    obtain ⟨bound, _⟩ := state.next unfinished
    have rowArithmetic : ∀ row ∈ context.bytecode[first.val + done]?,
        DivisionArithmeticRow row.instruction := by
      intro row atRow
      have atInstruction := expansionInstructions_at context.bytecode first done unfinished count row atRow
      rw [← atInstruction]
      exact arithmetic _ (List.getElem_mem _)
    obtain ⟨step, answer, nextRun, indexIs, entry, present, traceEq, executes,
      encoded, _, _, extendsRun, size, after⟩ :=
      arithmetic_plain_row_step joltField witness context equations run first done state unfinished bound rowArithmetic
    obtain ⟨tailPre, candidate, tailEntry, tailComplete, extendsTail, tailSize, complete, tailRun⟩ :=
      ih (done + 1) nextRun after (by omega) (by omega)
    have finalNext : TraceWitness.finalTraceState nextRun.toTrace = step.postState :=
      (congrArg TraceWitness.finalTraceState traceEq).trans (finalTraceState_push run.toTrace step)
    have tailPreIs : tailPre = step.postState := by
      by_cases more : done + 1 < expansionRowCount context.bytecode first
      · obtain ⟨next, _, ready, _⟩ := tailEntry more
        exact (after.interior_pre (by omega) more next tailPre ready).trans finalNext
      · have full : done + 1 = expansionRowCount context.bytecode first := by
          have done_le := after.done_le
          omega
        exact (tailComplete full).trans finalNext
    have bytecodeEq : run.bytecode = context.bytecode :=
      Option.some.inj (run.expands.symm.trans context.expands)
    have atRow : context.bytecode[first.val + done]? = some run.bytecode[step.rowIndex] := by
      rw [← indexIs, ← bytecodeEq]
      simp only [Array.getElem?_eq_getElem step.rowIndex.isLt, Fin.getElem_fin]
    have atInstruction := expansionInstructions_at context.bytecode first done unfinished count _ atRow
    let q := witnessWord witness (startCycle + adviceOffset)
    have headRun := arithmetic_advice_row_run joltField witness _ adviceOffset unique startCycle done
      (by omega) ⟨run.rows.size, bound⟩ position run.bytecode step answer atInstruction
      (rowArithmetic _ atRow) encoded executes
    refine ⟨step.preState, candidate, fun _ => ⟨step.rowIndex, indexIs, entry, present⟩,
      ?_, extendsRun.trans extendsTail, by omega, complete, ?_⟩
    · intro impossible
      omega
    · rw [List.drop_eq_getElem_cons (by omega), List.map_cons]
      unfold Program.Run
      change (execProgram (.instr (patchAdviceWord q ((expansionInstructions context.bytecode first)[done]'(by omega)))
        (Program.seq (((expansionInstructions context.bytecode first).drop (done + 1)).map (patchAdviceWord q))))).run
          step.preState = .ok RETIRE_SUCCESS (TraceWitness.finalTraceState candidate.toTrace)
      rw [execProgram_instr_run_retire _ _ _ _ headRun]
      simpa only [tailPreIs] using tailRun

/-- Execute one arithmetic advice sequence using the witness's advice word.
The conclusion retains the old run, the complete expansion invariant, and an
actual `Program.Run` certificate from the prepared starting state to the new
final state; it makes no honesty claim about the new advice.
The sequence is generic over the twelve row kinds in `DivisionArithmeticRow`.
Its row proofs must use `RegisterAgreementOn (ExpansionLive ... done)`, with
operand liveness from the expanded bytecode's temporary-write certificate;
newly written temporaries become live until the completed boundary drops them.
For example, REM with witness quotient 5 runs to a state agreeing outside
temporaries even though the honest quotient is 0.
The proved arithmetic row step applies the live-register instruction families
and VirtualAdvice rule; the suffix induction composes their executions and
excludes a truncated interior sequence through the expansion invariant. -/
theorem arithmetic_advice_sequence_run {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (program : BitVec 64 → Program)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first) program) :
    ∃ (q : BitVec 64) (pre : SailJoltState)
      (candidate : UntrustedAnswerRun joltInstance privateInputs),
      (∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre) ∧
      AllRegistersPresent pre.sail ∧
      RunExtends run candidate ∧
      candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context candidate first (expansionRowCount context.bytecode first) ∧
      Program.Run (program q) pre (TraceWitness.finalTraceState candidate.toTrace) := by
  obtain ⟨adviceOffset, _, _, unique⟩ :=
    single_advice_index (expansionInstructions context.bytecode first) shape.singleAdvice
  obtain ⟨pre, candidate, entry, _, extendsRun, size, complete, runs⟩ :=
    arithmetic_advice_suffix_run joltField witness context equations first count shape.arithmetic
      adviceOffset unique run.rows.size 0 run state (by omega)
  obtain ⟨next, indexIs, ready, present⟩ := entry (Nat.zero_lt_succ _)
  refine ⟨witnessWord witness (run.rows.size + adviceOffset), pre, candidate,
    ⟨next, by simpa only [Nat.add_zero] using indexIs,
      ⟨honestAdvice, state.noEarlierStop, ready⟩⟩, present, extendsRun, ?_, complete, ?_⟩
  · simpa only [Nat.sub_zero] using size
  · rw [shape.program_eq]
    simpa only [List.drop_zero] using runs

/-- Two completed division states agree on every component except instruction
temporaries: Sail (including PC and RAM), device, tape, host settings, and all
other virtual registers are equal.
For example, REM may leave temporary 40 as 5 in one state and 0 in the other,
while both states have the same architectural remainder. -/
structure DivisionFinalAgreement (witnessPost honestPost : SailJoltState) : Prop where
  sail : honestPost.sail = witnessPost.sail
  device : honestPost.jolt_device = witnessPost.jolt_device
  tape : honestPost.adviceTape = witnessPost.adviceTape
  host : honestPost.hostIO = witnessPost.hostIO
  virtualRegisters : ∀ register : BitVec 7,
    ¬ IsInstructionTemporary register.toFin →
    honestPost.vregs register = witnessPost.vregs register

end JoltInstance
