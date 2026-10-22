import JoltConstraints.Soundness.Layer6.PrefixState
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

/-- The twelve row kinds used by the eight division expansions.
This excludes memory accesses, tape loads, branches, jumps and HostIO.
For example, REM's VirtualAdvice, VirtualNegateIf, multiplication, subtraction
and assertion rows all satisfy this predicate. -/
def DivisionArithmeticRow : Instr → Prop
  | .VirtualAdvice .. | .VirtualNegateIf .. | .XOR .. | .MUL .. | .SUB .. | .ADDI ..
  | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
  | .VirtualAssertValidDiv0 .. | .VirtualAssertMulUNoOverflow ..
  | .VirtualAssertLTE .. | .VirtualAssertValidUnsignedRemainder .. => True
  | _ => False

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

/-- Execute one arithmetic advice sequence using the witness's advice word.
The conclusion retains the old run, the complete expansion invariant, and an
actual `Program.Run` certificate from the prepared starting state to the new
final state; it makes no honesty claim about the new advice.
The sequence is generic over the twelve row kinds in `DivisionArithmeticRow`.
Its row proofs must use `RegisterAgreementOn (ExpansionLive ... done)`, with
operand liveness from `shape.temporaries`; newly written temporaries become
live until the completed boundary drops them.
For example, REM with witness quotient 5 runs to a state agreeing outside
temporaries even though the honest quotient is 0.
Port `addi_step`, `arithmetic_step`, `xor_step`, `virtualBinary_step`,
`unaryWord_step`, `binaryAssertion_step`, `mulAssertion_step`, and
`assertLTE_step` to live-register agreement, and supply the missing
VirtualAdvice row step; compose with `Program.Run` and the existing bytecode
progress lemmas, including the exclusion of a truncated interior sequence. -/
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
  sorry

/-- Any successful generated division run has the architectural Sail result.
Use the existing `*Program_sound` results; for DIV, DIVU and DIVW combine their
advice uniqueness with `*Program_concrete` and deterministic execution.
Register presence supplies the successful source reads those theorems require.
For example, REM of 7 by zero ends with destination 7 even when `q = 5`. -/
theorem division_program_result (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (q : BitVec 64) (pre post : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (runs : Program.Run (kind.program rd rs1 rs2 q) pre post) :
    post.sail = stateAfterWrite pre.sail rd
      (kind.result (sourceValue (.xreg rs1) pre) (sourceValue (.xreg rs2) pre)) := by
  sorry

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

/-- Construct the honest generated run from the same prepared state, using
`*Program_concrete`, and compare its final state with the witness-advice run.
The supplied Sail result is step 3; the remaining equalities require frames
for this arithmetic-only program, including virtual registers outside 40–47.
Use `StatePreservation.Preserves` for those frames; the general device-setup
frame alone does not establish equality of every device field.
For example, REM of 7 by zero with witness quotient 5 is replaced by quotient
0, preserving destination 7, PC, RAM, device, tape and persistent registers. -/
theorem division_program_honest (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (q : BitVec 64) (pre witnessPost : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (runs : Program.Run (kind.program rd rs1 rs2 q) pre witnessPost)
    (result : witnessPost.sail = stateAfterWrite pre.sail rd
      (kind.result (sourceValue (.xreg rs1) pre) (sourceValue (.xreg rs2) pre))) :
    ∃ honestPost : SailJoltState,
      Program.Run (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost ∧
      DivisionFinalAgreement witnessPost honestPost := by
  sorry

/-- Split the certified honest program run into rows and append them to the
original prefix, transferring the candidate's represented observations and
completed expansion invariant.
Only persistent operands are compared inside the block; division programs
write their architectural destination last, and both executions share the
prepared start and their final state outside temporaries.
The source lookup identifies the honest advice at every appended row, and
retaining the old rows preserves their honest-advice values.
For example, the new nine REM rows carry quotient 0 instead of 5 while their
PCs, RAM addresses and non-temporary operands still match the witness. -/
theorem division_append_honest {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run candidate : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx) (placeholder : BitVec 64)
    (nonzero : rd ≠ .Regidx 0)
    (source : joltInstance.program.instructionAt context.bytecode[first].address =
      some (kind.source rd rs1 rs2 placeholder))
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (extendsRun : RunExtends run candidate)
    (size : candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first)
    (complete : ExpansionState witness context candidate first
      (expansionRowCount context.bytecode first))
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost)
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧
      run'.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context run' first (expansionRowCount context.bytecode first) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  sorry

/-- Append an entire advice-bearing division expansion, using honest advice in
the returned run and restoring agreement outside instruction temporaries.
The input is before the expansion, so a later proof may separately execute
witness advice, apply the matching division soundness theorem, and construct
honest rows using its concrete-execution theorem.
For example, REM with divisor zero may use witness quotient 5 while the returned
nine rows use quotient 0 and still produce the same architectural result.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) at 5def437f. -/
theorem division_block {F : Type} [Field F] (joltField : JoltField F)
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
    (hasAdvice : ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧
      run'.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context run' first (expansionRowCount context.bytecode first) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
  obtain ⟨kind, rd, rs1, rs2, placeholder, nonzero, source, count, shape⟩ :=
    division_expansion_layout joltInstance.program context.bytecode context.expands
      ⟨slots, preprocessed⟩ first state.starts hasAdvice
  obtain ⟨q, pre, candidate, entry, present, extendsRun, size, complete, runs⟩ :=
    arithmetic_advice_sequence_run joltField witness context equations run first state
      honestAdvice (kind.program rd rs1 rs2) count shape
  have result := division_program_result kind rd rs1 rs2 nonzero q pre
    (TraceWitness.finalTraceState candidate.toTrace) present runs
  obtain ⟨honestPost, honestRun, same⟩ := division_program_honest kind rd rs1 rs2 nonzero
    q pre (TraceWitness.finalTraceState candidate.toTrace) present runs result
  exact division_append_honest witness context run candidate first state kind rd rs1 rs2
    placeholder nonzero source count shape pre honestPost entry extendsRun size complete
    honestRun same

end JoltInstance
