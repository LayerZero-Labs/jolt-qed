import JoltConstraints.Soundness.Layer6.DivisionPrograms

/-! Identify the generated rows of an advice-bearing division source. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- Detect an internal VirtualAdvice row in an unstamped expansion.
For example, a sequence containing REM's advice row returns true. -/
private def expandedInternalAdvice : ExpandedSource → Bool
  | .native row => row.adviceValue?.isSome
  | .sequence rows => rows.any (·.adviceValue?.isSome)

/-- The source expansion contains an internal VirtualAdvice row.
For example, REM into x1 satisfies this predicate, whereas AdviceLD does not. -/
private def SourceInternalAdvice (source : SourceInstruction) : Prop :=
  source.expand.any expandedInternalAdvice = true

private theorem division_source_kind (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) (advice : SourceInternalAdvice (kind.source rd rs1 rs2 q)) :
    ∃ (kind' : DivisionKind) (rd' rs1' rs2' : regidx) (q' : BitVec 64),
      kind.source rd rs1 rs2 q = kind'.source rd' rs1' rs2' q' ∧ rd' ≠ .Regidx 0 := by
  refine ⟨kind, rd, rs1, rs2, q, rfl, ?_⟩
  intro zero
  subst rd
  cases kind <;> simp [SourceInternalAdvice, expandedInternalAdvice, DivisionKind.source,
    SourceInstruction.expand, ExpandedSource.ofPureProgram, isX0,
    Instr.canonicalNoOp, Instr.adviceValue?] at advice

private theorem source_advice_kind (source : SourceInstruction)
    (advice : SourceInternalAdvice source) :
    ∃ (kind : DivisionKind) (rd rs1 rs2 : regidx) (q : BitVec 64),
      source = kind.source rd rs1 rs2 q ∧ rd ≠ .Regidx 0 := by
  -- Classify source constructors once, keeping division programs symbolic.
  cases source <;> rename_i instruction <;> cases instruction
  case riscv.DIV => exact division_source_kind .div _ _ _ _ advice
  case riscv.DIVU => exact division_source_kind .divu _ _ _ _ advice
  case riscv.DIVW => exact division_source_kind .divw _ _ _ _ advice
  case riscv.DIVUW => exact division_source_kind .divuw _ _ _ _ advice
  case riscv.REM => exact division_source_kind .rem _ _ _ _ advice
  case riscv.REMU => exact division_source_kind .remu _ _ _ _ advice
  case riscv.REMW => exact division_source_kind .remw _ _ _ _ advice
  case riscv.REMUW => exact division_source_kind .remuw _ _ _ _ advice
  -- Move conditional choices through each observer before unfolding the observer.
  all_goals simp only [SourceInternalAdvice, SourceInstruction.expand, expandedInternalAdvice,
        ExpandedSource.ofNative, ExpandedSource.ofProgram, ExpandedSource.ofPureProgram,
        Instr.rewriteNative, Instr.destination?, Instr.canonicalNoOp, Program.instrs,
        Instr.adviceValue?, Option.any_some, Option.isSome_none, List.any_cons, List.any_nil,
        Bool.or_false, Bool.false_eq_true, ite_self,
        ↓apply_ite expandedInternalAdvice, ↓apply_ite Instr.adviceValue?, ↓apply_ite Program.instrs,
        ↓apply_ite (fun rows : List Instr => rows.any (·.adviceValue?.isSome)),
        Encoded.LD, Encoded.SD, Encoded.ADDI, Encoded.ADDIW, Encoded.AUIPC,
        Encoded.JAL, Encoded.JALR, Encoded.BEQ, Encoded.BNE, Encoded.BLT,
        Encoded.BGE, Encoded.BLTU, Encoded.BGEU, Encoded.SLTI, Encoded.SLTIU,
        Encoded.XORI, Encoded.ORI, Encoded.ANDI, Encoded.VirtualAssertEQ,
        Encoded.VirtualAlignAddr, Encoded.VirtualWindowMaskB, Encoded.VirtualWindowMaskH,
        Encoded.VirtualWindowMaskW, Encoded.VirtualAssertHalfwordAlignment,
        Encoded.VirtualAssertWordAlignment,
        lbProgramAuto, lbuProgramAuto, lhProgramAuto, lhuProgramAuto, lwProgramAuto,
        lwuProgramAuto, sbProgramAuto, shProgramAuto, swProgramAuto,
        slliProgramAuto, srliProgramAuto, sraiProgramAuto, sllProgramAuto, srlProgramAuto,
        sraProgramAuto, slliwProgramAuto, srliwProgramAuto, sraiwProgramAuto,
        sllwProgramAuto, srlwProgramAuto, srawProgramAuto, mulhProgramAuto, mulhsuProgramAuto,
        lrwProgramAuto, scwProgramAuto, amoswapwProgramAuto, amoaddwProgramAuto,
        amoandwProgramAuto, amoorwProgramAuto, amoxorwProgramAuto, amominwProgramAuto,
        amomaxwProgramAuto, amominuwProgramAuto, amomaxuwProgramAuto,
        lrdProgramAuto, scdProgramAuto, amoswapdProgramAuto, amoadddProgramAuto,
        amoanddProgramAuto, amoordProgramAuto, amoxordProgramAuto, amomindProgramAuto,
        amomaxdProgramAuto, amominudProgramAuto, amomaxudProgramAuto,
        advicelbProgramAuto, advicelhProgramAuto, advicelwProgramAuto, adviceldProgramAuto,
        ecallProgram, ebreakProgram, mretProgram, csrrwProgram, csrrsProgram,
        pureWritebackRdZeroProgram] at advice

private theorem source_internal_advice_of_rows
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (advice : ∃ row ∈ rows, row.instruction.adviceValue? ≠ none) :
    SourceInternalAdvice source.instruction := by
  have checks := ExpansionFacts.expand_instruction_checks source rows emits
  obtain ⟨row, member, hasAdvice⟩ := advice
  have inInstructions : row.instruction ∈ rows.map (·.instruction) :=
    List.mem_map.mpr ⟨row, member, rfl⟩
  unfold SourceInternalAdvice
  cases shape : source.instruction.expand with
  | none => simp only [shape] at checks
  | some result =>
    cases result with
    | native instruction =>
      simp only [shape, Option.any_some, expandedInternalAdvice] at checks ⊢
      rw [checks.1] at inInstructions
      have equal := List.mem_singleton.mp inInstructions
      simpa only [← equal, Option.isSome_iff_ne_none] using hasAdvice
    | sequence instructions =>
      simp only [shape, Option.any_some, expandedInternalAdvice] at checks ⊢
      rw [checks.1] at inInstructions
      exact List.any_eq_true.mpr ⟨row.instruction, inInstructions,
        Option.isSome_iff_ne_none.mpr hasAdvice⟩

private theorem source_expansion_split
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (source : SourceInstructionRow SourceInstruction) (member : source ∈ image.instructions.toList)
    (rows : List JoltInstructionRow) (emits : expand_instruction source = some rows) :
    ∃ before after, bytecode.toList = before ++ rows ++ after := by
  obtain ⟨chunks, mapped, materialized⟩ := Option.map_eq_some_iff.mp expanded
  obtain ⟨index, bound, atSource⟩ := List.mem_iff_getElem.mp member
  obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ chunks mapped
  have inChunks : index < chunks.length := by omega
  have atRows : chunks[index] = rows := by
    have step := steps index bound inChunks
    rw [atSource, emits] at step
    exact (Option.some.inj step).symm
  refine ⟨(chunks.take index).flatten, (chunks.drop (index + 1)).flatten, ?_⟩
  rw [← materialized, List.toList_toArray]
  conv_lhs => rw [← List.take_append_drop index chunks,
    List.drop_eq_getElem_cons inChunks]
  simp only [List.flatten_append, List.flatten_cons, atRows, List.append_assoc]

private theorem expansion_block_eq
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode) (accepted : pc_map_ok bytecode = true)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (source : SourceInstructionRow SourceInstruction) (member : source ∈ image.instructions.toList)
    (rows : List JoltInstructionRow) (emits : expand_instruction source = some rows)
    (inRows : bytecode[first] ∈ rows) :
    expansionInstructions bytecode first = rows.map (·.instruction) ∧
      rows.length = expansionRowCount bytecode first := by
  obtain ⟨index, inside, atRow⟩ := List.mem_iff_getElem.mp inRows
  have valid := expand_instruction_expandedRows source rows emits
  have zero : index = 0 := by
    have start := valid.starts index inside
    rw [atRow, starts] at start
    simpa using start.symm
  subst index
  have count : rows.length = expansionRowCount bytecode first := by
    have remaining := valid.countdown 0 inside
    rw [atRow] at remaining
    unfold expansionRowCount
    omega
  obtain ⟨before, after, splitRows⟩ := source_expansion_split image bytecode expanded source member rows emits
  have inBytecode : before.length < bytecode.size := by
    have sizes := congrArg List.length splitRows
    simp only [Array.length_toList, List.length_append] at sizes
    omega
  have atStart : bytecode[before.length] = bytecode[first] := by
    have h : bytecode.toList[before.length]? = some rows[0] := by
      rw [splitRows, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_append_left inside, List.getElem?_eq_getElem inside]
    simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem inBytecode,
      Option.some.injEq, atRow] using h
  have firstIndex := expand_program_unique image bytecode expanded accepted
    before.length first.val inBytecode first.isLt
    (congrArg JoltInstructionRow.address atStart)
    (congrArg (fun row => row.virtual_sequence_remaining.getD 0) atStart)
  refine ⟨?_, count⟩
  simp only [expansionInstructions, Array.toList_extract, List.extract_eq_take_drop,
    Nat.add_sub_cancel_left, ← count, ← firstIndex, splitRows, List.append_assoc,
    List.drop_left, List.take_left]

private theorem source_instructionAt
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode) (accepted : pc_map_ok bytecode = true)
    (source : SourceInstructionRow SourceInstruction) (member : source ∈ image.instructions.toList) :
    image.instructionAt source.address = some source.instruction := by
  have distinct := pc_map_ok_distinct_addresses image bytecode expanded accepted
  obtain ⟨index, inside, atSource⟩ := List.mem_iff_getElem.mp member
  have found : image.instructions.toList.find? (·.address == source.address) = some source := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp, index, inside, atSource, ?_⟩
    intro other earlier
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro same
    have equal := List.inj_on_of_nodup_map distinct (List.getElem_mem (by omega)) member same
    have indices := (List.Nodup.getElem_inj_iff (List.Nodup.of_map _ distinct)).mp
      (equal.trans atSource.symm)
    omega
  simp only [Rv64ProgramImage.instructionAt, ← Array.find?_toList, found, Option.map_some]

private theorem division_source_expand (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) :
    (kind.source rd rs1 rs2 q).expand =
      some (.ofPureProgram rd (kind.program rd rs1 rs2 q)) := by
  cases kind <;> rfl

private theorem divisionRows_arithmetic (rows : List Instr) (safe : DivisionRows rows) :
    ∀ row ∈ rows, DivisionArithmeticRow row := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
    intro row member
    rcases List.mem_cons.mp member with equal | later
    · subst row
      exact safe.1.1
    · exact ih safe.2 row later

private theorem expanded_division_shape
    (source : SourceInstructionRow SourceInstruction) (rows : List JoltInstructionRow)
    (emits : expand_instruction source = some rows)
    (kind : DivisionKind) (rd rs1 rs2 : regidx) (q : BitVec 64)
    (sourceEq : source.instruction = kind.source rd rs1 rs2 q) (nonzero : rd ≠ .Regidx 0) :
    ArithmeticAdviceSequence (rows.map (·.instruction)) (kind.program rd rs1 rs2) := by
  have notX0 : isX0 rd = false := Bool.eq_false_iff.mpr fun zero =>
    nonzero (ExpansionRows.regidx_zero_of_isX0 zero)
  have checks := ExpansionFacts.expand_instruction_checks source rows emits
  rw [sourceEq, division_source_expand, ExpandedSource.ofPureProgram, notX0] at checks
  simp only [Bool.false_eq_true, ↓reduceIte] at checks
  rw [checks.1]
  obtain ⟨patched, single⟩ := division_program_advice_shape kind rd rs1 rs2 q nonzero
  exact ⟨patched, single,
    divisionRows_arithmetic _ (division_program_rows kind rd rs1 rs2 q),
    ExpansionFacts.sequenceOk_tempsReadAfterWrite _ checks.2.1⟩

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
  obtain ⟨slots, preprocessed⟩ := preprocessed
  have accepted : pc_map_ok bytecode = true := by
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  obtain ⟨source, member, rows, emits, inRows⟩ := expand_program_source_of_row
    image bytecode expanded bytecode[first]
    (by simp only [Array.mem_toList_iff]; exact Array.getElem_mem first.isLt)
  obtain ⟨block, count⟩ := expansion_block_eq image bytecode expanded accepted
    first starts source member rows emits inRows
  have address := expand_instruction_address source rows emits bytecode[first] inRows
  obtain ⟨offset, inside, row, atRow, advice⟩ := hasAdvice
  have inBlock : row.instruction ∈ expansionInstructions bytecode first := by
    have length : (expansionInstructions bytecode first).length = expansionRowCount bytecode first := by
      rw [block, List.length_map, count]
    rw [← expansionInstructions_at bytecode first offset inside length row atRow]
    exact List.getElem_mem (by omega)
  rw [block] at inBlock
  obtain ⟨adviceRow, adviceMember, sameInstruction⟩ := List.mem_map.mp inBlock
  have sourceAdvice := source_internal_advice_of_rows source rows emits
    ⟨adviceRow, adviceMember, by rwa [sameInstruction]⟩
  obtain ⟨kind, rd, rs1, rs2, placeholder, sourceEq, nonzero⟩ :=
    source_advice_kind source.instruction sourceAdvice
  refine ⟨kind, rd, rs1, rs2, placeholder, nonzero, ?_, ?_, ?_⟩
  · rw [address, source_instructionAt image bytecode expanded accepted source member, sourceEq]
  · rw [block, List.length_map, count]
  · rw [block]
    exact expanded_division_shape source rows emits kind rd rs1 rs2 placeholder sourceEq nonzero

end JoltInstance
