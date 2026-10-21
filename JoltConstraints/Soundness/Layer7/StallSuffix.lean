import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer3.Access
import JoltConstraints.Soundness.Layer2.Registers
import JoltConstraints.Completeness.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer5.Registers
import JoltConstraints.Soundness.Layer7.Emission
import JoltConstraints.Soundness.Layer4.Word
import JoltConstraints.Soundness.Layer4.ComparisonEntry
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Arithmetic
import JoltConstraints.trace_interface
import JoltConstraints.Completeness.Helpers.TracePCProofHelpers

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- At `cycle`, either the witness selects padding, or it selects a row of
`last`'s source instruction with the control operands needed to replay its
stall. Branch operands retain their values from `last.preState`; a JALR base
retains its pre-state value unless the JALR wrote that nonzero base, in which
case it holds the value in `last.postState`. For example, replaying
`jalr x1, imm(x1)` reads the link written by its first execution.
See PR #2109 head d2995380, jolt/crates/jolt-riscv/src/row.rs:105-132. -/
def StallSuffixInvariant {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (bytecode : Array JoltInstructionRow)
    (last : TraceRow bytecode) (cycle : Fin params.traceLength) : Prop :=
  witness.InstructionFlags .IsNoop cycle = 1 ∨
    ∃ (slot : Fin (2 ^ params.logBytecodeK)) (row : JoltInstructionRow),
      JoltConstraints.bytecodeRa witness slot cycle = 1 ∧
      JoltConstraints.bytecodeRow bytecode slot.val = some row ∧
      row.address = bytecode[last.rowIndex].address ∧
      let readAtStall (src : JoltISA.Src) : Prop :=
        witness.RegistersVal (TraceWitness.sourceRegisterAddress src) cycle =
          ((JoltISA.sourceValue src last.preState).toNat : F)
      match bytecode[last.rowIndex].instruction with
      | .JALR dst base _ =>
          witness.RegistersVal (TraceWitness.sourceRegisterAddress base) cycle =
            ((JoltISA.sourceValue base
              (if TraceWitness.destinationRegisterAddress dst =
                    TraceWitness.sourceRegisterAddress base ∧
                  (TraceWitness.sourceRegisterAddress base).val ≠ 0 then
                last.postState else last.preState)).toNat : F)
      | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _
      | .BGE lhs rhs _ | .BLTU lhs rhs _ | .BGEU lhs rhs _ =>
          readAtStall lhs ∧ readAtStall rhs
      | _ => True

/-- A bytecode Branch flag identifies one of the six conditional branches;
for example, BEQ carries this flag.
See jolt/crates/jolt-riscv/src/instructions/i/beq.rs:1-20 at 8bbb2357. -/
theorem branch_instruction_of_flag (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    ∃ lhs rhs imm,
      instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm := by
  cases instruction <;> simp_all [JoltMetadata.instructionFlag]

/-- A terminal row carries its source's compression flag itself. For example,
the last ECALL row has the flag used to prepare ECALL's next PC.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 at 8bbb2357. -/
theorem source_compressed_of_last (bytecode : Array JoltInstructionRow)
    (i : Fin bytecode.size)
    (last : bytecode[i].virtual_sequence_remaining.getD 0 = 0) :
    source_is_compressed bytecode i = bytecode[i].is_compressed := by
  unfold source_is_compressed
  simp only [Fin.getElem_fin] at last ⊢
  rw [last]
  simp

/-- A terminal bytecode row's 64-bit link equals its unwrapped source address
plus its length when the image satisfies `NextPCNoWrap`. For example, an
uncompressed JALR at address `0x1000` links to `0x1004`.
See jolt/tracer/src/instruction/jalr.rs:19-30 at 8bbb2357. -/
theorem terminal_link_no_wrap
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (noWrap : image.NextPCNoWrap)
    (index : Fin bytecode.size)
    (terminal : bytecode[index].virtual_sequence_remaining.getD 0 = 0) :
    (bytecode[index].address +
      if bytecode[index].is_compressed then 2 else 4).toNat =
      bytecode[index].address.toNat +
        if bytecode[index].is_compressed then 2 else 4 := by
  have bound := expand_program_next_pc_no_wrap image bytecode expanded noWrap index
  rw [source_compressed_of_last bytecode index terminal] at bound
  cases compressed : bytecode[index].is_compressed with
  | false =>
      simp only [compressed, Bool.false_eq_true, ↓reduceIte] at bound ⊢
      simp only [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt bound
  | true =>
      simp only [compressed, ↓reduceIte] at bound ⊢
      simp only [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt bound

/-- At a represented real cycle, the selected bytecode slot is the executed
row's index plus one; for example, row zero occupies slot one.
See jolt/crates/jolt-witness/src/witnesses/pc.rs:1-35 at 8bbb2357. -/
theorem selected_represented_row
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size) :
    JoltConstraints.bytecodeRa witness
      ⟨run.rows[cycle.val].rowIndex.val + 1, by
        have domain : params.BytecodeDomainFor run.bytecode.size := by
          simpa only [bytecodeEq] using context.bytecodeDomain
        have fits := domain.rowsFit
        have rowBound := run.rows[cycle.val].rowIndex.isLt
        omega⟩ cycle = 1 := by
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) context equations cycle
  have pcSelected := JoltConstraints.Soundness.pc_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected
  have pcRun := represented.pc cycle inRun
  have encoded : (slot.val : F) = ((run.rows[cycle.val].rowIndex.val + 1 : Nat) : F) := by
    rw [← pcSelected, pcRun]
    simp [TraceWitness.PC, TraceWitness.bytecodePc, inRun]
  have slotBound : slot.val < ringChar F := by
    have domain := params.logBytecodeK_lt_usizeBits
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have rowBound : run.rows[cycle.val].rowIndex.val + 1 < ringChar F := by
    have domain : params.BytecodeDomainFor run.bytecode.size := by
      simpa only [bytecodeEq] using context.bytecodeDomain
    have fits := domain.rowsFit
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have same := JoltConstraints.Soundness.natCast_injective_below_char
    slotBound rowBound encoded
  have sameSlot : slot = ⟨run.rows[cycle.val].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[cycle.val].rowIndex.isLt
      omega⟩ := Fin.ext same
  simpa only [sameSlot] using selected

/-- Rows at one accepted bytecode address come from one source instruction's
expansion. For example, every row at an ECALL address comes from that ECALL.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:119-164 at 8bbb2357. -/
theorem expanded_same_source_rows
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (first second : JoltInstructionRow)
    (firstMember : first ∈ bytecode.toList)
    (secondMember : second ∈ bytecode.toList)
    (sameAddress : first.address = second.address) :
    ∃ source ∈ image.instructions.toList,
      ∃ rows : List JoltInstructionRow,
        expand_instruction source = some rows ∧ first ∈ rows ∧ second ∈ rows := by
  have originalExpanded := expanded
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => simp only [mapped, Option.map_none] at expanded; cases expanded
  | some groups =>
      simp only [mapped, Option.map_some, Option.some.injEq] at expanded
      have distinct := pc_map_ok_distinct_addresses image bytecode
        originalExpanded accepted
      subst bytecode
      obtain ⟨firstRows, firstRowsMember, firstIn⟩ := List.mem_flatten.mp firstMember
      obtain ⟨secondRows, secondRowsMember, secondIn⟩ := List.mem_flatten.mp secondMember
      obtain ⟨i, iBound, firstRowsAt⟩ := List.mem_iff_getElem.mp firstRowsMember
      obtain ⟨j, jBound, secondRowsAt⟩ := List.mem_iff_getElem.mp secondRowsMember
      obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction
        image.instructions.toList groups mapped
      have iSourceBound : i < image.instructions.toList.length := by omega
      have jSourceBound : j < image.instructions.toList.length := by omega
      have firstStep := steps i iSourceBound iBound
      have secondStep := steps j jSourceBound jBound
      have firstAt : first ∈ groups[i] := by simpa only [firstRowsAt] using firstIn
      have secondAt : second ∈ groups[j] := by simpa only [secondRowsAt] using secondIn
      have firstAddress := expand_instruction_address
        image.instructions.toList[i] groups[i] firstStep first firstAt
      have secondAddress := expand_instruction_address
        image.instructions.toList[j] groups[j] secondStep second secondAt
      have iMapBound : i < (image.instructions.toList.map (·.address)).length := by
        simpa only [List.length_map] using iSourceBound
      have jMapBound : j < (image.instructions.toList.map (·.address)).length := by
        simpa only [List.length_map] using jSourceBound
      have indices : i = j := by
        apply (List.Nodup.getElem_inj_iff distinct
          (hi := iMapBound) (hj := jMapBound)).mp
        rw [List.getElem_map, List.getElem_map]
        exact firstAddress.symm.trans (sameAddress.trans secondAddress)
      subst j
      refine ⟨image.instructions.toList[i], List.getElem_mem _ , groups[i], firstStep,
        firstAt, ?_⟩
      exact secondAt

/-- If the stable row constrains its next unexpanded address to its own source,
the first real suffix cycle selects a row at that source. For example, after
`j .` the next real cycle selects the same JAL address.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:347-353
at 8bbb2357. -/
theorem selected_source_after_stable
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (nonempty : 0 < run.rows.size)
    (lastBound : run.rows.size - 1 < params.traceLength)
    (cutBound : run.rows.size < params.traceLength)
    (target : witness.NextUnexpandedPC ⟨run.rows.size - 1, lastBound⟩ =
      (run.bytecode[last.rowIndex].address.toNat : F))
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, cutBound⟩ ≠ 1) :
    ∃ (slot : Fin (2 ^ params.logBytecodeK)) (row : JoltInstructionRow),
      JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, cutBound⟩ = 1 ∧
      JoltConstraints.bytecodeRow run.bytecode slot.val = some row ∧
      row.address = run.bytecode[last.rowIndex].address := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  let previous : Fin params.traceLength := ⟨run.rows.size - 1, lastBound⟩
  let cut : Fin params.traceLength := ⟨run.rows.size, cutBound⟩
  have nextEq : previous.val + 1 = cut.val := by
    dsimp [previous, cut]
    omega
  have shifted : witness.UnexpandedPC cut =
      (run.bytecode[last.rowIndex].address.toNat : F) := by
    have shift := equations.nextUnexpandedPCEqShift previous
    simp only [dif_pos (show previous.val + 1 < params.traceLength by omega)] at shift
    simpa only [nextEq] using shift.symm.trans target
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    charAbove2pow127 context equations cut
  cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
  | none =>
      have flag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
        charAbove2pow127 context equations .IsNoop cut slot selected
      simp [JoltConstraints.bytecodeInstructionFlag, present] at flag
      exact False.elim (real flag)
  | some row =>
      have read := JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        charAbove2pow127 context equations cut slot selected
      have equalField : (row.address.toNat : F) =
          (run.bytecode[last.rowIndex].address.toNat : F) := by
        simpa [JoltConstraints.bytecodeAddress, present] using read.symm.trans shifted
      have equalWord := JoltConstraints.Soundness.word_eq_of_field_eq
        charAbove2pow127 equalField
      refine ⟨slot, row, selected, ?_, equalWord⟩
      simpa only [bytecodeEq] using present

/-- A selected row's first or second source reads its register-table entry.
For example, BEQ's two selected operands read the table entries for its bases.
See jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:97-121
at 8bbb2357. -/
theorem selected_operand_register
    {F : Type} [Field F] (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (second : Bool) (register : Fin 128)
    (reads : (if second then JoltConstraints.bytecodeRs2Register row.instruction
      else JoltConstraints.bytecodeRs1Register row.instruction) = some register) :
    (if second then witness.Rs2Value cycle else witness.Rs1Value cycle) =
      witness.RegistersVal register cycle := by
  cases second with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at reads ⊢
      rw [JoltConstraints.Soundness.rs1Value_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected]
      simp [rowIs, reads]
  | true =>
      simp only [↓reduceIte] at reads ⊢
      rw [JoltConstraints.Soundness.rs2Value_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected]
      simp [rowIs, reads]

/-- Across one represented row, a control source's table entry remains its
pre-state value unless that row selects it as destination, in which case it
becomes the constrained write value. For example, `jalr x1, imm(x1)` updates
the table entry for x1, while `jalr x2, imm(x1)` leaves x1 unchanged.
See jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:97-121
at 8bbb2357. -/
theorem represented_read_register_succ
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size)
    (next : cycle.val + 1 < params.traceLength)
    (second : Bool) (source : JoltISA.Src)
    (reads : (if second then JoltConstraints.bytecodeRs2Register
        run.bytecode[run.rows[cycle.val].rowIndex].instruction
      else JoltConstraints.bytecodeRs1Register
        run.bytecode[run.rows[cycle.val].rowIndex].instruction) =
      some (TraceWitness.sourceRegisterAddress source))
    (observed :
      (if second then TraceWitness.Rs2Value params run.toTrace cycle
      else TraceWitness.Rs1Value params run.toTrace cycle) =
      ((JoltISA.sourceValue source run.rows[cycle.val].preState).toNat : F)) :
    witness.RegistersVal (TraceWitness.sourceRegisterAddress source)
        ⟨cycle.val + 1, next⟩ =
      match JoltConstraints.bytecodeRdRegister
          run.bytecode[run.rows[cycle.val].rowIndex].instruction with
      | none => ((JoltISA.sourceValue source run.rows[cycle.val].preState).toNat : F)
      | some destination =>
          if TraceWitness.sourceRegisterAddress source = destination then
            witness.RdWriteValue cycle
          else ((JoltISA.sourceValue source run.rows[cycle.val].preState).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  let slot : Fin (2 ^ params.logBytecodeK) :=
    ⟨run.rows[cycle.val].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[cycle.val].rowIndex.isLt
      omega⟩
  have selected := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented cycle inRun
  have rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[run.rows[cycle.val].rowIndex] := by
    simp [slot, ← bytecodeEq, JoltConstraints.bytecodeRow]
  have tableRead := selected_operand_register charAbove2pow127 joltInstance
    privateInputs witness context equations cycle slot selected
    run.bytecode[run.rows[cycle.val].rowIndex] rowAt second
    (TraceWitness.sourceRegisterAddress source) reads
  have traceRead :
      (if second then witness.Rs2Value cycle else witness.Rs1Value cycle) =
        (if second then TraceWitness.Rs2Value params run.toTrace cycle
        else TraceWitness.Rs1Value params run.toTrace cycle) := by
    cases second with
    | false => simpa using represented.rs1 cycle inRun
    | true => simpa using represented.rs2 cycle inRun
  have before : witness.RegistersVal (TraceWitness.sourceRegisterAddress source) cycle =
      ((JoltISA.sourceValue source run.rows[cycle.val].preState).toNat : F) :=
    tableRead.symm.trans (traceRead.trans observed)
  have after := JoltConstraints.Soundness.registersVal_succ_of_selected_bytecode
    charAbove2pow127 context equations (TraceWitness.sourceRegisterAddress source)
    cycle next slot selected
  simpa only [rowAt, Option.bind_some, before] using after

/-- The last represented row occupies a real selected cycle immediately before
the cut. For example, a retained `jal x0, 0` selects its JAL bytecode slot at
the cycle before the first suffix cycle.
See jolt/crates/jolt-witness/src/witnesses/pc.rs:1-35 at 8bbb2357. -/
theorem selected_last_represented_row
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (cutBound : run.rows.size < params.traceLength) :
    ∃ (before : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK)),
      before.val + 1 = run.rows.size ∧
      run.rows[before.val]? = some last ∧
      JoltConstraints.bytecodeRa witness slot before = 1 ∧
      JoltConstraints.bytecodeRow run.bytecode slot.val =
        some run.bytecode[last.rowIndex] ∧
      witness.InstructionFlags .IsNoop before = 0 := by
  have nonempty : 0 < run.rows.size := by
    have existsRow : run.rows.back? = some last := by simpa using atEnd
    by_contra empty
    have zero : run.rows.size = 0 := by omega
    simp [Array.back?_eq_getElem?, zero] at existsRow
  have beforeBound : run.rows.size - 1 < params.traceLength := by omega
  let before : Fin params.traceLength := ⟨run.rows.size - 1, beforeBound⟩
  have inRun : before.val < run.rows.size := by dsimp [before]; omega
  have lastAt : run.rows[before.val] = last := by
    have atEndEq : run.rows.back? = some last := by simpa using atEnd
    rw [Array.back?_eq_getElem?] at atEndEq
    have atIndex : run.rows[before.val]? = some last := by
      simpa [before] using atEndEq
    exact Option.some.inj ((Array.getElem?_eq_getElem inRun).symm.trans atIndex)
  let slot : Fin (2 ^ params.logBytecodeK) :=
    ⟨run.rows[before.val].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[before.val].rowIndex.isLt
      omega⟩
  have selected := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented before inRun
  have rowAt : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by
    simp [slot, lastAt, JoltConstraints.bytecodeRow]
  have noOpFlag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations .IsNoop before slot selected
  have real : witness.InstructionFlags .IsNoop before = 0 := by
    simpa [← bytecodeEq, rowAt, JoltConstraints.bytecodeInstructionFlag,
      JoltMetadata.instructionFlag] using noOpFlag
  refine ⟨before, slot, by dsimp [before]; omega, ?_, selected, rowAt, real⟩
  simpa only [Array.getElem?_eq_getElem inRun] using congrArg some lastAt

/-- A represented control operand at the last retained cycle equals the
corresponding source register in the last row's pre-state. For example, a
retained BEQ reads its two pre-state operands from their register-table entries.
See jolt/crates/jolt-witness/src/witnesses/registers.rs:1-35 at 8bbb2357. -/
theorem represented_last_control_read
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode)
    (before : Fin params.traceLength) (inRun : before.val < run.rows.size)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot before = 1)
    (rowAt : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (second : Bool) (source : JoltISA.Src)
    (reads : (if second then JoltConstraints.bytecodeRs2Register
        run.bytecode[last.rowIndex].instruction
      else JoltConstraints.bytecodeRs1Register
        run.bytecode[last.rowIndex].instruction) =
      some (TraceWitness.sourceRegisterAddress source))
    (observed :
      (if second then TraceWitness.Rs2Value params run.toTrace before
      else TraceWitness.Rs1Value params run.toTrace before) =
        ((JoltISA.sourceValue source last.preState).toNat : F)) :
    witness.RegistersVal (TraceWitness.sourceRegisterAddress source) before =
      ((JoltISA.sourceValue source last.preState).toNat : F) := by
  have rowAtContext : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by simpa only [← bytecodeEq] using rowAt
  have read := selected_operand_register
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) joltInstance
    privateInputs witness context equations before slot selected
    run.bytecode[last.rowIndex] rowAtContext second
    (TraceWitness.sourceRegisterAddress source) reads
  have representedRead :
      (if second then witness.Rs2Value before else witness.Rs1Value before) =
        (if second then TraceWitness.Rs2Value params run.toTrace before
        else TraceWitness.Rs1Value params run.toTrace before) := by
    cases second with
    | false => simpa using represented.rs1 before inRun
    | true => simpa using represented.rs2 before inRun
  exact read.symm.trans (representedRead.trans observed)

/-- A constrained next unexpanded PC selects padding or a bytecode row at
that address. For example, a `JAL +0` target at address `a` can only lead to
padding or a row whose address is `a`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:344-352
at 8bbb2357. -/
private theorem stall_next_cycle_of_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (target : BitVec 64)
    (targetEq : witness.NextUnexpandedPC cycle = (target.toNat : F)) :
    witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 1 ∨
      ∃ (slot : Fin (2 ^ params.logBytecodeK)) (row : JoltInstructionRow),
        JoltConstraints.bytecodeRa witness slot ⟨cycle.val + 1, next⟩ = 1 ∧
        JoltConstraints.bytecodeRow context.bytecode slot.val = some row ∧
        row.address = target := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := by
    have large := joltField
    unfold JoltField at large
    omega
  obtain ⟨slot, selected, _⟩ :=
    JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations
      ⟨cycle.val + 1, next⟩
  cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
  | none =>
      left
      simpa [JoltConstraints.bytecodeInstructionFlag, present] using
        (JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
          charAbove2pow127 context equations .IsNoop ⟨cycle.val + 1, next⟩ slot selected)
  | some row =>
      right
      have shifted : witness.UnexpandedPC ⟨cycle.val + 1, next⟩ =
          (target.toNat : F) := by
        simpa only [equations.nextUnexpandedPCEqShift cycle, dif_pos next] using targetEq
      have encoded : (row.address.toNat : F) = (target.toNat : F) := by
        simpa [JoltConstraints.bytecodeAddress, present] using
          (JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
            charAbove2pow127 context equations ⟨cycle.val + 1, next⟩ slot selected).symm.trans shifted
      exact ⟨slot, row, selected, present,
        JoltConstraints.Soundness.word_eq_of_field_eq charAbove2pow127 encoded⟩

/-- A real bytecode slot is one plus the index of its row in the expanded
array. For example, slot one contains bytecode row zero.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:1-30 at 8bbb2357. -/
private theorem stall_real_slot_index (bytecode : Array JoltInstructionRow)
    (slot : Nat) (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow bytecode slot = some row) :
    ∃ index : Fin bytecode.size, slot = index.val + 1 ∧ row = bytecode[index] := by
  cases slot with
  | zero => simp [JoltConstraints.bytecodeRow] at present
  | succ n =>
      have inRange : n < bytecode.size := by
        exact (Array.getElem?_eq_some_iff.mp
          (show bytecode[n]? = some row by simpa [JoltConstraints.bytecodeRow] using present)).1
      refine ⟨⟨n, inRange⟩, rfl, ?_⟩
      simpa only [JoltConstraints.bytecodeRow, Array.getElem?_eq_getElem inRange,
        Option.some.injEq] using present.symm

/-- A real selected row of accepted expanded bytecode has an array index, and
its slot can be read through the witness context. For example, bytecode row
zero is selected through slot one.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:119-164 at 8bbb2357. -/
theorem stall_cycle_selected_row
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (bytecode : Array JoltInstructionRow)
    (bytecodeEq : bytecode = context.bytecode)
    (slot : Fin (2 ^ params.logBytecodeK)) (row : JoltInstructionRow)
    (rowAt : JoltConstraints.bytecodeRow bytecode slot.val = some row) :
    pc_map_ok bytecode = true ∧
      JoltConstraints.bytecodeRow context.bytecode slot.val = some row ∧
      ∃ index : Fin bytecode.size,
        slot.val = index.val + 1 ∧ row = bytecode[index] := by
  have acceptedContext : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  have accepted : pc_map_ok bytecode = true := by
    simpa only [bytecodeEq] using acceptedContext
  obtain ⟨index, slotIs, rowIs⟩ := stall_real_slot_index bytecode slot.val row rowAt
  exact ⟨accepted, by simpa only [← bytecodeEq] using rowAt,
    index, slotIs, rowIs⟩

/-- A selected JAL row's lookup computes its wrapped bytecode address plus
its immediate. For example, `JAL +0` at `a` looks up `a`.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/jal.rs:18-30
at 8bbb2357. -/
private theorem stall_jal_lookup_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : row.instruction = .JAL dst imm) :
    witness.LookupOutput cycle = ((row.address + imm).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have inputs := JoltConstraints.Soundness.instructionInputs_of_selected_bytecode
    charAbove2pow127 context equations cycle slot selected row present
  have address : witness.UnexpandedPC cycle = (row.address.toNat : F) := by
    simpa [JoltConstraints.bytecodeAddress, present] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  have immediate : witness.Imm cycle = (imm.toNat : F) := by
    simpa [JoltConstraints.bytecodeImmediate, present, jump,
      JoltMetadata.immediate] using
      JoltConstraints.Soundness.imm_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  have left : witness.LeftInstructionInput cycle = (row.address.toNat : F) := by
    simpa [jump, JoltMetadata.instructionFlag, address] using inputs.1
  have right : witness.RightInstructionInput cycle = (imm.toNat : F) := by
    simpa [jump, JoltMetadata.instructionFlag, immediate] using inputs.2
  have active : witness.OpFlags .AddOperands cycle = 1 := by
    simpa [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, jump] using
      JoltConstraints.Soundness.opFlag_of_selected_bytecode
        charAbove2pow127 context equations .AddOperands cycle slot selected
  have table : (JoltConstraints.bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck := by
    simp [present, jump, JoltMetadata.lookupTable]
  exact JoltConstraints.Soundness.lookupOutput_rangeCheck_add joltField context equations
    cycle slot selected table active row.address imm left right

/-- If a selected JAL is followed by a real cycle, the jump constraint sets
the next unexpanded PC to its lookup target. For example, `JAL +0` at `a`
keeps the next unexpanded PC at `a`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:344-352
at 8bbb2357. -/
private theorem stall_jal_next_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : row.instruction = .JAL dst imm)
    (nextReal : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1) :
    witness.NextUnexpandedPC cycle = ((row.address + imm).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have jumpFlag : witness.OpFlags .Jump cycle = 1 := by
    simpa [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, jump] using
      JoltConstraints.Soundness.opFlag_of_selected_bytecode
        charAbove2pow127 context equations .Jump cycle slot selected
  have nextNoop : witness.NextIsNoop cycle = 0 := by
    have shifted := equations.nextIsNoopEqShift cycle
    simp only [dif_pos next] at shifted
    obtain ⟨nextSlot, nextSelected, _⟩ :=
      JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations
        ⟨cycle.val + 1, next⟩
    have flag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
      charAbove2pow127 context equations .IsNoop ⟨cycle.val + 1, next⟩
        nextSlot nextSelected
    cases presentNext : JoltConstraints.bytecodeRow context.bytecode nextSlot.val with
    | none =>
        simp [JoltConstraints.bytecodeInstructionFlag, presentNext] at flag
        exact False.elim (nextReal flag)
    | some nextRow =>
        simp [JoltConstraints.bytecodeInstructionFlag, presentNext,
          JoltMetadata.instructionFlag] at flag
        exact shifted.trans flag
  have shouldJump : witness.ShouldJump cycle = 1 := by
    rw [equations.shouldJumpEqJumpMulNotNextIsNoop cycle, jumpFlag, nextNoop]
    ring
  have relation := equations.nextUnexpandedPCEqLookupIfShouldJump cycle
  rw [shouldJump, one_mul] at relation
  exact (sub_eq_zero.mp relation).trans
    (stall_jal_lookup_target joltField joltInstance privateInputs witness
      context equations cycle slot selected row present dst imm jump)

/-- Executing a JAL puts its address plus immediate in Sail's nextPC. For
example, `JAL +0` at address `a` leaves nextPC at `a`.
See jolt/tracer/src/instruction/jal.rs:19-30 at 8bbb2357. -/
private theorem stall_jal_exec_target (dst : JoltISA.Dst) (imm address link : BitVec 64)
    (pre post : SailJoltState)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltISA.execInstr (.JAL dst imm) pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some (address + imm) := by
  have readNext : liftSail (Sail.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link nextPC]
  have readPC : liftSail (Sail.readReg Register.PC) pre = .ok address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail address pc]
  simp only [JoltISA.execInstr, bind, EStateM.bind, readNext, readPC] at runs
  cases written : JoltISA.writeDst dst link pre with
  | error error state => simp only [written] at runs; cases runs
  | ok result middle =>
      cases result
      simp only [written, liftSail, Sail.writeReg, pure, EStateM.pure] at runs
      cases runs
      simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, ↓reduceDIte, cast_eq]

/-- An executed JAL whose post-state nextPC is its own address has immediate
zero. For example, a replaying `j .` is `JAL +0`.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
private theorem stall_jal_immediate_zero (dst : JoltISA.Dst)
    (imm address link : BitVec 64) (pre post : SailJoltState)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltISA.execInstr (.JAL dst imm) pre = .ok RETIRE_SUCCESS post)
    (stalled : post.sail.regs.get? Register.nextPC = some address) : imm = 0 := by
  have target := stall_jal_exec_target dst imm address link pre post pc nextPC runs
  have same : address + imm = address := Option.some.inj (target.symm.trans stalled)
  exact add_eq_left.mp same

/-- A row certified as the back of a run is its final indexed row, so its
execution certificate and prepared PC are available. For example, a one-row
`j .` run has its sole row at index zero.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
private theorem stall_last_run_index
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?) :
    ∃ i : Fin run.rows.size, run.rows[i] = last := by
  have someLast : run.rows.back? = some last := by simpa using atEnd
  rw [Array.back?_eq_getElem?] at someLast
  have inRange : run.rows.size - 1 < run.rows.size :=
    (Array.getElem?_eq_some_iff.mp someLast).1
  refine ⟨⟨run.rows.size - 1, inRange⟩, ?_⟩
  exact (Array.getElem?_eq_some_iff.mp someLast).2

/-- A selected row preserves a register it does not write at the next cycle.
For example, `jalr x2, 0(x1)` leaves x1's table entry unchanged.
See jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:97-121
at 8bbb2357. -/
theorem register_unchanged_of_no_write
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (register : Fin 128)
    (noWrite : JoltConstraints.bytecodeRdRegister row.instruction ≠ some register) :
    witness.RegistersVal register ⟨cycle.val + 1, next⟩ =
      witness.RegistersVal register cycle := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have succ := JoltConstraints.Soundness.registersVal_succ_of_selected_bytecode
    charAbove2pow127 context equations register cycle next slot selected
  cases destination : JoltConstraints.bytecodeRdRegister row.instruction with
  | none => simpa [present, destination] using succ
  | some written =>
      have different : register ≠ written := by
        intro same
        exact noWrite (by simpa only [same] using destination)
      simpa [present, destination, different] using succ

/-- A Branch flag identifies one of the six conditional branch instructions.
For example, BEQ has this flag and its two source operands are explicit.
See jolt/crates/jolt-riscv/src/instructions/b/beq.rs:1-35 at 8bbb2357. -/
private theorem stall_branch_shape (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    ∃ lhs rhs imm,
      instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm := by
  cases instruction <;> simp_all [JoltMetadata.instructionFlag]

/-- Each branch's control inputs come from both source registers, with no
runtime advice. For example, BEQ compares Rs1 and Rs2 without an immediate
lookup operand. See jolt/crates/jolt-riscv/src/instructions/b/beq.rs:1-35
at 8bbb2357. -/
private theorem stall_branch_control_flags (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = true ∧
      JoltMetadata.instructionRafFlag instruction = false ∧
      JoltMetadata.instructionFlag instruction .LeftOperandIsPC = false ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsImm = false := by
  obtain ⟨lhs, rhs, imm, shape⟩ := stall_branch_shape instruction branch
  rcases shape with h | h | h | h | h | h
  all_goals simp [h, JoltMetadata.instructionFlag,
    JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag]

/-- Each branch's comparison table returns the same taken bit as the ISA
branch decision on two words. For example, BEQ on equal words returns one.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/beq.rs:1-35
at 8bbb2357. -/
private theorem stall_branch_table_decision
    {F : Type} [Field F] (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true)
    (lhs rhs : BitVec 64) :
    (match JoltMetadata.lookupTable instruction with
      | some table => JoltConstraints.lookupTableEntry (F := F) table
          (TraceWitness.interleaveLookupOperands lhs rhs).toFin
      | none => 0) =
      if JoltISA.branchDecisionPure instruction lhs rhs then 1 else 0 := by
  cases instruction <;> simp_all [JoltMetadata.instructionFlag,
    JoltMetadata.lookupTable, JoltConstraints.lookupTableEntry,
    JoltConstraints.equal_entry, JoltConstraints.notEqual_entry,
    JoltConstraints.signedLessThan_entry,
    JoltConstraints.signedGreaterThanEqual_entry,
    JoltConstraints.unsignedLessThan_entry,
    JoltConstraints.unsignedGreaterThanEqual_entry,
    JoltISA.branchDecisionPure, zopz0zI_s, zopz0zKzJ_s,
    zopz0zI_u, zopz0zKzJ_u, BitVec.toNatInt, BitVec.lt_def,
    BitVec.le_def]

/-- A selected branch row uses its two register inputs in the comparison
table, so its lookup output is the ISA taken bit. For example, BEQ with two
equal register values has lookup output one.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:347-352
at 8bbb2357. -/
private theorem stall_branch_lookup_decision
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    (lhs rhs : BitVec 64)
    (rs1 : witness.Rs1Value cycle = (lhs.toNat : F))
    (rs2 : witness.Rs2Value cycle = (rhs.toNat : F)) :
    witness.LookupOutput cycle =
      if JoltISA.branchDecisionPure row.instruction lhs rhs then 1 else 0 := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have flags := stall_branch_control_flags row.instruction branch
  have inputs := JoltConstraints.Soundness.instructionInputs_of_selected_bytecode
    charAbove2pow127 context equations cycle slot selected row present
  have left : witness.LeftInstructionInput cycle = (lhs.toNat : F) := by
    simpa only [flags.1, ↓reduceIte, flags.2.2.2.1, Bool.false_eq_true,
      add_zero, rs1] using inputs.1
  have right : witness.RightInstructionInput cycle = (rhs.toNat : F) := by
    simpa only [flags.2.1, ↓reduceIte, flags.2.2.2.2, Bool.false_eq_true,
      add_zero, rs2] using inputs.2
  have raf : witness.InstructionRafFlag cycle = 0 := by
    simpa [JoltConstraints.bytecodeRafFlag, present, flags.2.2.1] using
      JoltConstraints.Soundness.instructionRafFlag_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  obtain ⟨leftLookup, rightLookup⟩ :=
    JoltConstraints.Soundness.lookupOperands_eq_inputs_of_raf_zero
      charAbove2pow127 context equations cycle raf
  have output := JoltConstraints.Soundness.lookupOutput_of_interleaved
    charAbove2pow127 context equations cycle slot selected lhs rhs raf
      (leftLookup.trans left) (rightLookup.trans right)
  simp only [present, Option.bind_some] at output
  exact output.trans (stall_branch_table_decision row.instruction branch lhs rhs)

/-- An ordinary row leaves the pending next PC unchanged even when its tape
answer is chosen independently. For example, an interior VirtualAdviceLoad row
may choose any value without changing the pending return address.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
private theorem ordinary_tape_next_pc
    (instruction : JoltISA.Instr) (answer : BitVec 64)
    (before after : SailJoltState)
    (ordinaryRow : ExpansionFacts.ordinary instruction = true)
    (runs : JoltConstraints.Soundness.execWithTapeAnswer instruction answer before =
      .ok (.Retire_Success ()) after) :
    after.sail.regs.get? Register.nextPC = before.sail.regs.get? Register.nextPC := by
  cases instruction with
  | VirtualAdviceLoad dst width =>
      simp only [JoltConstraints.Soundness.execWithTapeAnswer] at runs
      split at runs
      · rename_i widthOk
        let prepared : SailJoltState :=
          { before with adviceTape :=
              { before.adviceTape with
                readPosition := before.adviceTape.readPosition + width.toNat } }
        change (do JoltISA.writeDst dst answer; pure RETIRE_SUCCESS) prepared =
          .ok (.Retire_Success ()) after at runs
        simp only [bind, EStateM.bind] at runs
        cases written : JoltISA.writeDst dst answer prepared with
        | error e s => simp only [written] at runs; cases runs
        | ok value s =>
            simp only [written, pure, EStateM.pure] at runs
            have frame := JoltNextPCFrame.write_rule dst answer prepared s value written
            cases runs
            simpa [prepared] using frame
      · cases runs
  | _ =>
      exact ExpansionRows.nextPC_unchanged_of_ordinary _ before after ordinaryRow
        (by simpa only [JoltConstraints.Soundness.execWithTapeAnswer] using runs)

/-- A non-jump, non-branch tape row retains nextPC, including HostIO, which
keeps the Sail state. For example, an SD does not alter the pending next PC.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
private theorem noncontrol_tape_next_pc
    (instruction : JoltISA.Instr) (answer : BitVec 64)
    (before after : SailJoltState)
    (notJump : JoltMetadata.opcodeFlag instruction .Jump = false)
    (notBranch : JoltMetadata.instructionFlag instruction .Branch = false)
    (runs : JoltConstraints.Soundness.execWithTapeAnswer instruction answer before =
      .ok (.Retire_Success ()) after) :
    after.sail.regs.get? Register.nextPC = before.sail.regs.get? Register.nextPC := by
  by_cases ordinaryRow : ExpansionFacts.ordinary instruction = true
  · exact ordinary_tape_next_pc instruction answer before after ordinaryRow runs
  · cases instruction with
    | VirtualHostIO dst src imm =>
      have ranHost : JoltISA.execHostIO before = .ok (.Retire_Success ()) after := by
        simpa only [JoltConstraints.Soundness.execWithTapeAnswer, JoltISA.execInstr]
          using runs
      rw [execHostIO_keeps_sail before after _ ranHost]
    | _ =>
        simp_all [ExpansionFacts.ordinary, JoltMetadata.opcodeFlag,
          JoltMetadata.instructionFlag]

/-- Executing any untrusted-answer row leaves the source PC register unchanged;
tape answers can change a destination value but not PC. For example, a JAL
changes nextPC while its PC remains the address of the JAL.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
private theorem tape_row_preserves_pc
    (instruction : JoltISA.Instr) (answer : BitVec 64)
    (before after : SailJoltState)
    (runs : JoltConstraints.Soundness.execWithTapeAnswer instruction answer before =
      .ok (.Retire_Success ()) after) :
    after.sail.regs.get? Register.PC = before.sail.regs.get? Register.PC := by
  unfold JoltConstraints.Soundness.execWithTapeAnswer at runs
  split at runs
  · rename_i skipped dst width
    let prepared : SailJoltState :=
      { before with adviceTape :=
          { before.adviceTape with
            readPosition := before.adviceTape.readPosition + width.toNat } }
    split at runs
    · change (do JoltISA.writeDst dst answer; pure RETIRE_SUCCESS) prepared =
        .ok (.Retire_Success ()) after at runs
      have frame := JoltPCFrame.bind_rule (JoltPCFrame.write_rule dst answer)
        (fun _ => JoltPCFrame.pure_rule RETIRE_SUCCESS) prepared after _ runs
      simpa [prepared] using frame
    · cases runs
  · have hostFrame : instruction.HostIOPCFrame before after := by
      unfold JoltISA.Instr.HostIOPCFrame
      split
      · rename_i skipped instr dst src imm notTape
        have ranHost : JoltISA.execHostIO before = .ok (.Retire_Success ()) after := by
          simpa only [JoltISA.execInstr] using runs
        rw [execHostIO_keeps_sail before after _ ranHost]
      · trivial
    exact JoltPCFrame.instruction instruction before after hostFrame runs

/-- Every row of an untrusted-answer run begins with PC at its bytecode source
address. For example, the second row of an ECALL expansion still has PC at the
ECALL address. See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
theorem untrusted_row_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) :
    run.rows[i].preState.sail.regs.get? Register.PC =
      some run.bytecode[run.rows[i].rowIndex].address := by
  have layout := expand_program_layout joltInstance.program run.bytecode run.expands
  have all (n : Nat) (bound : n < run.rows.size) :
      run.rows[n].preState.sail.regs.get? Register.PC =
        some run.bytecode[run.rows[n].rowIndex].address := by
    induction n with
    | zero =>
        obtain ⟨entry, _, prepared⟩ :=
          run.starts run.rows[0] (Array.getElem?_eq_getElem bound)
        rw [prepared]
        simp only [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq,
          ↓reduceDIte, cast_eq]
        exact congrArg some entry.symm
    | succ n ih =>
        have beforeBound : n < run.rows.size := by omega
        have link := run.linked n run.rows[n] run.rows[n + 1]
          (Array.getElem?_eq_getElem beforeBound)
          (Array.getElem?_eq_getElem bound)
        split at link
        · rename_i continues
          have preStateEq := link.2
          have continuesFlag : run.bytecode[run.rows[n].rowIndex].continues = true := by
            simpa [JoltInstructionRow.continues, bne_iff_ne] using continues
          have sameAddress := (layout.next run.rows[n].rowIndex
            run.rows[n + 1].rowIndex link.1 continuesFlag).1
          have runs := run.executes ⟨n, beforeBound⟩
          have kept := tape_row_preserves_pc
            (run.bytecode[run.rows[n].rowIndex].instruction.withRuntimeAdvice
              run.rows[n].runtimeAdvice) (run.answers ⟨n, beforeBound⟩)
            run.rows[n].preState run.rows[n].postState runs
          rw [preStateEq, sameAddress]
          exact kept.trans (ih beforeBound)
        · rename_i continues
          obtain ⟨address, _, sourceAddress, _, prepared⟩ := link
          rw [prepared]
          simp only [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq,
            ↓reduceDIte, cast_eq]
          exact congrArg some sourceAddress.symm
  exact all i.val i.isLt

/-- Consecutive rows within one source read the same compression flag from
that source's final row. For example, both ECALL rows use its final-row flag.
See jolt/crates/jolt-program/src/expand/metadata.rs:46-52 at 8bbb2357. -/
private theorem source_compressed_next
    (bytecode : Array JoltInstructionRow) (layout : BytecodeLayout bytecode)
    (i j : Fin bytecode.size) (adjacent : j.val = i.val + 1)
    (continues : bytecode[i].continues = true) :
    source_is_compressed bytecode i = source_is_compressed bytecode j := by
  have next := layout.next i j adjacent continues
  have nonzero : bytecode[i].virtual_sequence_remaining.getD 0 ≠ 0 := by
    simpa only [JoltInstructionRow.continues, bne_iff_ne] using continues
  have positive : (1 : BitVec 16) ≤ bytecode[i].virtual_sequence_remaining.getD 0 := by
    rw [BitVec.le_def]
    have := BitVec.toNat_ne_iff_ne.mpr nonzero
    have oneNat : (1 : BitVec 16).toNat = 1 := rfl
    have zeroNat : (0 : BitVec 16).toNat = 0 := rfl
    omega
  have stepCount :
      (bytecode[j].virtual_sequence_remaining.getD 0).toNat + 1 =
        (bytecode[i].virtual_sequence_remaining.getD 0).toNat := by
    rw [next.2.1, Option.getD_some, BitVec.toNat_sub_of_le positive]
    have oneNat : (1 : BitVec 16).toNat = 1 := rfl
    have positiveNat : 1 ≤ (bytecode[i].virtual_sequence_remaining.getD 0).toNat := by
      simpa [BitVec.le_def] using positive
    omega
  have sameEnd :
      i.val + (bytecode[i].virtual_sequence_remaining.getD 0).toNat =
        j.val + (bytecode[j].virtual_sequence_remaining.getD 0).toNat := by omega
  unfold source_is_compressed
  simpa only [Fin.getElem_fin] using congrArg
    (fun position => (bytecode[position]?.map (·.is_compressed)).getD false) sameEnd

/-- Every row of an untrusted-answer run begins with nextPC prepared to the
source address plus its full 2-byte or 4-byte length. For example, an interior
row of a compressed expansion still starts with address + 2.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
theorem untrusted_row_next_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) :
    run.rows[i].preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[run.rows[i].rowIndex].address +
        if source_is_compressed run.bytecode run.rows[i].rowIndex then 2 else 4) := by
  have layout := expand_program_layout joltInstance.program run.bytecode run.expands
  have all (n : Nat) (bound : n < run.rows.size) :
      run.rows[n].preState.sail.regs.get? Register.nextPC =
        some (run.bytecode[run.rows[n].rowIndex].address +
          if source_is_compressed run.bytecode run.rows[n].rowIndex then 2 else 4) := by
    induction n with
    | zero =>
        obtain ⟨entry, _, prepared⟩ :=
          run.starts run.rows[0] (Array.getElem?_eq_getElem bound)
        rw [prepared]
        simp only [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq,
          ↓reduceDIte, cast_eq]
        rw [entry]
    | succ n ih =>
        have beforeBound : n < run.rows.size := by omega
        have link := run.linked n run.rows[n] run.rows[n + 1]
          (Array.getElem?_eq_getElem beforeBound)
          (Array.getElem?_eq_getElem bound)
        split at link
        · rename_i continues
          have continuesFlag : run.bytecode[run.rows[n].rowIndex].continues = true := by
            simpa [JoltInstructionRow.continues, bne_iff_ne] using continues
          have sameAddress := (layout.next run.rows[n].rowIndex
            run.rows[n + 1].rowIndex link.1 continuesFlag).1
          have sameCompression := source_compressed_next run.bytecode layout
            run.rows[n].rowIndex run.rows[n + 1].rowIndex link.1 continuesFlag
          have rowOk := ExpansionRows.expand_program_rowOk joltInstance.program
            run.bytecode run.expands run.bytecode[run.rows[n].rowIndex]
            (Array.getElem_mem_toList run.rows[n].rowIndex.isLt)
          have ordinaryRow := rowOk.ordinaryIfContinues continuesFlag
          have actualOrdinary := ExpansionRows.ordinary_withRuntimeAdvice
            run.bytecode[run.rows[n].rowIndex].instruction
            run.rows[n].runtimeAdvice ordinaryRow
          have kept := ordinary_tape_next_pc
            (run.bytecode[run.rows[n].rowIndex].instruction.withRuntimeAdvice
              run.rows[n].runtimeAdvice) (run.answers ⟨n, beforeBound⟩)
            run.rows[n].preState run.rows[n].postState actualOrdinary
            (run.executes ⟨n, beforeBound⟩)
          rw [link.2, sameAddress, ← sameCompression]
          exact kept.trans (ih beforeBound)
        · obtain ⟨address, _, sourceAddress, _, prepared⟩ := link
          rw [prepared]
          simp only [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq,
            ↓reduceDIte, cast_eq]
          rw [sourceAddress]
  exact all i.val i.isLt

/-- Runtime advice changes only the value carried by VirtualAdvice, so it
preserves both control flags. For example, patched DIV advice remains ordinary.
See jolt/tracer/src/instruction/mod.rs:215-241 at 8bbb2357. -/
private theorem control_flags_with_runtime_advice
    (instruction : JoltISA.Instr) (advice : instruction.RuntimeAdvice) :
    JoltMetadata.opcodeFlag (instruction.withRuntimeAdvice advice) .Jump =
        JoltMetadata.opcodeFlag instruction .Jump ∧
      JoltMetadata.instructionFlag (instruction.withRuntimeAdvice advice) .Branch =
        JoltMetadata.instructionFlag instruction .Branch := by
  cases instruction <;> exact ⟨rfl, rfl⟩

/-- Any executed row outside JAL, JALR and branch control flow leaves nextPC
at its source address plus its 2-byte or 4-byte source instruction length.
For example, an interior row of a compressed expansion retains address + 2.
See jolt/tracer/src/emulator/cpu.rs:622-632 at 8bbb2357. -/
theorem noncontrol_next_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size)
    (notJal : ¬ ∃ dst imm,
      run.bytecode[run.rows[i].rowIndex].instruction = .JAL dst imm)
    (notJalr : ¬ ∃ dst base imm,
      run.bytecode[run.rows[i].rowIndex].instruction = .JALR dst base imm)
    (notBranch : JoltMetadata.instructionFlag
      run.bytecode[run.rows[i].rowIndex].instruction .Branch = false) :
    run.rows[i].postState.sail.regs.get? Register.nextPC =
      some (run.bytecode[run.rows[i].rowIndex].address +
        if source_is_compressed run.bytecode run.rows[i].rowIndex then 2 else 4) := by
  have noJump : JoltMetadata.opcodeFlag
      run.bytecode[run.rows[i].rowIndex].instruction .Jump = false := by
    change (match run.bytecode[run.rows[i].rowIndex].instruction with
      | .JAL _ _ | .JALR _ _ _ => true
      | _ => false) = false
    split
    · rename_i dst imm jump
      exact False.elim (notJal ⟨dst, imm, jump⟩)
    · rename_i dst base imm jump
      exact False.elim (notJalr ⟨dst, base, imm, jump⟩)
    · rfl
  have flags := control_flags_with_runtime_advice
    run.bytecode[run.rows[i].rowIndex].instruction run.rows[i].runtimeAdvice
  have kept := noncontrol_tape_next_pc
    (run.bytecode[run.rows[i].rowIndex].instruction.withRuntimeAdvice
      run.rows[i].runtimeAdvice) (run.answers i)
    run.rows[i].preState run.rows[i].postState
    (by simpa only [flags.1] using noJump)
    (by simpa only [flags.2] using notBranch)
    (run.executes i)
  exact kept.trans (untrusted_row_next_pc joltInstance privateInputs run i)

/-- An executed final JAL that stably stalls has offset zero. For example,
the SDK's `j .` row is a `JAL +0` at its own address.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
private theorem stall_executed_jal_immediate_zero
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JAL dst imm) : imm = 0 := by
  obtain ⟨lastIndex, lastRow⟩ :=
    stall_last_run_index joltInstance privateInputs run last atEnd
  have pc : last.preState.sail.regs.get? Register.PC =
      some run.bytecode[last.rowIndex].address := by
    simpa only [lastRow] using
      untrusted_row_pc joltInstance privateInputs run lastIndex
  have nextPC : last.preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[last.rowIndex].address +
        if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
    simpa only [lastRow] using
      untrusted_row_next_pc joltInstance privateInputs run lastIndex
  have jalRuns : JoltISA.execInstr (.JAL dst imm) last.preState =
      .ok RETIRE_SUCCESS last.postState := by
    have instrEq : run.bytecode[run.rows[lastIndex].rowIndex].instruction =
        .JAL dst imm := by simpa only [lastRow] using jump
    have noAdvice :
        run.bytecode[run.rows[lastIndex].rowIndex].instruction.withRuntimeAdvice
          run.rows[lastIndex].runtimeAdvice =
        run.bytecode[run.rows[lastIndex].rowIndex].instruction :=
      JoltConstraints.Soundness.withRuntimeAdvice_eq_of_noAdvice _ _
        (by rw [instrEq]; rfl)
    have executed := run.executes lastIndex
    rw [noAdvice] at executed
    rw [instrEq] at executed
    simpa only [lastRow, JoltConstraints.Soundness.execWithTapeAnswer] using executed
  exact stall_jal_immediate_zero dst imm run.bytecode[last.rowIndex].address
    (run.bytecode[last.rowIndex].address +
      if source_is_compressed run.bytecode last.rowIndex then 2 else 4)
    last.preState last.postState pc nextPC jalRuns stable.2.1

/-- A selected interior virtual row selects the following bytecode row of the
same source on the next cycle. For example, the first ECALL row is followed by
another row stamped with ECALL's address.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 at 8bbb2357. -/
theorem stall_next_cycle_of_remaining
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program joltInstance.program = some bytecode)
    (bytecodeEq : bytecode = context.bytecode)
    (sourceAddress : BitVec 64)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowAt : JoltConstraints.bytecodeRow bytecode slot.val = some row)
    (sameSource : row.address = sourceAddress)
    (index : Fin bytecode.size)
    (slotIs : slot.val = index.val + 1)
    (rowIs : row = bytecode[index])
    (remaining : bytecode[index].virtual_sequence_remaining.getD 0 ≠ 0) :
    ∃ (nextSlot : Fin (2 ^ params.logBytecodeK)) (nextRow : JoltInstructionRow),
      JoltConstraints.bytecodeRa witness nextSlot ⟨cycle.val + 1, next⟩ = 1 ∧
      JoltConstraints.bytecodeRow bytecode nextSlot.val = some nextRow ∧
      nextRow.address = sourceAddress := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have layout := expand_program_layout joltInstance.program bytecode expanded
  have nextIndexBound : index.val + 1 < bytecode.size := by
    have endBound := layout.endInBounds index
    have positive : 0 < (bytecode[index].virtual_sequence_remaining.getD 0).toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr remaining)
    omega
  let nextIndex : Fin bytecode.size := ⟨index.val + 1, nextIndexBound⟩
  have continuesFlag : bytecode[index].continues = true := by
    simpa [JoltInstructionRow.continues, bne_iff_ne] using remaining
  have sameNext := (layout.next index nextIndex rfl continuesFlag).1
  have rowRemaining : row.virtual_sequence_remaining.getD 0 ≠ 0 := by
    rw [rowIs]
    exact remaining
  have rowAtContext : JoltConstraints.bytecodeRow context.bytecode slot.val = some row := by
    simpa only [← bytecodeEq] using rowAt
  obtain ⟨nextSlot, nextSelected, nextSlotIs⟩ :=
    JoltConstraints.Soundness.selected_next_of_remaining charAbove2pow127
      context equations cycle next slot selected rowAtContext rowRemaining
  have nextRowAt : JoltConstraints.bytecodeRow bytecode nextSlot.val =
      some bytecode[nextIndex] := by
    rw [nextSlotIs, slotIs]
    simp [JoltConstraints.bytecodeRow, nextIndex,
      Array.getElem?_eq_getElem nextIndexBound]
  refine ⟨nextSlot, bytecode[nextIndex], nextSelected, nextRowAt, ?_⟩
  calc
    bytecode[nextIndex].address = bytecode[index].address := sameNext
    _ = row.address := by rw [rowIs]
    _ = sourceAddress := sameSource

/-- A real JAL replay advances to another row of the same source, or to
padding. For example, EBREAK's `JAL +0` returns to its own source address.
See jolt/crates/jolt-program/src/expand/control_flow/ebreak.rs:1-20
at 8bbb2357. -/
theorem stall_jal_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JAL dst imm)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  have offsetZero : imm = 0 :=
    stall_executed_jal_immediate_zero joltInstance privateInputs run last atEnd
      stable dst imm jump
  rcases atCycle with padding | ⟨slot, row, selected, rowAt, sameSource, _⟩
  · exact False.elim (real padding)
  obtain ⟨accepted, rowAtContext, index, slotIs, rowIs⟩ :=
    stall_cycle_selected_row joltInstance privateInputs context run.bytecode
      bytecodeEq slot row rowAt
  by_cases continues : run.bytecode[index].virtual_sequence_remaining.getD 0 ≠ 0
  · obtain ⟨nextSlot, nextRow, nextSelected, nextRowAt, nextAddress⟩ :=
      stall_next_cycle_of_remaining joltField joltInstance privateInputs witness
        context equations run.bytecode run.expands bytecodeEq
        run.bytecode[last.rowIndex].address cycle next slot selected row rowAt
        sameSource index slotIs rowIs continues
    exact Or.inr ⟨nextSlot, nextRow, nextSelected, nextRowAt,
      nextAddress, by rw [jump]; trivial⟩
  · have lastCount := stable.1
    have indexZero : run.bytecode[index].virtual_sequence_remaining.getD 0 = 0 := by
      by_contra nonzero
      exact continues nonzero
    have indexEq : index.val = last.rowIndex.val :=
      expand_program_unique joltInstance.program run.bytecode run.expands accepted
        index.val last.rowIndex.val index.isLt last.rowIndex.isLt
        (by simpa only [rowIs] using sameSource)
        (by simpa only [Fin.getElem_fin] using indexZero.trans lastCount.symm)
    have sameIndex : index = last.rowIndex := Fin.ext indexEq
    have currentJump : row.instruction = .JAL dst imm := by
      rw [rowIs, sameIndex]
      exact jump
    by_cases nextPadding :
        witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 1
    · exact Or.inl nextPadding
    · have target := stall_jal_next_target joltField joltInstance privateInputs
        witness context equations cycle next slot selected row rowAtContext dst imm
          currentJump nextPadding
      have targetAddress : witness.NextUnexpandedPC cycle =
          (run.bytecode[last.rowIndex].address.toNat : F) := by
        simpa only [offsetZero, add_zero, sameSource] using target
      rcases stall_next_cycle_of_target joltField joltInstance privateInputs
        witness context equations cycle next run.bytecode[last.rowIndex].address
          targetAddress with
        isPadding | ⟨nextSlot, nextRow, nextSelected, nextRowAt, nextAddress⟩
      · exact False.elim (nextPadding isPadding)
      · have nextRowAtRun : JoltConstraints.bytecodeRow run.bytecode nextSlot.val =
            some nextRow := by rw [bytecodeEq]; exact nextRowAt
        exact Or.inr ⟨nextSlot, nextRow, nextSelected, nextRowAtRun,
          nextAddress, by simp only [jump]⟩

/-- A source with a branch row emits only that native row; no expanded
sequence emits a branch. For example, a BEQ source emits one BEQ row.
See jolt/crates/jolt-program/src/expand/mod.rs:281-307 at 8bbb2357. -/
private theorem expanded_branch_source_singleton
    (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow)
    (expanded : expand_instruction source = some rows)
    (branchRow : JoltInstructionRow) (member : branchRow ∈ rows)
    (branch : JoltMetadata.instructionFlag branchRow.instruction .Branch = true) :
    rows = [branchRow] := by
  unfold expand_instruction at expanded
  split at expanded
  · cases expanded
  · rename_i instruction native
    cases expanded
    simp only [List.mem_singleton] at member
    simp only [member]
  · split at expanded
    · cases expanded
    · rename_i instructions sequence _
      cases expanded
      obtain ⟨k, inRange, rowAt⟩ := List.mem_iff_getElem.mp member
      have indexBound : k < instructions.length := by
        simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using inRange
      have ok := ExpansionFacts.expand_ok _ _ sequence
      have rowsOk : ExpansionFacts.rowsOk instructions = true := by
        change (ExpansionFacts.rowsOk instructions &&
          ExpansionFacts.shiftsOk instructions &&
          ExpansionTempLiveness.tempsReadAfterWrite instructions) = true at ok
        simp only [Bool.and_eq_true] at ok
        exact ok.1.1
      have rowOk := (ExpansionRows.rowsOk_rows instructions rowsOk k indexBound).1
      have noBranch : JoltMetadata.instructionFlag instructions[k] .Branch = false := by
        simp only [ExpansionFacts.sequenceRowOk, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true] at rowOk
        exact rowOk.1.1.2
      have sameInstr : branchRow.instruction = instructions[k] := by
        rw [← rowAt]
        simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx]
      rw [sameInstr, noBranch] at branch
      cases branch

/-- At an accepted address whose final row is a branch, every selected row
is that branch row. For example, every real row at a BEQ address is the BEQ.
See jolt/crates/jolt-program/src/expand/mod.rs:281-307 at 8bbb2357. -/
private theorem expanded_branch_same_address
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (lastIndex : Fin bytecode.size)
    (branch : JoltMetadata.instructionFlag bytecode[lastIndex].instruction .Branch = true)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (sameAddress : row.address = bytecode[lastIndex].address) :
    row = bytecode[lastIndex] := by
  obtain ⟨source, _, rows, expands, rowIn, lastIn⟩ :=
    expanded_same_source_rows image bytecode expanded accepted
      row bytecode[lastIndex] member
      (Array.getElem_mem_toList lastIndex.isLt) sameAddress
  have singleton := expanded_branch_source_singleton source rows expands
    bytecode[lastIndex] lastIn branch
  rw [singleton] at rowIn
  simpa only [List.mem_singleton] using rowIn

/-- The final represented branch executes the bytecode branch directly;
runtime advice never changes a branch. For example, a BEQ run uses its BEQ
row rather than a tape answer. See jolt/tracer/src/emulator/cpu.rs:622-632
at 8bbb2357. -/
private theorem stall_branch_runs
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (branch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true) :
    JoltISA.execInstr run.bytecode[last.rowIndex].instruction last.preState =
      .ok RETIRE_SUCCESS last.postState := by
  obtain ⟨lastIndex, lastRow⟩ :=
    stall_last_run_index joltInstance privateInputs run last atEnd
  obtain ⟨lhs, rhs, imm, isBranch⟩ :=
    stall_branch_shape run.bytecode[last.rowIndex].instruction branch
  have instrEq : run.bytecode[run.rows[lastIndex].rowIndex].instruction =
      run.bytecode[last.rowIndex].instruction := by simp only [lastRow]
  have noAdvice :
      run.bytecode[run.rows[lastIndex].rowIndex].instruction.withRuntimeAdvice
        run.rows[lastIndex].runtimeAdvice =
      run.bytecode[run.rows[lastIndex].rowIndex].instruction := by
    apply JoltConstraints.Soundness.withRuntimeAdvice_eq_of_noAdvice
    rw [instrEq]
    rcases isBranch with h | h | h | h | h | h
    all_goals rw [h]; rfl
  have executed := run.executes lastIndex
  rw [noAdvice, instrEq] at executed
  have executedLast : JoltConstraints.Soundness.execWithTapeAnswer
      run.bytecode[last.rowIndex].instruction (run.answers lastIndex)
      last.preState = .ok RETIRE_SUCCESS last.postState := by
    simpa only [lastRow] using executed
  rcases isBranch with h | h | h | h | h | h
  all_goals simpa only [h, JoltConstraints.Soundness.execWithTapeAnswer] using executedLast

/-- A branch that executed and then stably stalled was taken with zero signed
offset. For example, a taken `BEQ x1, x1, 0` repeats its own address.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
private theorem stall_branch_model_target
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (accepted : pc_map_ok run.bytecode = true)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (branch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true) :
    JoltNextPCFrame.BranchTaken run.bytecode[last.rowIndex].instruction
      last.preState = true ∧
    JoltMetadata.immediate run.bytecode[last.rowIndex].instruction = 0 := by
  obtain ⟨lastIndex, lastRow⟩ :=
    stall_last_run_index joltInstance privateInputs run last atEnd
  obtain ⟨lhs, rhs, imm, isBranch⟩ :=
    stall_branch_shape run.bytecode[last.rowIndex].instruction branch
  have pc : last.preState.sail.regs.get? Register.PC =
      some run.bytecode[last.rowIndex].address := by
    simpa only [lastRow] using
      untrusted_row_pc joltInstance privateInputs run lastIndex
  have prepared : last.preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[last.rowIndex].address +
        if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
    simpa only [lastRow] using
      untrusted_row_next_pc joltInstance privateInputs run lastIndex
  have runs := stall_branch_runs joltInstance privateInputs run last atEnd branch
  have taken : JoltNextPCFrame.BranchTaken
      run.bytecode[last.rowIndex].instruction last.preState = true := by
    cases decision : JoltNextPCFrame.BranchTaken
      run.bytecode[last.rowIndex].instruction last.preState with
    | true => rfl
    | false =>
        have sameState := JoltNextPCFrame.branch_not_taken _ _ _ branch decision runs
        have equalNext : run.bytecode[last.rowIndex].address +
            (if source_is_compressed run.bytecode last.rowIndex then 2 else 4) =
            run.bytecode[last.rowIndex].address := by
          have postAt := stable.2.1
          rw [sameState] at postAt
          exact Option.some.inj (prepared.symm.trans
            postAt)
        have zeroLength := add_eq_left.mp equalNext
        cases h : source_is_compressed run.bytecode last.rowIndex <;>
          simp [h] at zeroLength
  refine ⟨taken, ?_⟩
  have valid := (expand_program_rows_valid joltInstance.program run.bytecode run.expands).rowValid
    last.rowIndex
  obtain ⟨_, offset, offsetEq⟩ := valid.branch isBranch
  have target := JoltConstraints.execInstr_branch_target _ lhs rhs imm isBranch
    last.preState last.postState run.bytecode[last.rowIndex].address taken pc runs
  have sameTarget : run.bytecode[last.rowIndex].address + imm.setWidth 64 =
      run.bytecode[last.rowIndex].address := Option.some.inj (target.symm.trans stable.2.1)
  have addressOk := pc_map_ok_addresses run.bytecode accepted last.rowIndex.val
    last.rowIndex.isLt
  have ram : JoltISA.RAM_START_ADDRESS ≤
      run.bytecode[last.rowIndex].address.toNat := by
    simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at addressOk
    simpa only [Fin.getElem_fin] using addressOk.1
  have targetNat := JoltConstraints.branch_target_toNat
    run.bytecode[last.rowIndex].address offset ram (by
      simpa only [← offsetEq, sameTarget] using ram)
  have offsetIntZero : (offset.signExtend 128).toInt = 0 := by
    have sameOffset : run.bytecode[last.rowIndex].address +
        (offset.signExtend 128).setWidth 64 =
        run.bytecode[last.rowIndex].address := by
      simpa only [← offsetEq] using sameTarget
    rw [sameOffset] at targetNat
    omega
  rcases isBranch with h | h | h | h | h | h
  all_goals
    rw [h]
    change imm.toInt = 0
    rw [offsetEq]
    exact offsetIntZero

/-- When the selected branch has the same operands as the stable stall, the
branch constraint keeps the witness at that source address. For example,
selected `BEQ x1, x1, 0` targets its own address.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:337-347
at 8bbb2357. -/
private theorem stall_branch_witness_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    (lhs rhs : BitVec 64)
    (rs1 : witness.Rs1Value cycle = (lhs.toNat : F))
    (rs2 : witness.Rs2Value cycle = (rhs.toNat : F))
    (taken : JoltISA.branchDecisionPure row.instruction lhs rhs = true)
    (zeroImm : JoltMetadata.immediate row.instruction = 0) :
    witness.NextUnexpandedPC cycle = (row.address.toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have lookup := stall_branch_lookup_decision joltField joltInstance privateInputs
    witness context equations cycle slot selected row present branch lhs rhs rs1 rs2
  simp only [taken, ↓reduceIte] at lookup
  have branchFlag : witness.InstructionFlags .Branch cycle = 1 := by
    simpa [JoltConstraints.bytecodeInstructionFlag, present, branch] using
      JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
        charAbove2pow127 context equations .Branch cycle slot selected
  have shouldBranch : witness.ShouldBranch cycle = 1 := by
    rw [equations.shouldBranchEqLookupOutputMulBranch cycle, lookup, branchFlag]
    ring
  have relation := equations.nextUnexpandedPCEqPCPlusImmIfShouldBranch cycle
  rw [shouldBranch, one_mul] at relation
  have address : witness.UnexpandedPC cycle = (row.address.toNat : F) := by
    simpa [JoltConstraints.bytecodeAddress, present] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  have immediate : witness.Imm cycle = 0 := by
    simpa [JoltConstraints.bytecodeImmediate, present, zeroImm] using
      JoltConstraints.Soundness.imm_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  rw [address, immediate] at relation
  exact sub_eq_zero.mp (by simpa only [sub_zero] using relation)

/-- The two branch controls in the suffix invariant supply the source's
original operands. For example, a replayed BEQ keeps both compared registers.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
private theorem stall_branch_control_values
    {F : Type} [Field F]
    {params : WitnessParams} (witness : WitnessType F params)
    (bytecode : Array JoltInstructionRow) (last : TraceRow bytecode)
    (cycle : Fin params.traceLength)
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shape : bytecode[last.rowIndex].instruction = .BEQ lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BNE lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BLT lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BGE lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BLTU lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BGEU lhs rhs imm)
    (controls :
      let readAtStall (src : JoltISA.Src) : Prop :=
        witness.RegistersVal (TraceWitness.sourceRegisterAddress src) cycle =
          ((JoltISA.sourceValue src last.preState).toNat : F)
      match bytecode[last.rowIndex].instruction with
      | .JALR dst base _ =>
          witness.RegistersVal (TraceWitness.sourceRegisterAddress base) cycle =
            ((JoltISA.sourceValue base
              (if TraceWitness.destinationRegisterAddress dst =
                    TraceWitness.sourceRegisterAddress base ∧
                  (TraceWitness.sourceRegisterAddress base).val ≠ 0 then
                last.postState else last.preState)).toNat : F)
      | .BEQ left right _ | .BNE left right _ | .BLT left right _
      | .BGE left right _ | .BLTU left right _ | .BGEU left right _ =>
          readAtStall left ∧ readAtStall right
      | _ => True) :
    witness.RegistersVal (TraceWitness.sourceRegisterAddress lhs) cycle =
        ((JoltISA.sourceValue lhs last.preState).toNat : F) ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress rhs) cycle =
        ((JoltISA.sourceValue rhs last.preState).toNat : F) := by
  rcases shape with h | h | h | h | h | h
  all_goals simpa only [h] using controls

/-- A branch writes neither control register, so the next cycle keeps both
values from the stable row. For example, BEQ leaves both compared registers
unchanged. See jolt/crates/jolt-riscv/src/instructions/b/beq.rs:1-35
at 8bbb2357. -/
private theorem stall_branch_controls_succ
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (bytecode : Array JoltInstructionRow) (last : TraceRow bytecode)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shape : bytecode[last.rowIndex].instruction = .BEQ lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BNE lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BLT lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BGE lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BLTU lhs rhs imm ∨
      bytecode[last.rowIndex].instruction = .BGEU lhs rhs imm)
    (current : row = bytecode[last.rowIndex])
    (values :
      witness.RegistersVal (TraceWitness.sourceRegisterAddress lhs) cycle =
          ((JoltISA.sourceValue lhs last.preState).toNat : F) ∧
        witness.RegistersVal (TraceWitness.sourceRegisterAddress rhs) cycle =
          ((JoltISA.sourceValue rhs last.preState).toNat : F)) :
    let readAtStall (src : JoltISA.Src) : Prop :=
      witness.RegistersVal (TraceWitness.sourceRegisterAddress src)
        ⟨cycle.val + 1, next⟩ =
          ((JoltISA.sourceValue src last.preState).toNat : F)
    match bytecode[last.rowIndex].instruction with
    | .JALR dst base _ =>
        witness.RegistersVal (TraceWitness.sourceRegisterAddress base)
          ⟨cycle.val + 1, next⟩ =
          ((JoltISA.sourceValue base
            (if TraceWitness.destinationRegisterAddress dst =
                  TraceWitness.sourceRegisterAddress base ∧
                (TraceWitness.sourceRegisterAddress base).val ≠ 0 then
              last.postState else last.preState)).toNat : F)
    | .BEQ left right _ | .BNE left right _ | .BLT left right _
    | .BGE left right _ | .BLTU left right _ | .BGEU left right _ =>
        readAtStall left ∧ readAtStall right
    | _ => True := by
  have noDestination : JoltConstraints.bytecodeRdRegister row.instruction = none := by
    rw [current]
    rcases shape with h | h | h | h | h | h
    all_goals rw [h]; rfl
  have nextLhs := register_unchanged_of_no_write joltField joltInstance
    privateInputs witness context equations cycle next slot selected row present
      (TraceWitness.sourceRegisterAddress lhs) (by simp [noDestination])
  have nextRhs := register_unchanged_of_no_write joltField joltInstance
    privateInputs witness context equations cycle next slot selected row present
      (TraceWitness.sourceRegisterAddress rhs) (by simp [noDestination])
  rcases shape with h | h | h | h | h | h
  all_goals
    simp only [h]
    exact ⟨nextLhs.trans values.1, nextRhs.trans values.2⟩

/-- The witness branch target at a replayed stable stall is its source
address. For example, a taken BEQ with zero offset targets its own source.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:337-347
at 8bbb2357. -/
private theorem stall_branch_replay_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (bytecode : Array JoltInstructionRow) (last : TraceRow bytecode)
    (cycle : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (current : row = bytecode[last.rowIndex])
    (branch : JoltMetadata.instructionFlag bytecode[last.rowIndex].instruction .Branch = true)
    (model : JoltNextPCFrame.BranchTaken bytecode[last.rowIndex].instruction
        last.preState = true ∧
      JoltMetadata.immediate bytecode[last.rowIndex].instruction = 0)
    (controls :
      let readAtStall (src : JoltISA.Src) : Prop :=
        witness.RegistersVal (TraceWitness.sourceRegisterAddress src) cycle =
          ((JoltISA.sourceValue src last.preState).toNat : F)
      match bytecode[last.rowIndex].instruction with
      | .JALR dst base _ =>
          witness.RegistersVal (TraceWitness.sourceRegisterAddress base) cycle =
            ((JoltISA.sourceValue base
              (if TraceWitness.destinationRegisterAddress dst =
                    TraceWitness.sourceRegisterAddress base ∧
                  (TraceWitness.sourceRegisterAddress base).val ≠ 0 then
                last.postState else last.preState)).toNat : F)
      | .BEQ left right _ | .BNE left right _ | .BLT left right _
      | .BGE left right _ | .BLTU left right _ | .BGEU left right _ =>
          readAtStall left ∧ readAtStall right
      | _ => True) :
    witness.NextUnexpandedPC cycle = (row.address.toNat : F) := by
  obtain ⟨lhs, rhs, imm, isBranch⟩ :=
    stall_branch_shape bytecode[last.rowIndex].instruction branch
  have sourceReads := stall_branch_control_values witness bytecode last cycle
    lhs rhs imm isBranch controls
  have rs1 : witness.Rs1Value cycle =
      ((JoltISA.sourceValue lhs last.preState).toNat : F) := by
    have read := selected_operand_register
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      joltInstance privateInputs witness context equations cycle slot selected row
      present false (TraceWitness.sourceRegisterAddress lhs) (by
        rw [current]
        rcases isBranch with h | h | h | h | h | h
        all_goals rw [h]; rfl)
    exact read.trans sourceReads.1
  have rs2 : witness.Rs2Value cycle =
      ((JoltISA.sourceValue rhs last.preState).toNat : F) := by
    have read := selected_operand_register
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      joltInstance privateInputs witness context equations cycle slot selected row
      present true (TraceWitness.sourceRegisterAddress rhs) (by
        rw [current]
        rcases isBranch with h | h | h | h | h | h
        all_goals rw [h]; rfl)
    exact read.trans sourceReads.2
  have taken : JoltISA.branchDecisionPure row.instruction
      (JoltISA.sourceValue lhs last.preState)
      (JoltISA.sourceValue rhs last.preState) = true := by
    rw [current]
    rcases isBranch with h | h | h | h | h | h
    all_goals simpa only [h, JoltNextPCFrame.BranchTaken] using model.1
  exact stall_branch_witness_target joltField joltInstance privateInputs
    witness context equations cycle slot selected row present
      (by rw [current]; exact branch)
      (JoltISA.sourceValue lhs last.preState)
      (JoltISA.sourceValue rhs last.preState) rs1 rs2 taken
      (by rw [current]; exact model.2)

/-- A real branch replay preserves its two control operands and advances to
the same source or padding. For example, a BEQ self jump still compares the
same registers on replay. See jolt/crates/jolt-riscv/src/row.rs:105-132
in PR #2109 head d2995380. -/
theorem stall_branch_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (branch : JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  rcases atCycle with padding | ⟨slot, row, selected, rowAt, sameSource, controls⟩
  · exact False.elim (real padding)
  obtain ⟨accepted, rowAtContext, index, _, rowIs⟩ :=
    stall_cycle_selected_row joltInstance privateInputs context run.bytecode
      bytecodeEq slot row rowAt
  have rowMember : row ∈ run.bytecode.toList := by
    rw [rowIs]
    exact Array.getElem_mem_toList index.isLt
  have currentEq : row = run.bytecode[last.rowIndex] :=
    expanded_branch_same_address joltInstance.program run.bytecode run.expands accepted
      last.rowIndex branch row rowMember sameSource
  have model := stall_branch_model_target joltInstance privateInputs run accepted
    last atEnd stable branch
  have target := stall_branch_replay_target joltField joltInstance privateInputs
    witness context equations run.bytecode last cycle slot selected row rowAtContext
    currentEq branch model controls
  rcases stall_next_cycle_of_target joltField joltInstance privateInputs
    witness context equations cycle next run.bytecode[last.rowIndex].address
      (by simpa only [sameSource] using target) with
    isPadding | ⟨nextSlot, nextRow, nextSelected, nextRowAt, nextAddress⟩
  · exact Or.inl isPadding
  · obtain ⟨lhs, rhs, imm, isBranch⟩ :=
      stall_branch_shape run.bytecode[last.rowIndex].instruction branch
    have sourceReads := stall_branch_control_values witness run.bytecode last cycle
      lhs rhs imm isBranch controls
    have nextControls :
        (let readAtStall (src : JoltISA.Src) : Prop :=
          witness.RegistersVal (TraceWitness.sourceRegisterAddress src)
            ⟨cycle.val + 1, next⟩ =
              ((JoltISA.sourceValue src last.preState).toNat : F)
         match run.bytecode[last.rowIndex].instruction with
         | .JALR dst base _ =>
             witness.RegistersVal (TraceWitness.sourceRegisterAddress base)
               ⟨cycle.val + 1, next⟩ =
               ((JoltISA.sourceValue base
                 (if TraceWitness.destinationRegisterAddress dst =
                       TraceWitness.sourceRegisterAddress base ∧
                     (TraceWitness.sourceRegisterAddress base).val ≠ 0 then
                   last.postState else last.preState)).toNat : F)
         | .BEQ left right _ | .BNE left right _ | .BLT left right _
         | .BGE left right _ | .BLTU left right _ | .BGEU left right _ =>
             readAtStall left ∧ readAtStall right
         | _ => True) :=
      stall_branch_controls_succ joltField joltInstance privateInputs witness
        context equations run.bytecode last cycle next slot selected row rowAtContext
        lhs rhs imm isBranch currentEq sourceReads
    have nextRowAtRun : JoltConstraints.bytecodeRow run.bytecode nextSlot.val =
        some nextRow := by rw [bytecodeEq]; exact nextRowAt
    exact Or.inr ⟨nextSlot, nextRow, nextSelected, nextRowAtRun,
      nextAddress, nextControls⟩

/-- An executed JALR writes its masked base-plus-immediate target to `nextPC`,
even when it also writes a link register. For example, `jalr x1, -4(x2)`
sets `nextPC` to `(x2 - 4) & ~1`.
See jolt/tracer/src/instruction/jalr.rs:19-30 at 8bbb2357. -/
private theorem tape_jalr_target
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm link answer : BitVec 64)
    (pre post : SailJoltState)
    (hnext : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltConstraints.Soundness.execWithTapeAnswer (.JALR dst base imm)
      answer pre = .ok (.Retire_Success ()) post) :
    post.sail.regs.get? Register.nextPC =
      some (jolt_jalr_target64 (JoltISA.sourceValue base pre) imm) := by
  have hreadNext : liftSail (Sail.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link hnext]
  simp only [JoltConstraints.Soundness.execWithTapeAnswer, JoltISA.execInstr,
    bind, EStateM.bind, hreadNext] at runs
  cases hread : JoltISA.readSrc base pre with
  | error err state => simp only [hread] at runs; cases runs
  | ok source state =>
    obtain ⟨hstate, hsource⟩ := lookup_readSrc_value base pre state source hread
    subst state
    subst source
    let target := jolt_jalr_target64 (JoltISA.sourceValue base pre) imm
    let afterPC : SailJoltState :=
      { pre with sail := { pre.sail with
        regs := pre.sail.regs.insert Register.nextPC target } }
    have hpcWrite : liftSail (Sail.writeReg Register.nextPC target) pre =
        .ok () afterPC := by rfl
    simp only [hread] at runs
    rw [hpcWrite] at runs
    cases hwrite : JoltISA.writeDst dst link afterPC with
    | error err state => simp only [hwrite] at runs; cases runs
    | ok result mid =>
      cases result
      simp only [hwrite, pure, EStateM.pure] at runs
      cases runs
      have hpres := JoltNextPCFrame.write_rule dst link _ _ _ hwrite
      simpa [afterPC, target] using hpres

/-- A run's final stable JALR actually targeted its source address using the
base value in its recorded pre-state. For example, a native `jalr x0, 0(x1)`
that stably stalls read an `x1` value targeting its own source.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stable_jalr_target
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR dst base imm) :
    jolt_jalr_target64 (JoltISA.sourceValue base last.preState) imm =
      run.bytecode[last.rowIndex].address := by
  have atEndEq : run.rows.back? = some last := by simpa using atEnd
  have nonempty : 0 < run.rows.size := by
    by_contra empty
    have zero : run.rows.size = 0 := by omega
    simp [Array.back?_eq_getElem?, zero] at atEndEq
  let i : Fin run.rows.size := ⟨run.rows.size - 1, by omega⟩
  have rowEq : run.rows[i] = last := by
    have back := atEndEq
    rw [Array.back?_eq_getElem?] at back
    have hsome : run.rows[i]? = some last := by simpa [i] using back
    exact Option.some.inj ((Array.getElem?_eq_getElem i.isLt).symm.trans hsome)
  have hnext : last.preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[last.rowIndex].address +
        if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
    simpa only [rowEq] using untrusted_row_next_pc joltInstance privateInputs run i
  have lastFlag :
      source_is_compressed run.bytecode last.rowIndex =
        run.bytecode[last.rowIndex].is_compressed :=
    source_compressed_of_last run.bytecode last.rowIndex stable.1
  rw [lastFlag] at hnext
  have idxEq : run.rows[i].rowIndex = last.rowIndex :=
    congrArg TraceRow.rowIndex rowEq
  have hinst : run.bytecode[run.rows[i].rowIndex].instruction =
      .JALR dst base imm := by simpa only [idxEq] using jump
  have runs := run.executes i
  rw [JoltConstraints.Soundness.withRuntimeAdvice_eq_of_noAdvice
    _ run.rows[i].runtimeAdvice (by rw [hinst]; rfl), hinst] at runs
  have actual : JoltConstraints.Soundness.execWithTapeAnswer (.JALR dst base imm)
      (run.answers i) last.preState = .ok (.Retire_Success ()) last.postState := by
    simpa only [rowEq] using runs
  have target := tape_jalr_target dst base imm
    (run.bytecode[last.rowIndex].address +
      if run.bytecode[last.rowIndex].is_compressed then 2 else 4)
    (run.answers i) last.preState last.postState hnext actual
  exact Option.some.inj (target.symm.trans stable.2.1)

/-- A final executed JALR that writes its own nonzero architectural base
leaves that base holding the source's prepared return address. For example,
`jalr x1, imm(x1)` leaves `x1` equal to its address plus its source length.
See jolt/tracer/src/instruction/jalr.rs:19-30 at 8bbb2357. -/
theorem stable_written_jalr_link
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (rd : regidx) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR (.xreg rd) (.xreg rd) imm)
    (nonzero : JoltISA.isX0 rd = false) :
    JoltISA.sourceValue (.xreg rd) last.postState =
      run.bytecode[last.rowIndex].address +
        if run.bytecode[last.rowIndex].is_compressed then 2 else 4 := by
  obtain ⟨i, rowEq⟩ := stall_last_run_index joltInstance privateInputs run last atEnd
  have prepared : last.preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[last.rowIndex].address +
        if run.bytecode[last.rowIndex].is_compressed then 2 else 4) := by
    have nextPC : last.preState.sail.regs.get? Register.nextPC =
        some (run.bytecode[last.rowIndex].address +
          if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
      simpa only [rowEq] using untrusted_row_next_pc joltInstance privateInputs run i
    rw [source_compressed_of_last run.bytecode last.rowIndex stable.1] at nextPC
    exact nextPC
  have idxEq : run.rows[i].rowIndex = last.rowIndex :=
    congrArg TraceRow.rowIndex rowEq
  have hinst : run.bytecode[run.rows[i].rowIndex].instruction =
      .JALR (.xreg rd) (.xreg rd) imm := by simpa only [idxEq] using jump
  have runs := run.executes i
  rw [JoltConstraints.Soundness.withRuntimeAdvice_eq_of_noAdvice
    _ run.rows[i].runtimeAdvice (by rw [hinst]; rfl), hinst] at runs
  have executed : JoltISA.execInstr (.JALR (.xreg rd) (.xreg rd) imm)
      last.preState = .ok (.Retire_Success ()) last.postState := by
    simpa only [rowEq, JoltConstraints.Soundness.execWithTapeAnswer] using runs
  have link := jump_jalr_link (.xreg rd) (.xreg rd) imm
    (run.bytecode[last.rowIndex].address +
      if run.bytecode[last.rowIndex].is_compressed then 2 else 4)
    last.preState last.postState nonzero prepared executed
  simpa only [TraceWitness.capturedDestinationValue,
    TraceWitness.capturedDestination] using link

/-- An architectural register index does not compare unequal to itself; for
example, the repeated base in `jalr x1, imm(x1)` is the same index.
See PR #2109 head d2995380, jolt/crates/jolt-riscv/src/row.rs:105-132. -/
private theorem regidx_bne_self_false (rd : regidx) : (rd != rd) = false := by
  cases rd with
  | Regidx bits =>
    change (!(bits == bits)) = false
    rw [beq_self_eq_true bits]
    rfl

/-- For a stable JALR that overwrites its own nonzero base, the stored link
targets the same source on replay. For example, `jalr x1, imm(x1)` is stable
only when applying its immediate to its new `x1` returns its address.
See PR #2109 head d2995380,
jolt/crates/jolt-riscv/src/row.rs:105-132. -/
theorem stable_written_jalr_replay_target
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (rd : regidx) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR (.xreg rd) (.xreg rd) imm)
    (nonzero : JoltISA.isX0 rd = false) :
    jolt_jalr_target64 (JoltISA.sourceValue (.xreg rd) last.postState) imm =
      run.bytecode[last.rowIndex].address := by
  rw [stable_written_jalr_link joltInstance privateInputs run last atEnd
    stable rd imm jump nonzero]
  have repeats := stable.2.2
  unfold JoltInstructionRow.selfJumpRepeats at repeats
  rw [jump] at repeats
  change (if (JoltISA.isX0 rd || rd != rd) = true then true else
    jolt_jalr_target64
      (run.bytecode[last.rowIndex].address +
        if run.bytecode[last.rowIndex].is_compressed then 2 else 4) imm ==
          run.bytecode[last.rowIndex].address) = true at repeats
  rw [nonzero, regidx_bne_self_false] at repeats
  simpa only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] using repeats

/-- For canonical operands, equal register-table addresses mean that a JALR
destination and base name the same register. For example, `x1` and `x1`
share an address, while a virtual temporary and architectural `x1` do not.
See jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20
at 8bbb2357. -/
theorem jalr_destination_base_address_eq_iff
    (dst : JoltISA.Dst) (base : JoltISA.Src)
    (canonicalDst : JoltRegisterEncoding.destinationIsCanonical dst = true)
    (canonicalBase : JoltRegisterEncoding.sourceIsCanonical base = true) :
    TraceWitness.destinationRegisterAddress dst =
      TraceWitness.sourceRegisterAddress base ↔
    JoltConstraints.Soundness.destinationSource dst = base := by
  have canonicalDstSource :
      JoltRegisterEncoding.sourceIsCanonical
        (JoltConstraints.Soundness.destinationSource dst) = true := by
    cases dst <;> simpa [JoltConstraints.Soundness.destinationSource,
      JoltRegisterEncoding.sourceIsCanonical,
      JoltRegisterEncoding.destinationIsCanonical] using canonicalDst
  have sameEncoding : TraceWitness.sourceRegisterAddress
      (JoltConstraints.Soundness.destinationSource dst) =
      TraceWitness.destinationRegisterAddress dst := by
    cases dst <;> rfl
  constructor
  · intro same
    exact JoltConstraints.Soundness.sourceRegisterAddress_injective
      canonicalDstSource canonicalBase (sameEncoding.trans same)
  · intro same
    rw [← same, ← sameEncoding]

/-- A selected JALR's aligned lookup output is its 64-bit base-plus-immediate
target. For example, a base of `0x1003` and immediate zero yields `0x1002`.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/jalr.rs:29-33
at 8bbb2357. -/
theorem selected_jalr_lookup_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm value : BitVec 64)
    (jump : row.instruction = .JALR dst base imm)
    (baseAt : witness.RegistersVal (TraceWitness.sourceRegisterAddress base) cycle =
      (value.toNat : F)) :
    witness.LookupOutput cycle = ((jolt_jalr_target64 value imm).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have read := selected_operand_register charAbove2pow127 joltInstance
    privateInputs witness context equations cycle slot selected row present false
    (TraceWitness.sourceRegisterAddress base) (by simp [jump, JoltConstraints.bytecodeRs1Register])
  have rs1 : witness.Rs1Value cycle = (value.toNat : F) := read.trans baseAt
  have immediate : witness.Imm cycle = (imm.toNat : F) := by
    simpa [JoltConstraints.bytecodeImmediate, present, jump, JoltMetadata.immediate] using
      JoltConstraints.Soundness.imm_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  have inputs := JoltConstraints.Soundness.instructionInputs_of_selected_bytecode
    charAbove2pow127 context equations cycle slot selected row present
  have left : witness.LeftInstructionInput cycle = (value.toNat : F) := by
    simpa [jump, JoltMetadata.instructionFlag, rs1] using inputs.1
  have right : witness.RightInstructionInput cycle = (imm.toNat : F) := by
    simpa [jump, JoltMetadata.instructionFlag, immediate] using inputs.2
  have active : witness.OpFlags .AddOperands cycle = 1 := by
    simpa [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, jump] using
      JoltConstraints.Soundness.opFlag_of_selected_bytecode
        charAbove2pow127 context equations .AddOperands cycle slot selected
  have raf := JoltConstraints.Soundness.instructionRafFlag_one_of_arithmetic
    charAbove2pow127 context equations cycle (Or.inl active)
  have encoded := JoltConstraints.Soundness.rightLookupOperand_add
    equations.rightLookupAdd cycle active value imm left right
  have table : (JoltConstraints.bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) =
        some .RangeCheckAligned := by
    simp [present, jump, JoltMetadata.lookupTable]
  have output := JoltConstraints.Soundness.lookupOutput_rangeCheckAligned_of_identity
    joltField context equations cycle slot selected _ raf encoded table
  simpa [jolt_jalr_target64, Sail.BitVec.update,
    Sail.BitVec.updateSubrange', BitVec.and_comm,
    BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output

/-- A selected JALR followed by a real cycle places its aligned lookup target
in the next unexpanded PC. For example, a stable `jalr x0, 0(x1)` selects its
own source address as the next unexpanded PC.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:344-352
at 8bbb2357. -/
theorem selected_jalr_next_target
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm value : BitVec 64)
    (jump : row.instruction = .JALR dst base imm)
    (baseAt : witness.RegistersVal (TraceWitness.sourceRegisterAddress base) cycle =
      (value.toNat : F))
    (nextReal : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1) :
    witness.NextUnexpandedPC cycle = ((jolt_jalr_target64 value imm).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have jumpFlag : witness.OpFlags .Jump cycle = 1 := by
    simpa [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, jump] using
      JoltConstraints.Soundness.opFlag_of_selected_bytecode
        charAbove2pow127 context equations .Jump cycle slot selected
  have nextNoop : witness.NextIsNoop cycle = 0 := by
    have shifted := equations.nextIsNoopEqShift cycle
    simp only [dif_pos next] at shifted
    obtain ⟨nextSlot, nextSelected, _⟩ :=
      JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations
        ⟨cycle.val + 1, next⟩
    have flag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
      charAbove2pow127 context equations .IsNoop ⟨cycle.val + 1, next⟩
        nextSlot nextSelected
    cases presentNext : JoltConstraints.bytecodeRow context.bytecode nextSlot.val with
    | none =>
        simp [JoltConstraints.bytecodeInstructionFlag, presentNext] at flag
        exact False.elim (nextReal flag)
    | some nextRow =>
        simp [JoltConstraints.bytecodeInstructionFlag, presentNext,
          JoltMetadata.instructionFlag] at flag
        exact shifted.trans flag
  have shouldJump : witness.ShouldJump cycle = 1 := by
    rw [equations.shouldJumpEqJumpMulNotNextIsNoop cycle, jumpFlag, nextNoop]
    ring
  have relation := equations.nextUnexpandedPCEqLookupIfShouldJump cycle
  rw [shouldJump, one_mul] at relation
  exact (sub_eq_zero.mp relation).trans
    (selected_jalr_lookup_target joltField joltInstance privateInputs witness
      context equations cycle slot selected row present dst base imm value jump baseAt)

/-- At an accepted address, a JALR with an architectural base is the only
row of its source. For example, the `ret` x0 rewrite emits one JALR row.
See jolt/crates/jolt-program/src/expand/mod.rs:281-307 at 8bbb2357. -/
theorem architectural_jalr_same_source_row
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (lastIndex : Fin bytecode.size)
    (dst : JoltISA.Dst) (rs1 : regidx) (imm : BitVec 64)
    (jump : bytecode[lastIndex].instruction = .JALR dst (.xreg rs1) imm)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (sameAddress : row.address = bytecode[lastIndex].address) :
    row = bytecode[lastIndex] := by
  obtain ⟨source, _, rows, sourceExpanded, lastMember, rowMember⟩ :=
    expanded_same_source_rows image bytecode expanded accepted
      bytecode[lastIndex] row (Array.getElem_mem_toList lastIndex.isLt)
      member sameAddress.symm
  have singleton := expanded_arch_jalr_singleton source rows sourceExpanded
    bytecode[lastIndex] lastMember dst rs1 imm jump
  rw [singleton] at rowMember
  simpa only [List.mem_singleton] using rowMember

/-- A selected jump writes the source address plus its full source length as
the link value when that addition does not wrap. For example, an uncompressed
JALR at `0x1000` writes `0x1004`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:296-302
at 8bbb2357. -/
theorem selected_jump_link_write_value
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (present : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (jump : JoltMetadata.opcodeFlag row.instruction .Jump = true)
    (linkNoWrap :
      (row.address + if row.is_compressed then 2 else 4).toNat =
        row.address.toNat + if row.is_compressed then 2 else 4) :
    witness.RdWriteValue cycle =
      ((row.address + if row.is_compressed then 2 else 4).toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have flags := JoltConstraints.Soundness.opFlag_of_selected_bytecode
    charAbove2pow127 context equations
  have jumpFlag : witness.OpFlags .Jump cycle = 1 := by
    simpa only [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag, jump] using
      flags .Jump cycle slot selected
  have compressedFlag : witness.OpFlags .IsCompressed cycle =
      if row.is_compressed then 1 else 0 := by
    simpa only [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag] using flags .IsCompressed cycle slot selected
  have address : witness.UnexpandedPC cycle = (row.address.toNat : F) := by
    simpa only [JoltConstraints.bytecodeAddress, present] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        charAbove2pow127 context equations cycle slot selected
  have relation := equations.rdWriteEqPCPlusConstIfJump cycle
  rw [jumpFlag, one_mul, address, compressedFlag] at relation
  rw [linkNoWrap]
  cases compressed : row.is_compressed with
  | false =>
      simp only [compressed, Bool.false_eq_true, ↓reduceIte] at relation ⊢
      rw [Nat.cast_add]
      linear_combination relation
  | true =>
      simp only [compressed, ↓reduceIte] at relation ⊢
      rw [Nat.cast_add]
      linear_combination relation

/-- A terminal architectural-base JALR whose destination differs from its
base replays with the same base value. For example, `jalr x1, 0(x2)` keeps
reading `x2` on each visit to its source.
See PR #2109 head d2995380, jolt/crates/jolt-riscv/src/row.rs:105-132. -/
private theorem stall_arch_jalr_preserved_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (dst : JoltISA.Dst) (rs1 : regidx) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR dst (.xreg rs1) imm)
    (noWriteBase : TraceWitness.destinationRegisterAddress dst ≠
      TraceWitness.sourceRegisterAddress (.xreg rs1))
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  rcases atCycle with padding | ⟨slot, row, selected, rowAt, sameSource, control⟩
  · exact False.elim (real padding)
  obtain ⟨accepted, rowAtContext, index, _, rowIs⟩ :=
    stall_cycle_selected_row joltInstance privateInputs context run.bytecode
      bytecodeEq slot row rowAt
  have member : row ∈ run.bytecode.toList := by
    rw [rowIs]
    exact Array.getElem_mem_toList index.isLt
  have rowEq : row = run.bytecode[last.rowIndex] :=
    architectural_jalr_same_source_row joltInstance.program run.bytecode
      run.expands accepted last.rowIndex dst rs1 imm jump row member sameSource
  have currentJump : row.instruction = .JALR dst (.xreg rs1) imm := by
    rw [rowEq]
    exact jump
  have baseAt : witness.RegistersVal
      (TraceWitness.sourceRegisterAddress (.xreg rs1)) cycle =
        ((JoltISA.sourceValue (.xreg rs1) last.preState).toNat : F) := by
    simpa only [jump, noWriteBase, false_and, ↓reduceIte] using control
  by_cases nextPadding :
      witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 1
  · exact Or.inl nextPadding
  have stableTarget := stable_jalr_target joltInstance privateInputs run last
    atEnd stable dst (.xreg rs1) imm jump
  have target := selected_jalr_next_target joltField joltInstance privateInputs
    witness context equations cycle next slot selected row rowAtContext
    dst (.xreg rs1) imm (JoltISA.sourceValue (.xreg rs1) last.preState)
    currentJump baseAt nextPadding
  have targetAddress : witness.NextUnexpandedPC cycle =
      (run.bytecode[last.rowIndex].address.toNat : F) := by
    simpa only [stableTarget] using target
  rcases stall_next_cycle_of_target joltField joltInstance privateInputs
    witness context equations cycle next run.bytecode[last.rowIndex].address
      targetAddress with isPadding | ⟨nextSlot, nextRow, nextSelected,
        nextRowAtContext, nextAddress⟩
  · exact False.elim (nextPadding isPadding)
  have nextRowAt : JoltConstraints.bytecodeRow run.bytecode nextSlot.val =
      some nextRow := by simpa only [bytecodeEq] using nextRowAtContext
  have noWrite : JoltConstraints.bytecodeRdRegister row.instruction ≠
      some (TraceWitness.sourceRegisterAddress (.xreg rs1)) := by
    intro same
    have addressEq : TraceWitness.destinationRegisterAddress dst =
        TraceWitness.sourceRegisterAddress (.xreg rs1) := by
      simpa [currentJump, JoltConstraints.bytecodeRdRegister,
        TraceWitness.capturedDestination] using same
    exact noWriteBase addressEq
  have unchanged := register_unchanged_of_no_write joltField joltInstance
    privateInputs witness context equations cycle next slot selected row rowAtContext
    (TraceWitness.sourceRegisterAddress (.xreg rs1)) noWrite
  have baseNext : witness.RegistersVal
      (TraceWitness.sourceRegisterAddress (.xreg rs1)) ⟨cycle.val + 1, next⟩ =
        ((JoltISA.sourceValue (.xreg rs1) last.preState).toNat : F) := by
    exact unchanged.trans baseAt
  exact Or.inr ⟨nextSlot, nextRow, nextSelected, nextRowAt, nextAddress,
    by simpa only [jump, noWriteBase, false_and, ↓reduceIte] using baseNext⟩

/-- A real JALR replay with an unwritten architectural base returns to the
same source or padding. This includes `jalr x1, 0(x2)` with distinct registers
and the x0 rewrite `JALR (.vreg _) (.xreg rs1) imm` used for `ret` and `jr`.
See jolt/crates/jolt-riscv/src/row.rs:105-132 in PR #2109 head d2995380. -/
theorem stall_jalr_preserved_base_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (preserved :
      (∃ (rd rs1 : regidx) (imm : BitVec 64),
        run.bytecode[last.rowIndex].instruction = .JALR (.xreg rd) (.xreg rs1) imm ∧
        (rd ≠ rs1 ∨ JoltISA.isX0 rd = true)) ∨
      (∃ (rd : JoltISA.VReg) (rs1 : regidx) (imm : BitVec 64),
        run.bytecode[last.rowIndex].instruction = .JALR (.vreg rd) (.xreg rs1) imm))
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  have lastOk := ExpansionRows.expand_program_rowOk joltInstance.program
    run.bytecode run.expands run.bytecode[last.rowIndex]
      (Array.getElem_mem_toList last.rowIndex.isLt)
  rcases preserved with ⟨rd, rs1, imm, jump, condition⟩ |
    ⟨rd, rs1, imm, jump⟩
  · have writable : JoltISA.isX0 rd = false := (lastOk.valid.jalr jump)
    have different : rd ≠ rs1 := by
      rcases condition with different | zero
      · exact different
      · rw [writable] at zero
        cases zero
    have noWriteBase : TraceWitness.destinationRegisterAddress (.xreg rd) ≠
        TraceWitness.sourceRegisterAddress (.xreg rs1) := by
      intro same
      have registerEq :=
        (jalr_destination_base_address_eq_iff (.xreg rd) (.xreg rs1)
          (by rfl) (by rfl)).mp same
      exact different (by simpa [JoltConstraints.Soundness.destinationSource] using registerEq)
    exact stall_arch_jalr_preserved_step joltField joltInstance privateInputs
      witness context equations run bytecodeEq last atEnd stable (.xreg rd)
        rs1 imm jump noWriteBase cycle next real atCycle
  · have canonicalDst : JoltRegisterEncoding.destinationIsCanonical (.vreg rd) = true :=
      JoltConstraints.Soundness.instruction_destination_canonical
        run.bytecode[last.rowIndex].instruction (.vreg rd) lastOk.canonical
        (by rw [jump]; rfl)
    have noWriteBase : TraceWitness.destinationRegisterAddress (.vreg rd) ≠
        TraceWitness.sourceRegisterAddress (.xreg rs1) := by
      intro same
      have impossible :=
        (jalr_destination_base_address_eq_iff (.vreg rd) (.xreg rs1)
          canonicalDst (by rfl)).mp same
      cases impossible
    exact stall_arch_jalr_preserved_step joltField joltInstance privateInputs
      witness context equations run bytecodeEq last atEnd stable (.vreg rd)
        rs1 imm jump noWriteBase cycle next real atCycle

/-- A JALR that writes its own nonzero base uses the link value from its
first execution; `selfJumpRepeats` says that value still targets the source.
For example, `jalr x1, imm(x1)` may be a stable stall for a suitable offset.
See jolt/crates/jolt-riscv/src/row.rs:105-132 in PR #2109 head d2995380. -/
theorem stall_jalr_written_base_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (rd : regidx) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR (.xreg rd) (.xreg rd) imm)
    (nonzero : JoltISA.isX0 rd = false)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  rcases atCycle with padding | ⟨slot, row, selected, rowAt, sameSource, control⟩
  · exact False.elim (real padding)
  obtain ⟨accepted, rowAtContext, index, _, rowIs⟩ :=
    stall_cycle_selected_row joltInstance privateInputs context run.bytecode
      bytecodeEq slot row rowAt
  have member : row ∈ run.bytecode.toList := by
    rw [rowIs]
    exact Array.getElem_mem_toList index.isLt
  have rowEq : row = run.bytecode[last.rowIndex] :=
    architectural_jalr_same_source_row joltInstance.program run.bytecode
      run.expands accepted last.rowIndex (.xreg rd) rd imm jump row member sameSource
  have currentJump : row.instruction = .JALR (.xreg rd) (.xreg rd) imm := by
    rw [rowEq]
    exact jump
  have nonzeroAddress :
      (TraceWitness.sourceRegisterAddress (.xreg rd)).val ≠ 0 := by
    intro zeroAddress
    cases rd with
    | Regidx bits =>
        have bitsMod : bits.toNat % 128 = 0 := by
          simpa [TraceWitness.sourceRegisterAddress, BitVec.toFin] using zeroAddress
        have bitsLt : bits.toNat < 128 := by
          have small : bits.toNat < 2 ^ 5 := by simpa using bits.isLt
          exact lt_trans small (by norm_num)
        have bitsZero : bits.toNat = 0 := by
          simpa only [Nat.mod_eq_of_lt bitsLt] using bitsMod
        have isZero : JoltISA.isX0 (.Regidx bits) = true := by
          change decide (bits.toNat = 0) = true
          simp only [bitsZero, decide_true]
        rw [isZero] at nonzero
        cases nonzero
  have baseAt : witness.RegistersVal
      (TraceWitness.sourceRegisterAddress (.xreg rd)) cycle =
        ((JoltISA.sourceValue (.xreg rd) last.postState).toNat : F) := by
    have activeGuard : TraceWitness.destinationRegisterAddress (.xreg rd) =
        TraceWitness.sourceRegisterAddress (.xreg rd) ∧
        (TraceWitness.sourceRegisterAddress (.xreg rd)).val ≠ 0 :=
      ⟨rfl, nonzeroAddress⟩
    simpa only [jump, if_pos activeGuard] using control
  by_cases nextPadding :
      witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 1
  · exact Or.inl nextPadding
  have stableTarget := stable_written_jalr_replay_target
    joltInstance privateInputs run last atEnd stable rd imm jump nonzero
  have target := selected_jalr_next_target joltField joltInstance privateInputs
    witness context equations cycle next slot selected row rowAtContext
    (.xreg rd) (.xreg rd) imm (JoltISA.sourceValue (.xreg rd) last.postState)
    currentJump baseAt nextPadding
  have targetAddress : witness.NextUnexpandedPC cycle =
      (run.bytecode[last.rowIndex].address.toNat : F) := by
    simpa only [stableTarget] using target
  rcases stall_next_cycle_of_target joltField joltInstance privateInputs
    witness context equations cycle next run.bytecode[last.rowIndex].address
      targetAddress with isPadding | ⟨nextSlot, nextRow, nextSelected,
        nextRowAtContext, nextAddress⟩
  · exact False.elim (nextPadding isPadding)
  have nextRowAt : JoltConstraints.bytecodeRow run.bytecode nextSlot.val =
      some nextRow := by simpa only [bytecodeEq] using nextRowAtContext
  have terminalLink := terminal_link_no_wrap joltInstance.program run.bytecode
    run.expands noWrap last.rowIndex stable.1
  have linkNoWrap :
      (row.address + if row.is_compressed then 2 else 4).toNat =
        row.address.toNat + if row.is_compressed then 2 else 4 := by
    simpa only [rowEq] using terminalLink
  have jumpFlag : JoltMetadata.opcodeFlag row.instruction .Jump = true := by
    simp [currentJump, JoltMetadata.opcodeFlag]
  have linkWrite := selected_jump_link_write_value joltField joltInstance
    privateInputs witness context equations cycle slot selected row rowAtContext
    jumpFlag linkNoWrap
  have modelLink := stable_written_jalr_link joltInstance privateInputs run
    last atEnd stable rd imm jump nonzero
  have after := JoltConstraints.Soundness.registersVal_succ_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations (TraceWitness.sourceRegisterAddress (.xreg rd))
    cycle next slot selected
  have afterWrite : witness.RegistersVal
      (TraceWitness.sourceRegisterAddress (.xreg rd)) ⟨cycle.val + 1, next⟩ =
        witness.RdWriteValue cycle := by
    have sameAddress : TraceWitness.sourceRegisterAddress (.xreg rd) =
        TraceWitness.destinationRegisterAddress (.xreg rd) := rfl
    simpa only [rowAtContext, Option.bind_some, currentJump,
      JoltConstraints.bytecodeRdRegister, TraceWitness.capturedDestination,
      if_pos sameAddress] using after
  have modelLinkEq :
      ((row.address + if row.is_compressed then 2 else 4).toNat : F) =
        ((JoltISA.sourceValue (.xreg rd) last.postState).toNat : F) := by
    rw [rowEq, modelLink]
  have baseNext : witness.RegistersVal
      (TraceWitness.sourceRegisterAddress (.xreg rd)) ⟨cycle.val + 1, next⟩ =
        ((JoltISA.sourceValue (.xreg rd) last.postState).toNat : F) := by
    exact afterWrite.trans (linkWrite.trans modelLinkEq)
  exact Or.inr ⟨nextSlot, nextRow, nextSelected, nextRowAt, nextAddress,
    by
      have activeGuard : TraceWitness.destinationRegisterAddress (.xreg rd) =
          TraceWitness.sourceRegisterAddress (.xreg rd) ∧
          (TraceWitness.sourceRegisterAddress (.xreg rd)).val ≠ 0 :=
        ⟨rfl, nonzeroAddress⟩
      simpa only [jump, if_pos activeGuard] using baseNext⟩

/-- A real ECALL or MRET replay moves through its virtual rows and then
returns to the same source or padding; the virtual JALR base is not written.
For example, MRET jumps through mepc and stores its link in a fresh temporary.
See jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 and
jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:47-52 at 8bbb2357. -/
theorem stall_system_jalr_step
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (rd rs1 : JoltISA.VReg) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR (.vreg rd) (.vreg rs1) imm)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1)
    (atCycle : StallSuffixInvariant witness run.bytecode last cycle) :
    StallSuffixInvariant witness run.bytecode last ⟨cycle.val + 1, next⟩ := by
  sorry

/-- A virtual-destination, virtual-base JALR in expanded bytecode comes from
ECALL or MRET, and no row at that source address writes its virtual base.
For example, MRET reads mepc while its link goes to a fresh temporary.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:47-52 and
jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 at 8bbb2357. -/
theorem expanded_virtual_jalr_source
    (joltInstance : JoltInstance SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program joltInstance.program = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (rd rs1 : JoltISA.VReg) (imm : BitVec 64)
    (jump : row.instruction = .JALR (.vreg rd) (.vreg rs1) imm) :
    (∃ source ∈ joltInstance.program.instructions,
      source.address = row.address ∧
      (source.instruction = .riscv .ECALL ∨
        source.instruction = .riscv .MRET)) ∧
    ∀ other ∈ bytecode.toList, other.address = row.address →
      ∀ dst : JoltISA.Dst, other.instruction.destination? = some dst →
        TraceWitness.destinationRegisterAddress dst ≠
          TraceWitness.sourceRegisterAddress (.vreg rs1) := by
  sorry

/-- Every expanded JALR row uses an architectural base with an architectural
or virtual destination, or a virtual base with a virtual destination.
For example, the x0 rewrite has a virtual destination and architectural base.
See jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 and
jolt/crates/jolt-riscv/src/row.rs:105-132 in PR #2109 head d2995380. -/
theorem expanded_jalr_operand_forms
    (joltInstance : JoltInstance SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program joltInstance.program = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (isJalr : ∃ dst base imm, row.instruction = .JALR dst base imm) :
    (∃ (rd rs1 : regidx) (imm : BitVec 64),
      row.instruction = .JALR (.xreg rd) (.xreg rs1) imm) ∨
    (∃ (rd : JoltISA.VReg) (rs1 : regidx) (imm : BitVec 64),
      row.instruction = .JALR (.vreg rd) (.xreg rs1) imm) ∨
    (∃ (rd rs1 : JoltISA.VReg) (imm : BitVec 64),
      row.instruction = .JALR (.vreg rd) (.vreg rs1) imm) := by
  sorry

/-- The final row of a stable stall is a JAL, a JALR or a branch; an ordinary
row would leave nextPC at its positive successor instead of its own address.
For example, EBREAK's final row is JAL while ADDI cannot stably stall.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stable_stall_control_flow
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall) :
    (∃ dst imm, run.bytecode[last.rowIndex].instruction = .JAL dst imm) ∨
    (∃ dst base imm, run.bytecode[last.rowIndex].instruction = .JALR dst base imm) ∨
    JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true := by
  classical
  have lastAt : run.rows[run.rows.size - 1]? = some last := by
    simpa only [Array.back?_eq_getElem?] using atEnd
  obtain ⟨lastIn, lastEq⟩ := Array.getElem?_eq_some_iff.mp lastAt
  let index : Fin run.rows.size := ⟨run.rows.size - 1, lastIn⟩
  have rowEq : run.rows[index] = last := lastEq
  rcases Classical.em (∃ dst imm,
    run.bytecode[last.rowIndex].instruction = .JAL dst imm) with jal | jal
  · exact Or.inl jal
  rcases Classical.em (∃ dst base imm,
    run.bytecode[last.rowIndex].instruction = .JALR dst base imm) with jalr | jalr
  · exact Or.inr (Or.inl jalr)
  by_cases branch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true
  · exact Or.inr (Or.inr branch)
  have noBranch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = false :=
    Bool.eq_false_iff.mpr branch
  have next := noncontrol_next_pc joltInstance privateInputs run index
    (by simpa only [rowEq] using jal)
    (by simpa only [rowEq] using jalr)
    (by simpa only [rowEq] using noBranch)
  have stableNext := stable.2.1
  have nextLast :
      last.postState.sail.regs.get? Register.nextPC =
        some (run.bytecode[last.rowIndex].address +
          if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
    simpa only [rowEq] using next
  have impossible :
      run.bytecode[last.rowIndex].address +
          (if source_is_compressed run.bytecode last.rowIndex then 2 else 4) =
        run.bytecode[last.rowIndex].address :=
    Option.some.inj (nextLast.symm.trans stableNext)
  cases compressed : source_is_compressed run.bytecode last.rowIndex with
  | false =>
      simp only [compressed, Bool.false_eq_true, ↓reduceIte] at impossible
      have zeroLength : (4 : BitVec 64) = 0 :=
        add_left_cancel (by simpa only [add_zero] using impossible)
      exact False.elim ((by decide : (4 : BitVec 64) ≠ 0) zeroLength)
  | true =>
      simp only [compressed, ↓reduceIte] at impossible
      have zeroLength : (2 : BitVec 64) = 0 :=
        add_left_cancel (by simpa only [add_zero] using impossible)
      exact False.elim ((by decide : (2 : BitVec 64) ≠ 0) zeroLength)

/-- A represented final JAL establishes the replay invariant at the cut: its
last cycle is a valid JAL replay, and the JAL step lemma supplies the next
cycle. For example, a retained `j .` selects its source again after the cut.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stall_suffix_initial_jal
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JAL dst imm)
    (cutBound : run.rows.size < params.traceLength) :
    StallSuffixInvariant witness run.bytecode last ⟨run.rows.size, cutBound⟩ := by
  obtain ⟨before, slot, beforeEq, _, selected, rowAt, real⟩ :=
    selected_last_represented_row joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last atEnd cutBound
  have atBefore : StallSuffixInvariant witness run.bytecode last before := by
    right
    refine ⟨slot, run.bytecode[last.rowIndex], selected, rowAt, rfl, ?_⟩
    rw [jump]
    trivial
  have next : before.val + 1 < params.traceLength := by omega
  have notPadding : witness.InstructionFlags .IsNoop before ≠ 1 := by
    rw [real]
    exact zero_ne_one
  have stepped := stall_jal_step joltField joltInstance privateInputs witness
    context equations run bytecodeEq last atEnd stable dst imm jump before next
    notPadding atBefore
  have same : (⟨before.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, cutBound⟩ := Fin.ext beforeEq
  simpa only [same] using stepped

/-- A represented final branch establishes the replay invariant at the cut:
its two table reads equal its pre-state operands before the branch step runs.
For example, a stable BEQ keeps comparing the same two registers.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stall_suffix_initial_branch
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (branch : JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true)
    (cutBound : run.rows.size < params.traceLength) :
    StallSuffixInvariant witness run.bytecode last ⟨run.rows.size, cutBound⟩ := by
  obtain ⟨before, slot, beforeEq, lastAtOpt, selected, rowAt, real⟩ :=
    selected_last_represented_row joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last atEnd cutBound
  have inRun : before.val < run.rows.size := by omega
  have lastAt : run.rows[before.val] = last :=
    Option.some.inj ((Array.getElem?_eq_getElem inRun).symm.trans lastAtOpt)
  obtain ⟨lhs, rhs, imm, shapes⟩ :=
    branch_instruction_of_flag run.bytecode[last.rowIndex].instruction branch
  have lhsRead : witness.RegistersVal (TraceWitness.sourceRegisterAddress lhs) before =
      ((JoltISA.sourceValue lhs last.preState).toNat : F) := by
    apply represented_last_control_read joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last before inRun slot selected rowAt
      false lhs
    · rcases shapes with h | h | h | h | h | h
      all_goals rw [h]; rfl
    · rcases shapes with h | h | h | h | h | h
      all_goals
        simp [TraceWitness.Rs1Value, inRun, lastAt]
        simp only [Fin.getElem_fin] at h
        rw [h]
  have rhsRead : witness.RegistersVal (TraceWitness.sourceRegisterAddress rhs) before =
      ((JoltISA.sourceValue rhs last.preState).toNat : F) := by
    apply represented_last_control_read joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last before inRun slot selected rowAt
      true rhs
    · rcases shapes with h | h | h | h | h | h
      all_goals rw [h]; rfl
    · rcases shapes with h | h | h | h | h | h
      all_goals
        simp [TraceWitness.Rs2Value, inRun, lastAt]
        simp only [Fin.getElem_fin] at h
        rw [h]
  have atBefore : StallSuffixInvariant witness run.bytecode last before := by
    right
    refine ⟨slot, run.bytecode[last.rowIndex], selected, rowAt, rfl, ?_⟩
    rcases shapes with h | h | h | h | h | h
    all_goals simpa only [h] using And.intro lhsRead rhsRead
  have next : before.val + 1 < params.traceLength := by omega
  have notPadding : witness.InstructionFlags .IsNoop before ≠ 1 := by
    rw [real]
    exact zero_ne_one
  have stepped := stall_branch_step joltField joltInstance privateInputs witness
    context equations run bytecodeEq last atEnd stable branch before next
    notPadding atBefore
  have same : (⟨before.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, cutBound⟩ := Fin.ext beforeEq
  simpa only [same] using stepped

/-- At the represented last JALR cycle, the base register table equals the
base value read from the recorded pre-state. For example, a retained
`jalr x0, 0(x1)` reads x1's pre-state value.
See jolt/crates/jolt-witness/src/witnesses/registers.rs:1-35 at 8bbb2357. -/
theorem represented_last_jalr_base
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR dst base imm)
    (before : Fin params.traceLength) (inRun : before.val < run.rows.size)
    (lastAt : run.rows[before.val] = last)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot before = 1)
    (rowAt : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex]) :
    witness.RegistersVal (TraceWitness.sourceRegisterAddress base) before =
      ((JoltISA.sourceValue base last.preState).toNat : F) := by
  apply represented_last_control_read joltField joltInstance privateInputs witness
    context equations run bytecodeEq represented last before inRun slot selected rowAt
    false base
  · rw [jump]
    rfl
  · simp [TraceWitness.Rs1Value, inRun, lastAt]
    simp only [Fin.getElem_fin] at jump ⊢
    rw [jump]

/-- The first cycle after a represented stable stall satisfies the suffix
invariant: it is padding, or it selects the stalled source with its control
operands at the required values. For example, the first replay of `j .`
selects the same JAL source. See PR #2109 head d2995380,
jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stall_suffix_initial
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (cutBound : run.rows.size < params.traceLength) :
    StallSuffixInvariant witness run.bytecode last ⟨run.rows.size, cutBound⟩ := by
  sorry

/-- Every cycle after the stable cut satisfies the replay invariant, by
induction over the five control-flow cases and the persistent padding suffix.
For example, repeated ECALL rows remain at its source address until padding.
See PR #2109 head d2995380, jolt/tracer/src/emulator/cpu.rs:553-578. -/
theorem stall_suffix_replays_source
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall) :
    ∀ cycle : Fin params.traceLength, run.rows.size ≤ cycle.val →
      StallSuffixInvariant witness run.bytecode last cycle := by
  intro cycle afterCut
  have charAbove2pow127 : 2 ^ 127 < ringChar F := by
    have large := joltField
    unfold JoltField at large
    omega
  have replay (n : Nat) (lower : run.rows.size ≤ n)
      (bound : n < params.traceLength) :
      StallSuffixInvariant witness run.bytecode last ⟨n, bound⟩ := by
    induction n, lower using Nat.le_induction with
    | base =>
        exact stall_suffix_initial joltField joltInstance noWrap privateInputs witness
          context equations run bytecodeEq represented last atEnd stable bound
    | succ n lower ih =>
        have previousBound : n < params.traceLength := by omega
        let previous : Fin params.traceLength := ⟨n, previousBound⟩
        have atPrevious := ih previousBound
        by_cases padding : witness.InstructionFlags .IsNoop previous = 1
        · exact Or.inl (JoltConstraints.Soundness.padding_persists charAbove2pow127
            context equations previous bound padding)
        · rcases stable_stall_control_flow joltInstance privateInputs run last atEnd stable with
            ⟨dst, imm, jump⟩ | ⟨dst, base, imm, jump⟩ | branch
          · exact stall_jal_step joltField joltInstance privateInputs witness context
              equations run bytecodeEq last atEnd stable dst imm jump previous bound
              padding atPrevious
          · have forms := expanded_jalr_operand_forms joltInstance run.bytecode
              run.expands run.bytecode[last.rowIndex]
              (Array.getElem_mem_toList last.rowIndex.isLt) ⟨dst, base, imm, jump⟩
            rcases forms with ⟨rd, rs1, offset, form⟩ |
              ⟨rd, rs1, offset, form⟩ | ⟨rd, rs1, offset, form⟩
            · by_cases same : rd = rs1
              · subst rs1
                cases zero : JoltISA.isX0 rd with
                | true =>
                    exact stall_jalr_preserved_base_step joltField joltInstance
                      privateInputs witness context equations run bytecodeEq last atEnd
                      stable (Or.inl ⟨rd, rd, offset, form, Or.inr zero⟩) previous
                      bound padding atPrevious
                | false =>
                    exact stall_jalr_written_base_step joltField joltInstance noWrap
                      privateInputs witness context equations run bytecodeEq last atEnd
                      stable rd offset form zero previous bound padding atPrevious
              · exact stall_jalr_preserved_base_step joltField joltInstance
                  privateInputs witness context equations run bytecodeEq last atEnd
                  stable (Or.inl ⟨rd, rs1, offset, form, Or.inl same⟩) previous
                  bound padding atPrevious
            · exact stall_jalr_preserved_base_step joltField joltInstance
                privateInputs witness context equations run bytecodeEq last atEnd
                stable (Or.inr ⟨rd, rs1, offset, form⟩) previous bound padding atPrevious
            · exact stall_system_jalr_step joltField joltInstance privateInputs witness
                context equations run bytecodeEq last atEnd stable rd rs1 offset form
                previous bound padding atPrevious
          · exact stall_branch_step joltField joltInstance privateInputs witness context
              equations run bytecodeEq last atEnd stable branch previous bound
              padding atPrevious
  exact replay cycle.val afterCut cycle.isLt

/-- A stamped bytecode row retains an instruction from its source expansion.
For example, a stamped ECALL JALR comes from `ecallProgram.instrs`.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 at 8bbb2357. -/
theorem stamp_sequence_instruction_member
    (address : BitVec 64) (compressed : Bool)
    (instructions : List JoltISA.Instr) (row : JoltInstructionRow)
    (member : row ∈ stamp_sequence address compressed instructions) :
    row.instruction ∈ instructions := by
  obtain ⟨index, bound, rowAt⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < instructions.length := by
    simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using bound
  have instructionAt : row.instruction = instructions[index] := by
    rw [← rowAt]
    simp only [stamp_sequence, List.getElem_map, List.getElem_zipIdx]
  rw [instructionAt]
  exact List.getElem_mem sourceBound

/-- If a stable stall ends in JAL, JALR or branch, every bytecode row at that
source address has no Store flag. For example, ECALL's virtual rows and final
JALR contain no SD row.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:1-52
at 8bbb2357. -/
theorem stable_stall_source_no_store
    (joltInstance : JoltInstance SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program joltInstance.program = some bytecode)
    (accepted : pc_map_ok bytecode = true)
    (last : TraceRow bytecode) (stable : last.StableStall)
    (control :
      (∃ dst imm, bytecode[last.rowIndex].instruction = .JAL dst imm) ∨
      (∃ dst base imm, bytecode[last.rowIndex].instruction = .JALR dst base imm) ∨
      JoltMetadata.instructionFlag bytecode[last.rowIndex].instruction .Branch = true)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (sameSource : row.address = bytecode[last.rowIndex].address) :
    JoltMetadata.circuitFlag row .Store = false := by
  sorry

/-- Every real suffix cycle has its Store flag unset after a stable cut.
For example, a replayed JALR writes a link register but no RAM word.
See PR #2109 head d2995380, jolt/crates/jolt-riscv/src/row.rs:105-132. -/
theorem stall_suffix_no_store
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (nonempty : 0 < run.rows.size)
    (stops : ∀ last ∈ run.rows.back?, last.StableStall)
    (cycle : Fin params.traceLength) (afterCut : run.rows.size ≤ cycle.val)
    (real : witness.InstructionFlags .IsNoop cycle ≠ 1) :
    witness.OpFlags .Store cycle = 0 := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := by
    have large := joltField
    unfold JoltField at large
    omega
  have lastBound : run.rows.size - 1 < run.rows.size := by omega
  let last : TraceRow run.bytecode := run.rows[run.rows.size - 1]'lastBound
  have atEnd : last ∈ run.rows.back? := by
    rw [Array.back?_eq_getElem?]
    simp [last, nonempty]
  have stable := stops last atEnd
  have control := stable_stall_control_flow joltInstance privateInputs run last atEnd stable
  have acceptedContext : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  have accepted : pc_map_ok run.bytecode = true := by
    simpa only [bytecodeEq] using acceptedContext
  have replay := stall_suffix_replays_source joltField joltInstance noWrap privateInputs
    witness context equations run bytecodeEq represented last atEnd stable cycle afterCut
  rcases replay with isPadding | ⟨slot, row, selected, rowAt, sameSource, _⟩
  · exact False.elim (real isPadding)
  have member : row ∈ run.bytecode.toList := by
    cases slot with
    | mk index inSlots =>
      cases index with
      | zero => simp [JoltConstraints.bytecodeRow] at rowAt
      | succ k =>
          obtain ⟨inRange, rowEq⟩ := Array.getElem?_eq_some_iff.mp
            (show run.bytecode[k]? = some row from rowAt)
          rw [← rowEq]
          exact Array.getElem_mem_toList inRange
  have noStore := stable_stall_source_no_store joltInstance run.bytecode run.expands
    accepted last stable control row member sameSource
  have rowAtContext : JoltConstraints.bytecodeRow context.bytecode slot.val = some row := by
    simpa only [← bytecodeEq] using rowAt
  rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode charAbove2pow127 context
    equations .Store cycle slot selected]
  simp [JoltConstraints.bytecodeCircuitFlag, rowAtContext, noStore]

/-- Every witness cycle after a nonempty stable cut has zero selector weighted
RAM increment at every word. For example, a replayed jump or padding row
leaves the termination word unchanged.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:392-394
at 8bbb2357. -/
theorem soundness_stall_suffix_zero_ram_effects
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (nonempty : 0 < run.rows.size)
    (stops : ∀ last ∈ run.rows.back?, last.StableStall) :
    ∀ cycle : Fin params.traceLength, run.rows.size ≤ cycle.val →
      ∀ address : Fin params.ramSize,
        witness.RamRa address cycle * witness.RamInc cycle = 0 := by
  intro cycle afterCut address
  have charAbove2pow127 : 2 ^ 127 < ringChar F := by
    have large := joltField
    unfold JoltField at large
    omega
  by_cases padding : witness.InstructionFlags .IsNoop cycle = 1
  · exact (JoltConstraints.Soundness.ram_zero_effects charAbove2pow127 context equations cycle
      (JoltConstraints.Soundness.ramAddress_zero_of_padding charAbove2pow127
        context equations cycle padding)).2.2 address
  · have noStore := stall_suffix_no_store joltField joltInstance noWrap privateInputs
      witness context equations run bytecodeEq represented nonempty stops
      cycle afterCut padding
    by_cases load : witness.OpFlags .Load cycle = 1
    · exact JoltConstraints.Soundness.ram_write_effect_zero_of_load
        charAbove2pow127 context equations cycle load address
    · obtain ⟨slot, selected, _⟩ :=
        JoltConstraints.Soundness.bytecodeRa_unique charAbove2pow127 context equations cycle
      have value := JoltConstraints.Soundness.opFlag_of_selected_bytecode charAbove2pow127
        context equations .Load cycle slot selected
      have noLoad : witness.OpFlags .Load cycle = 0 := by
        cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
        | none => simpa [JoltConstraints.bytecodeCircuitFlag, present] using value
        | some row =>
          by_cases active : JoltMetadata.circuitFlag row .Load = true
          · have one : witness.OpFlags .Load cycle = 1 := by
              simpa [JoltConstraints.bytecodeCircuitFlag, present, active] using value
            exact False.elim (load one)
          · simpa [JoltConstraints.bytecodeCircuitFlag, present, active] using value
      exact (JoltConstraints.Soundness.ram_zero_effects charAbove2pow127 context equations
        cycle (JoltConstraints.Soundness.ramAddress_zero_of_not_load_store
          equations.ramAddrEqZeroIfNotLoadStore cycle noLoad noStore)).2.2 address

end JoltInstance
