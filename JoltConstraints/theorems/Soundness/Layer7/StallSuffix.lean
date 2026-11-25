import JoltConstraints.theorems.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.theorems.Soundness.Layer2.Registers
import JoltConstraints.theorems.Soundness.Layer4.Interleaved
import JoltConstraints.theorems.Soundness.Layer4.Word
import JoltConstraints.theorems.Soundness.Layer4.ComparisonEntry
import JoltConstraints.theorems.Soundness.Layer4.Inputs
import JoltConstraints.theorems.Soundness.Layer4.Arithmetic
import JoltConstraints.theorems.Completeness.Helpers.TracePCProofHelpers
import JoltConstraints.theorems.Soundness.Assumptions
import JoltConstraints.theorems.Soundness.Layer5.TapeTrace
import JoltConstraints.theorems.Soundness.Layer5.RuntimeAdvice

open LeanRV64D

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- A bytecode Branch flag identifies one of the six conditional branches;
for example, BEQ carries this flag.
See jolt/crates/jolt-riscv/src/instructions/i/beq.rs:1-8 at ff6fc6568. -/
theorem branch_instruction_of_flag (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    ∃ lhs rhs imm,
      instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm := by
  cases instruction <;> simp_all [JoltMetadata.instructionFlag]

/-- A decoded branch at a valid bytecode address cannot target field address
zero: its signed 13-bit offset is smaller than the RAM start address.
For example, even the minimum offset from `0x80000000` stays above zero. -/
theorem branch_target_ne_zero
    {F : Type} [Field F] (joltField : JoltField F)
    (row : JoltInstructionRow) (valid : row.Valid)
    (addressOk : bytecode_address_ok row.address = true)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true) :
    (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) ≠ 0 := by
  obtain ⟨lhs, rhs, imm, isBranch⟩ := branch_instruction_of_flag row.instruction branch
  obtain ⟨_, offset, offsetEq⟩ := valid.branch isBranch
  have immediate : JoltMetadata.immediate row.instruction = offset.toInt := by
    have ext : (offset.signExtend 128).toInt = offset.toInt :=
      BitVec.toInt_signExtend_of_le (by decide)
    rcases isBranch with h | h | h | h | h | h
    all_goals simp [h, JoltMetadata.immediate, offsetEq, ext]
  have ram : JoltISA.RAM_START_ADDRESS ≤ row.address.toNat := by
    have h := addressOk
    simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have low := BitVec.le_toInt offset
  have high := BitVec.toInt_lt (x := offset)
  have positive : 0 < (row.address.toNat : Int) + offset.toInt := by
    have ramStart : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
    rw [ramStart] at ram
    norm_num at low high
    omega
  let target : Nat := Int.toNat ((row.address.toNat : Int) + offset.toInt)
  have targetPositive : 0 < target := by
    dsimp [target]
    omega
  have targetBound : target < ringChar F := by
    have wordBound := row.address.isLt
    have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    have stronger := JoltConstraints.Soundness.two_pow_127_lt_char joltField
    norm_num at high
    dsimp [target]
    omega
  intro zero
  have targetCast : (target : F) = 0 := by
    have targetInt : (target : Int) = (row.address.toNat : Int) + offset.toInt := by
      dsimp [target]
      omega
    calc
      (target : F) = ((target : Int) : F) := by norm_num
      _ = (((row.address.toNat : Int) + offset.toInt : Int) : F) := by rw [targetInt]
      _ = (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) := by
        rw [immediate]
        norm_num
      _ = 0 := zero
  have targetZero : target = 0 :=
    JoltConstraints.Soundness.natCast_injective_below_char (b := 0) targetBound
      (by have h := JoltConstraints.Soundness.two_pow_127_lt_char joltField; omega)
      (by simpa using targetCast)
  omega

/-- A terminal row carries its source's compression flag itself. For example,
the last ECALL row has the flag used to prepare ECALL's next PC.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 at ff6fc6568. -/
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
See jolt/tracer/src/instruction/jalr.rs:19-30 at ff6fc6568. -/
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
See jolt/crates/jolt-witness/src/witnesses/pc.rs:1-35 at ff6fc6568. -/
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

/-- A selected row's first or second source reads its register-table entry.
For example, BEQ's two selected operands read the table entries for its bases.
See jolt/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs:97-121
at ff6fc6568. -/
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

/-- The last represented row selects its bytecode slot at a real witness cycle,
including when the run fills the witness.
For example, a final BEQ in a full witness still selects its BEQ slot.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`Pc::extract`)
at ff6fc6568. -/
theorem selected_last_represented_row_at_end
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
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?) :
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
  have beforeBound : run.rows.size - 1 < params.traceLength := by
    have rowsBound := represented.rowsBound
    omega
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

/-- The last represented row occupies a real selected cycle immediately before
the cut. For example, a retained `jal x0, 0` selects its JAL bytecode slot at
the cycle before the first suffix cycle.
See jolt/crates/jolt-witness/src/witnesses/pc.rs:1-35 at ff6fc6568. -/
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
    (_cutBound : run.rows.size < params.traceLength) :
    ∃ (before : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK)),
      before.val + 1 = run.rows.size ∧
      run.rows[before.val]? = some last ∧
      JoltConstraints.bytecodeRa witness slot before = 1 ∧
      JoltConstraints.bytecodeRow run.bytecode slot.val =
        some run.bytecode[last.rowIndex] ∧
      witness.InstructionFlags .IsNoop before = 0 := by
  exact selected_last_represented_row_at_end joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented last atEnd

/-- An instruction temporary has one of the eight addresses 40–47.
For example, temporary 40 has index zero. -/
theorem instructionTemporary_index :
    ∀ register : Fin 128, IsInstructionTemporary register →
      ∃ index : Fin 8, register.val = 40 + index.val := by
  unfold IsInstructionTemporary
  decide

/-- An operand encoded at an instruction-temporary address is that virtual register.
For example, address 40 identifies virtual register 40, never an architectural register. -/
theorem temporary_source (source : Src) (index : Fin 8)
    (address : TraceWitness.sourceRegisterAddress source =
      (BitVec.ofNat 7 (40 + index.val)).toFin) :
    source = .vreg (BitVec.ofNat 7 (40 + index.val)) := by
  cases source with
  | xreg register =>
      cases register with
      | Regidx bits =>
          have bound : bits.toNat < 32 := bits.isLt
          have indexBound := index.isLt
          have equal := congrArg Fin.val address
          change (bits.setWidth 7).toNat = (40 + index.val) % 128 at equal
          rw [BitVec.toNat_setWidth] at equal
          omega
  | vreg register => exact congrArg Src.vreg (BitVec.eq_of_toFin_eq address)

/-- All six branch forms read their two named operands in order.
For example, BEQ reads its left source as rs1 and its right source as rs2. -/
theorem branch_operand_forms (instruction : Instr) (lhs rhs : Src) (imm : BitVec 128)
    (shapes : instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm) :
    ExpansionTempLiveness.readSources instruction = [lhs, rhs] ∧
    JoltConstraints.bytecodeRs1Register instruction = some (TraceWitness.sourceRegisterAddress lhs) ∧
    JoltConstraints.bytecodeRs2Register instruction = some (TraceWitness.sourceRegisterAddress rhs) := by
  rcases shapes with h | h | h | h | h | h
  all_goals rw [h]; exact ⟨rfl, rfl, rfl⟩

private theorem control_operand_source (instruction : Instr)
    (control : JoltMetadata.instructionFlag instruction .Branch = true ∨
      ∃ dst base imm, instruction = .JALR dst base imm)
    (second : Bool) (register : Fin 128)
    (read : (if second then JoltConstraints.bytecodeRs2Register instruction
      else JoltConstraints.bytecodeRs1Register instruction) = some register) :
    ∃ source ∈ ExpansionTempLiveness.readSources instruction,
      TraceWitness.sourceRegisterAddress source = register := by
  rcases control with branch | ⟨dst, base, imm, rfl⟩
  · obtain ⟨lhs, rhs, imm, shapes⟩ := branch_instruction_of_flag instruction branch
    have forms := branch_operand_forms instruction lhs rhs imm shapes
    refine ⟨if second then rhs else lhs, ?_, ?_⟩
    · cases second <;> simp [forms.1]
    · cases second <;> simpa only [forms.2.1, forms.2.2, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq] using read
  · cases second with
    | false => exact ⟨base, by simp [ExpansionTempLiveness.readSources], Option.some.inj read⟩
    | true => cases read

private theorem unwritten_no_read (register : JoltISA.VReg) (instructions : List Instr)
    (live : ExpansionTempLiveness.firstAccessIsWrite register instructions = true)
    (unwritten : ∀ instruction ∈ instructions,
      ExpansionTempLiveness.writes register instruction = false)
    (instruction : Instr) (member : instruction ∈ instructions) :
    ExpansionTempLiveness.reads register instruction = false := by
  induction instructions with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ExpansionTempLiveness.firstAccessIsWrite_head_no_read _ _ _ live
      · exact ih (ExpansionTempLiveness.firstAccessIsWrite_tail _ _ _ live
          (unwritten first (by simp)))
          (fun row inside => unwritten row (List.mem_cons_of_mem first inside)) later

/-- An operand read by a branch or JALR in expanded bytecode is not an
instruction temporary (registers 40–47). For example, ECALL's JALR reads
persistent register 34 (`mtvec`), while BEQ reads architectural registers.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:47-51 and
jolt/crates/jolt-program/src/expand/control_flow/mret.rs:17-26 at ff6fc6568. -/
theorem expanded_control_read_not_temporary
    (program : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program program = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (control : JoltMetadata.instructionFlag row.instruction .Branch = true ∨
      ∃ dst base imm, row.instruction = .JALR dst base imm)
    (second : Bool) (register : Fin 128)
    (reads : (if second then JoltConstraints.bytecodeRs2Register row.instruction
      else JoltConstraints.bytecodeRs1Register row.instruction) = some register) :
    ¬ IsInstructionTemporary register := by
  intro temporary
  obtain ⟨index, address⟩ := instructionTemporary_index register temporary
  let temp := BitVec.ofNat 7 (40 + index.val)
  have registerEq : register = temp.toFin := by
    apply Fin.ext
    change register.val = (40 + index.val) % 128
    have bound := index.isLt
    omega
  obtain ⟨operand, operandIn, operandAddress⟩ :=
    control_operand_source row.instruction control second register reads
  rw [temporary_source operand index (operandAddress.trans registerEq)] at operandIn
  have isRead : ExpansionTempLiveness.reads temp row.instruction = true :=
    List.any_eq_true.mpr ⟨.vreg temp, operandIn, by simp⟩
  have liveOf : ∀ instructions, ExpansionTempLiveness.tempsReadAfterWrite instructions = true →
      ExpansionTempLiveness.firstAccessIsWrite temp instructions = true := by
    intro instructions live
    exact List.all_eq_true.mp live index.val (List.mem_range.mpr index.isLt)
  obtain ⟨source, _, rows, sourceExpanded, rowIn⟩ :=
    expand_program_source_of_row program bytecode expanded row member
  have checks := ExpansionFacts.expand_instruction_checks source rows sourceExpanded
  have instructionIn := List.mem_map_of_mem (f := JoltInstructionRow.instruction) rowIn
  cases sourceExpansion : source.instruction.expand with
  | none => simp only [sourceExpansion] at checks
  | some result =>
    cases result with
    | native instruction =>
      simp only [sourceExpansion] at checks
      rw [checks.1, List.mem_singleton] at instructionIn
      have noRead := ExpansionTempLiveness.firstAccessIsWrite_head_no_read temp instruction []
        (liveOf _ (ExpansionFacts.nativeRowOk_tempsReadAfterWrite instruction checks.2.1))
      rw [instructionIn, noRead] at isRead
      cases isRead
    | sequence instructions =>
      simp only [sourceExpansion] at checks
      rw [checks.1] at instructionIn
      rcases control with branch | ⟨dst, base, imm, jump⟩
      · obtain ⟨i, bound, atRow⟩ := List.mem_iff_getElem.mp instructionIn
        have ok := (ExpansionRows.rowsOk_rows instructions
          (ExpansionFacts.sequenceOk_rowsOk instructions checks.2.1) i bound).1
        rw [atRow] at ok
        simp [ExpansionFacts.sequenceRowOk, branch] at ok
      · have baseEq : .vreg temp = base := by
          simpa only [jump, ExpansionTempLiveness.readSources, List.mem_singleton] using operandIn
        rw [← baseEq] at jump
        have forms := List.all_eq_true.mp checks.2.2.2.1 row.instruction instructionIn
        cases dst with
        | xreg dst => simp only [jump, Bool.false_eq_true] at forms
        | vreg dst =>
          have guard := List.all_eq_true.mp checks.2.2.2.2.1 row.instruction instructionIn
          simp only [jump] at guard
          have noRead := unwritten_no_read temp instructions
            (liveOf _ (ExpansionFacts.sequenceOk_tempsReadAfterWrite instructions checks.2.1))
            (fun other inside => by
              simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using
                List.all_eq_true.mp guard other inside)
            row.instruction instructionIn
          rw [noRead] at isRead
          cases isRead

/-- A represented nontemporary control operand at the last retained cycle equals the
corresponding source register in the last row's pre-state. For example, a
retained BEQ reads its two pre-state operands from their register-table entries.
See jolt/crates/jolt-witness/src/witnesses/registers.rs:1-35 at ff6fc6568. -/
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
        ((JoltISA.sourceValue source last.preState).toNat : F))
    (nonTemporary : ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress source)) :
    witness.RegistersVal (TraceWitness.sourceRegisterAddress source) before =
      ((JoltISA.sourceValue source last.preState).toNat : F) := by
  have rowAtContext : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by simpa only [← bytecodeEq] using rowAt
  have read := selected_operand_register
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) joltInstance
    privateInputs witness context equations before slot selected
    run.bytecode[last.rowIndex] rowAtContext second
    (TraceWitness.sourceRegisterAddress source) reads
  have selectedRun := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented before inRun
  have slotEq := JoltConstraints.Soundness.bytecodeRa_at_most_one
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations before _ _ selected selectedRun
  have rowEq : run.bytecode[run.rows[before.val].rowIndex] =
      run.bytecode[last.rowIndex] := by
    rw [slotEq] at rowAt
    simpa [JoltConstraints.bytecodeRow] using rowAt
  have safeRead : ∀ register ∈ (if second then JoltConstraints.bytecodeRs2Register
      run.bytecode[last.rowIndex].instruction else JoltConstraints.bytecodeRs1Register
      run.bytecode[last.rowIndex].instruction), ¬ IsInstructionTemporary register := by
    simp only [reads, Option.mem_some_iff]
    intro register equal
    exact equal ▸ nonTemporary
  have representedRead :
      (if second then witness.Rs2Value before else witness.Rs1Value before) =
        (if second then TraceWitness.Rs2Value params run.toTrace before
        else TraceWitness.Rs1Value params run.toTrace before) := by
    cases second with
    | false =>
        exact represented.rs1 before inRun (by simpa only [rowEq] using! safeRead)
    | true =>
        exact represented.rs2 before inRun (by simpa only [rowEq] using! safeRead)
  exact read.symm.trans (representedRead.trans observed)

/-- The next cycle selects padding or a row whose address is the current
cycle's next unexpanded PC. For example, after a BEQ at address `a` targeting
`a + 8`, the next real row has address `a + 8`.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`NextUnexpandedPc::extract`)
at ff6fc6568. -/
theorem next_cycle_address
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength) :
    witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 1 ∨
      ∃ (slot : Fin (2 ^ params.logBytecodeK)) (row : JoltInstructionRow),
        JoltConstraints.bytecodeRa witness slot ⟨cycle.val + 1, next⟩ = 1 ∧
        JoltConstraints.bytecodeRow context.bytecode slot.val = some row ∧
        witness.NextUnexpandedPC cycle = (row.address.toNat : F) := by
  have charAbove2pow127 := JoltConstraints.Soundness.two_pow_127_lt_char joltField
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
          witness.NextUnexpandedPC cycle := by
        simp only [equations.nextUnexpandedPCEqShift cycle, dite_eq_left next]
      have encoded := JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        charAbove2pow127 context equations ⟨cycle.val + 1, next⟩ slot selected
      exact ⟨slot, row, selected, present,
        by simpa [JoltConstraints.bytecodeAddress, present] using shifted.symm.trans encoded⟩

/-- A constrained next unexpanded PC selects padding or a bytecode row at
that address. For example, a `JAL +0` target at address `a` can only lead to
padding or a row whose address is `a`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:395-403
at ff6fc6568. -/
theorem next_cycle_of_target
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
  rcases next_cycle_address joltField joltInstance privateInputs witness context
    equations cycle next with padding | ⟨slot, row, selected, present, address⟩
  · exact Or.inl padding
  · right
    refine ⟨slot, row, selected, present, ?_⟩
    exact JoltConstraints.Soundness.word_eq_of_field_eq
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      (address.symm.trans targetEq)

/-- A real bytecode slot is one plus the index of its row in the expanded
array. For example, slot one contains bytecode row zero.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:1-30 at ff6fc6568. -/
theorem real_slot_index (bytecode : Array JoltInstructionRow)
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
        Option.some.injEq] using! present.symm

/-- A real selected row of accepted expanded bytecode has an array index, and
its slot can be read through the witness context. For example, bytecode row
zero is selected through slot one.
See jolt/crates/jolt-program/src/preprocess/bytecode.rs:128-187 at ff6fc6568. -/
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
  obtain ⟨index, slotIs, rowIs⟩ := real_slot_index bytecode slot.val row rowAt
  exact ⟨accepted, by simpa only [← bytecodeEq] using rowAt,
    index, slotIs, rowIs⟩

/-- A selected JAL row's lookup computes its wrapped bytecode address plus
its immediate. For example, `JAL +0` at `a` looks up `a`.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/jal.rs:18-30
at ff6fc6568. -/
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
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:395-403
at ff6fc6568. -/
theorem stall_jal_next_target
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
  have relation := equations.nextUnexpandedPCEqLookupIfJump cycle
  rw [jumpFlag, one_mul] at relation
  exact (sub_eq_zero.mp relation).trans
    (stall_jal_lookup_target joltField joltInstance privateInputs witness
      context equations cycle slot selected row present dst imm jump)

/-- Executing a JAL puts its address plus immediate in Sail's nextPC. For
example, `JAL +0` at address `a` leaves nextPC at `a`.
See jolt/tracer/src/instruction/jal.rs:19-30 at ff6fc6568. -/
theorem stall_jal_exec_target (dst : JoltISA.Dst) (imm address link : BitVec 64)
    (pre post : SailJoltState)
    (pc : pre.sail.regs.get? Register.PC = some address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltISA.execInstr (.JAL dst imm) pre = .ok RETIRE_SUCCESS post) :
    post.sail.regs.get? Register.nextPC = some (address + imm) := by
  have readNext : liftSail (LeanRV64D.readReg Register.nextPC) pre = .ok link pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.nextPC pre.sail link nextPC]
  have readPC : liftSail (LeanRV64D.readReg Register.PC) pre = .ok address pre := by
    unfold liftSail
    rw [readReg_eq_of_get? Register.PC pre.sail address pc]
  simp only [JoltISA.execInstr, bind, EStateM.bind, readNext, readPC] at runs
  cases written : JoltISA.writeDst dst link pre with
  | error error state => simp only [written] at runs; cases runs
  | ok result middle =>
      cases result
      simp only [written, liftSail, LeanRV64D.writeReg, pure, EStateM.pure] at runs
      cases runs
      simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, ↓reduceDIte, cast_eq]

/-- A row certified as the back of a run is its final indexed row, so its
execution certificate and prepared PC are available. For example, a one-row
`j .` run has its sole row at index zero.
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
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

/-- Each branch's control inputs come from both source registers, with no
runtime advice. For example, BEQ compares Rs1 and Rs2 without an immediate
lookup operand. See jolt/crates/jolt-riscv/src/instructions/i/beq.rs:1-8
at ff6fc6568. -/
private theorem stall_branch_control_flags (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = true ∧
      JoltMetadata.instructionRafFlag instruction = false ∧
      JoltMetadata.instructionFlag instruction .LeftOperandIsPC = false ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsImm = false := by
  obtain ⟨lhs, rhs, imm, shape⟩ := branch_instruction_of_flag instruction branch
  rcases shape with h | h | h | h | h | h
  all_goals simp [h, JoltMetadata.instructionFlag,
    JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag]

/-- Each branch's comparison table returns the same taken bit as the ISA
branch decision on two words. For example, BEQ on equal words returns one.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/beq.rs:1-35
at ff6fc6568. -/
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
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:398-403
at ff6fc6568. -/
theorem stall_branch_lookup_decision
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
    have rd := JoltConstraints.Soundness.rdWriteInput_false_of_rs1Input row.instruction flags.1
    simpa only [flags.2.1, ↓reduceIte, flags.2.2.2.2, rd, Bool.false_eq_true,
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
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
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
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
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
    | VirtualHostIO =>
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
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
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
  · rename_i _ notAdvice
    replace runs : JoltISA.execInstr instruction before = .ok (.Retire_Success ()) after := by
      rw [← JoltConstraints.Soundness.execWithTapeAnswer_of_ne instruction answer notAdvice]
      exact runs
    have hostFrame : instruction.HostIOPCFrame before after := by
      unfold JoltISA.Instr.HostIOPCFrame
      split
      · have ranHost : JoltISA.execHostIO before = .ok (.Retire_Success ()) after := by
          simpa only [JoltISA.execInstr] using runs
        rw [execHostIO_keeps_sail before after _ ranHost]
      · trivial
    exact JoltPCFrame.instruction instruction before after hostFrame runs

/-- Consecutive rows within one source read the same compression flag from
that source's final row. For example, both ECALL rows use its final-row flag.
See jolt/crates/jolt-program/src/expand/metadata.rs:46-52 at ff6fc6568. -/
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

private theorem prefix_back_succ {α : Type} (rows : Array α) (n : Nat)
    (inside : n < rows.size) :
    (rows.extract 0 (n + 1)).back? = some rows[n] := by
  simp [Array.back?_eq_getElem?, Array.size_extract,
    inside]

private theorem untrusted_entry_at
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (inside : n < run.rows.size) :
    match (run.rows.extract 0 n).back? with
    | none => run.bytecode[run.rows[n].rowIndex].address = joltInstance.program.entry_address ∧
        run.bytecode[run.rows[n].rowIndex].starts_source ∧
        run.rows[n].preState = advance_pc joltInstance.program.entry_address
          (source_is_compressed run.bytecode run.rows[n].rowIndex) run.initialState
    | some last =>
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        run.rows[n].rowIndex.val = last.rowIndex.val + 1 ∧ run.rows[n].preState = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        run.bytecode[run.rows[n].rowIndex].address = address ∧ run.bytecode[run.rows[n].rowIndex].starts_source ∧
        run.rows[n].preState = advance_pc address (source_is_compressed run.bytecode run.rows[n].rowIndex) last.postState := by
  cases n with
  | zero => simpa using run.starts run.rows[0] (Array.getElem?_eq_getElem inside)
  | succ n =>
    rw [prefix_back_succ run.rows n (by omega)]
    exact run.linked n run.rows[n] run.rows[n + 1]
      (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem inside)

private theorem prepared_pc_link
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (last : TraceRow bytecode) (next : Fin bytecode.size) (pre : SailJoltState)
    (answer : BitVec 64)
    (executes : JoltConstraints.Soundness.execWithTapeAnswer
      (bytecode[last.rowIndex].instruction.withRuntimeAdvice last.runtimeAdvice)
      answer last.preState = .ok RETIRE_SUCCESS last.postState)
    (pc : last.preState.sail.regs.get? Register.PC = some bytecode[last.rowIndex].address)
    (nextPC : last.preState.sail.regs.get? Register.nextPC = some (bytecode[last.rowIndex].address +
      if source_is_compressed bytecode last.rowIndex then 2 else 4))
    (entry : if bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        bytecode[next].address = address ∧ bytecode[next].starts_source ∧
        pre = advance_pc address (source_is_compressed bytecode next) last.postState) :
    pre.sail.regs.get? Register.PC = some bytecode[next].address ∧
      pre.sail.regs.get? Register.nextPC = some (bytecode[next].address +
        if source_is_compressed bytecode next then 2 else 4) := by
  split at entry
  · rename_i continues
    have flag : bytecode[last.rowIndex].continues = true := by
      simpa [JoltInstructionRow.continues, bne_iff_ne] using continues
    have layout := expand_program_layout image bytecode expanded
    have sameAddress := (layout.next last.rowIndex next entry.1 flag).1
    have sameCompression := source_compressed_next bytecode layout last.rowIndex next entry.1 flag
    have ok := ExpansionRows.expand_program_rowOk image bytecode expanded bytecode[last.rowIndex]
      (Array.getElem_mem_toList last.rowIndex.isLt)
    have ordinary := ExpansionRows.ordinary_withRuntimeAdvice _ last.runtimeAdvice
      (ok.ordinaryIfContinues flag)
    rw [entry.2, sameAddress, ← sameCompression]
    exact ⟨(tape_row_preserves_pc _ answer _ _ executes).trans pc,
      (ordinary_tape_next_pc _ answer _ _ ordinary executes).trans nextPC⟩
  · obtain ⟨address, _, sourceAddress, _, prepared⟩ := entry
    rw [prepared, sourceAddress]
    simp [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq]

private theorem untrusted_prepared_pc_at
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (n : Nat) (within : n ≤ run.rows.size)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (entry : match (run.rows.extract 0 n).back? with
    | none => run.bytecode[next].address = joltInstance.program.entry_address ∧
        run.bytecode[next].starts_source ∧
        pre = advance_pc joltInstance.program.entry_address
          (source_is_compressed run.bytecode next) run.initialState
    | some last =>
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        run.bytecode[next].address = address ∧ run.bytecode[next].starts_source ∧
        pre = advance_pc address (source_is_compressed run.bytecode next) last.postState) :
    pre.sail.regs.get? Register.PC = some run.bytecode[next].address ∧
      pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
        if source_is_compressed run.bytecode next then 2 else 4) := by
  induction n generalizing next pre with
  | zero =>
    simp only [Array.extract_zero, Array.back?_empty] at entry
    obtain ⟨address, _, prepared⟩ := entry
    rw [prepared, address]
    simp [advance_pc, Std.ExtDHashMap.get?_insert, beq_iff_eq]
  | succ n ih =>
    have inside : n < run.rows.size := by omega
    rw [prefix_back_succ run.rows n inside] at entry
    obtain ⟨pc, nextPC⟩ := ih (by omega) run.rows[n].rowIndex run.rows[n].preState
      (untrusted_entry_at run n inside)
    exact prepared_pc_link joltInstance.program run.bytecode run.expands run.rows[n] next pre
      (run.answers ⟨n, inside⟩) (run.executes ⟨n, inside⟩) pc nextPC entry

/-- The state prepared after a certified prefix has PC at the next row's source
address and nextPC at that address plus its source length, before that row runs.
For example, ECALL's final JALR starts with the same prepared PCs as its AUIPC.
The entry clause is written out to avoid importing Layer 6's `RawRowEntry`.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at ff6fc6568. -/
theorem untrusted_prepared_pc
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (entry : match run.rows.back? with
    | none => run.bytecode[next].address = joltInstance.program.entry_address ∧
        run.bytecode[next].starts_source ∧
        pre = advance_pc joltInstance.program.entry_address
          (source_is_compressed run.bytecode next) run.initialState
    | some last =>
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
        ¬ last.Halts ∧ run.bytecode[next].address = address ∧ run.bytecode[next].starts_source ∧
        pre = advance_pc address (source_is_compressed run.bytecode next) last.postState) :
    pre.sail.regs.get? Register.PC = some run.bytecode[next].address ∧
      pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
        if source_is_compressed run.bytecode next then 2 else 4) := by
  apply untrusted_prepared_pc_at run run.rows.size (by omega) next pre
  simp only [Array.extract_size]
  cases lastIs : run.rows.back? with
  | none => simpa only [lastIs] using entry
  | some last =>
    simp only [lastIs] at entry ⊢
    split at entry
    · rename_i continues
      simpa only [ite_eq_left continues] using entry
    · rename_i terminal
      rw [ite_eq_right terminal]
      obtain ⟨address, nextPC, _, sourceAddress, starts, prepared⟩ := entry
      exact ⟨address, nextPC, sourceAddress, starts, prepared⟩

/-- Every row of an untrusted-answer run begins with PC at its bytecode source
address. For example, the second row of an ECALL expansion still has PC at the
ECALL address. See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
theorem untrusted_row_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) :
    run.rows[i].preState.sail.regs.get? Register.PC =
      some run.bytecode[run.rows[i].rowIndex].address := by
  exact (untrusted_prepared_pc_at run i.val (Nat.le_of_lt i.isLt) _ _
    (untrusted_entry_at run i.val i.isLt)).1

/-- Every row of an untrusted-answer run begins with nextPC prepared to the
source address plus its full 2-byte or 4-byte length. For example, an interior
row of a compressed expansion still starts with address + 2.
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
theorem untrusted_row_next_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size) :
    run.rows[i].preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[run.rows[i].rowIndex].address +
        if source_is_compressed run.bytecode run.rows[i].rowIndex then 2 else 4) := by
  exact (untrusted_prepared_pc_at run i.val (Nat.le_of_lt i.isLt) _ _
    (untrusted_entry_at run i.val i.isLt)).2

/-- Runtime advice changes only the value carried by VirtualAdvice, so it
preserves both control flags. For example, patched DIV advice remains ordinary.
See jolt/tracer/src/instruction/mod.rs:228-254 at ff6fc6568. -/
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
See jolt/tracer/src/emulator/cpu.rs:616-655,692-716 at ff6fc6568. -/
theorem noncontrol_next_pc
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (i : Fin run.rows.size)
    (noJump : JoltMetadata.opcodeFlag
      run.bytecode[run.rows[i].rowIndex].instruction .Jump = false)
    (notBranch : JoltMetadata.instructionFlag
      run.bytecode[run.rows[i].rowIndex].instruction .Branch = false) :
    run.rows[i].postState.sail.regs.get? Register.nextPC =
      some (run.bytecode[run.rows[i].rowIndex].address +
        if source_is_compressed run.bytecode run.rows[i].rowIndex then 2 else 4) := by
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

/-- The final represented branch executes the bytecode branch directly;
runtime advice never changes a branch. For example, a BEQ run uses its BEQ
row rather than a tape answer. See jolt/tracer/src/emulator/cpu.rs:616-655,692-716
at ff6fc6568. -/
theorem stall_branch_runs
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
    branch_instruction_of_flag run.bytecode[last.rowIndex].instruction branch
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
    simpa only [lastRow] using! executed
  rcases isBranch with h | h | h | h | h | h
  all_goals simpa only [h, JoltConstraints.Soundness.execWithTapeAnswer] using executedLast

/-- An executed JALR writes its masked base-plus-immediate target to `nextPC`,
even when it also writes a link register. For example, `jalr x1, -4(x2)`
sets `nextPC` to `(x2 - 4) & ~1`.
See jolt/tracer/src/instruction/jalr.rs:19-30 at ff6fc6568. -/
theorem tape_jalr_target
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm link answer : BitVec 64)
    (pre post : SailJoltState)
    (hnext : pre.sail.regs.get? Register.nextPC = some link)
    (runs : JoltConstraints.Soundness.execWithTapeAnswer (.JALR dst base imm)
      answer pre = .ok (.Retire_Success ()) post) :
    post.sail.regs.get? Register.nextPC =
      some (jolt_jalr_target64 (JoltISA.sourceValue base pre) imm) := by
  have hreadNext : liftSail (LeanRV64D.readReg Register.nextPC) pre = .ok link pre := by
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
    have hpcWrite : liftSail (LeanRV64D.writeReg Register.nextPC target) pre =
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

/-- A selected JALR's aligned lookup output is its 64-bit base-plus-immediate
target. For example, a base of `0x1003` and immediate zero yields `0x1002`.
See jolt/crates/jolt-lookup-tables/src/instructions/riscv/jalr.rs:29-33
at ff6fc6568. -/
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
    joltField context equations cycle slot selected _ raf encoded
    (JoltConstraints.Soundness.addWideIndex_lt value imm) table
  simpa [jolt_jalr_target64, Sail.BitVec.update,
    Sail.BitVec.updateSubrange', BitVec.and_comm,
    BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)] using output

/-- A selected JALR followed by a real cycle places its aligned lookup target
in the next unexpanded PC. For example, a stable `jalr x0, 0(x1)` selects its
own source address as the next unexpanded PC.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:395-403
at ff6fc6568. -/
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
  have relation := equations.nextUnexpandedPCEqLookupIfJump cycle
  rw [jumpFlag, one_mul] at relation
  exact (sub_eq_zero.mp relation).trans
    (selected_jalr_lookup_target joltField joltInstance privateInputs witness
      context equations cycle slot selected row present dst base imm value jump baseAt)

/-- A selected jump writes the source address plus its full source length as
the link value when that addition does not wrap. For example, an uncompressed
JALR at `0x1000` writes `0x1004`.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:345-351
at ff6fc6568. -/
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
      JoltMetadata.circuitFlag, jump] using!
      flags .Jump cycle slot selected
  have compressedFlag : witness.OpFlags .IsCompressed cycle =
      if row.is_compressed then 1 else 0 := by
    simpa only [JoltConstraints.bytecodeCircuitFlag, present,
      JoltMetadata.circuitFlag] using! flags .IsCompressed cycle slot selected
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

/-- A represented branch's register-table entries equal the operands read by
its executed row. For example, BEQ's two entries equal its pre-state sources.
See jolt/crates/jolt-witness/src/witnesses/registers.rs (`Rs1Value::extract`)
at ff6fc6568. -/
theorem represented_last_branch_registers
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
    (lastAt : run.rows[before.val] = last)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot before = 1)
    (rowAt : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (branch : JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true)
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shapes : run.bytecode[last.rowIndex].instruction = .BEQ lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BNE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLT lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLTU lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGEU lhs rhs imm) :
    (witness.RegistersVal (TraceWitness.sourceRegisterAddress lhs) before =
        ((JoltISA.sourceValue lhs last.preState).toNat : F) ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress rhs) before =
        ((JoltISA.sourceValue rhs last.preState).toNat : F)) ∧
    (witness.Rs1Value before = ((JoltISA.sourceValue lhs last.preState).toNat : F) ∧
      witness.Rs2Value before = ((JoltISA.sourceValue rhs last.preState).toNat : F)) := by
  have operands := (branch_operand_forms run.bytecode[last.rowIndex].instruction lhs rhs imm shapes).2
  have nonTemporary := expanded_control_read_not_temporary joltInstance.program
    run.bytecode run.expands run.bytecode[last.rowIndex]
    (Array.getElem_mem_toList last.rowIndex.isLt) (Or.inl branch)
  have values : witness.RegistersVal (TraceWitness.sourceRegisterAddress lhs) before =
        ((JoltISA.sourceValue lhs last.preState).toNat : F) ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress rhs) before =
        ((JoltISA.sourceValue rhs last.preState).toNat : F) := by
    constructor
    · apply represented_last_control_read joltField joltInstance privateInputs witness
        context equations run bytecodeEq represented last before inRun slot selected rowAt
        false lhs
      · exact operands.1
      · rcases shapes with h | h | h | h | h | h
        all_goals
          simp [TraceWitness.Rs1Value, inRun, lastAt]
          simp only [Fin.getElem_fin] at h
          rw [h]
      · exact nonTemporary false _ operands.1
    · apply represented_last_control_read joltField joltInstance privateInputs witness
        context equations run bytecodeEq represented last before inRun slot selected rowAt
        true rhs
      · exact operands.2
      · rcases shapes with h | h | h | h | h | h
        all_goals
          simp [TraceWitness.Rs2Value, inRun, lastAt]
          simp only [Fin.getElem_fin] at h
          rw [h]
      · exact nonTemporary true _ operands.2
  have rowAtContext : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by simpa only [← bytecodeEq] using rowAt
  refine ⟨values, ?_, ?_⟩
  · have read := selected_operand_register
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField) joltInstance
      privateInputs witness context equations before slot selected run.bytecode[last.rowIndex]
      rowAtContext false (TraceWitness.sourceRegisterAddress lhs) operands.1
    exact read.trans values.1
  · have read := selected_operand_register
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField) joltInstance
      privateInputs witness context equations before slot selected run.bytecode[last.rowIndex]
      rowAtContext true (TraceWitness.sourceRegisterAddress rhs) operands.2
    exact read.trans values.2

/-- At the represented last JALR cycle, the base register table equals the
base value read from the recorded pre-state. For example, a retained
`jalr x0, 0(x1)` reads x1's pre-state value.
See jolt/crates/jolt-witness/src/witnesses/registers.rs:1-35 at ff6fc6568. -/
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
  · apply expanded_control_read_not_temporary joltInstance.program run.bytecode run.expands
      run.bytecode[last.rowIndex] (Array.getElem_mem_toList last.rowIndex.isLt)
      (Or.inr ⟨dst, base, imm, jump⟩) false
    rw [jump]
    rfl

end JoltInstance
