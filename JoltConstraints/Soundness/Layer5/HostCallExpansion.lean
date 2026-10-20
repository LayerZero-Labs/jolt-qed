import JoltConstraints.Soundness.Assumptions
import JoltConstraints.program_facts
import JoltConstraints.expansion_facts

/-! The approved source-level HostIO destination restriction reaches every
HostIO row of the expanded bytecode. Generated instruction sequences contain
no HostIO row, and a direct HostIO source row rewrites x0 to temporary 40. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem host_source_native_destination
    (source : SourceInstruction) (dst : Dst) (src : Src) (imm : BitVec 64)
    (restricted : match source with
      | .jolt (.VirtualHostIO rd _ _) => isX0 rd = true
      | _ => True)
    (expands : source.expand = some (.native (.VirtualHostIO dst src imm))) :
    dst = .vreg rdZeroRewriteVReg := by
  cases source with
  | riscv instruction =>
    cases instruction <;>
      simp_all [SourceInstruction.expand, ExpandedSource.ofNative,
        ExpandedSource.ofProgram, ExpandedSource.ofPureProgram, Instr.rewriteNative,
        Instr.destination?, JoltISA.Encoded.AUIPC, JoltISA.Encoded.BEQ,
        JoltISA.Encoded.BNE, JoltISA.Encoded.BLT, JoltISA.Encoded.BGE,
        JoltISA.Encoded.BLTU, JoltISA.Encoded.BGEU] <;>
      split_ifs at expands <;> cases expands
  | jolt instruction =>
    cases instruction <;>
      simp_all [SourceInstruction.expand, ExpandedSource.ofNative,
        ExpandedSource.ofProgram, Instr.rewriteNative, sideEffectingDst,
        sideEffectingRdZeroDst, Instr.destination?, JoltISA.Encoded.VirtualAssertEQ] <;>
      split_ifs at expands <;> cases expands

private def NotHostIO : Instr → Prop
  | .VirtualHostIO _ _ _ => False
  | _ => True

private theorem sequenceRowOk_no_host (instruction : Instr)
    (ok : ExpansionFacts.sequenceRowOk instruction = true) :
    NotHostIO instruction := by
  cases instruction <;> simp only [NotHostIO]
  simp [ExpansionFacts.sequenceRowOk] at ok

private theorem rowsOk_no_host (instructions : List Instr)
    (ok : ExpansionFacts.rowsOk instructions = true) :
    ∀ instr ∈ instructions, NotHostIO instr := by
  induction instructions with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil =>
      have headOk : ExpansionFacts.sequenceRowOk head = true := by
        simpa only [ExpansionFacts.rowsOk] using ok
      intro instr member
      simp only [List.mem_singleton] at member
      subst instr
      exact sequenceRowOk_no_host head headOk
    | cons next rest =>
      have headOk : ExpansionFacts.sequenceRowOk head = true := by
        simp only [ExpansionFacts.rowsOk, Bool.and_eq_true] at ok
        exact ok.1.1
      have tailOk : ExpansionFacts.rowsOk (next :: rest) = true := by
        simp only [ExpansionFacts.rowsOk, Bool.and_eq_true] at ok
        exact ok.2
      intro instr member
      rcases List.mem_cons.mp member with same | later
      · subst instr
        exact sequenceRowOk_no_host head headOk
      · exact ih tailOk instr later

private theorem host_not_in_sequence (source : SourceInstruction)
    (instructions : List Instr)
    (expands : source.expand = some (.sequence instructions)) :
    ∀ instr ∈ instructions, NotHostIO instr := by
  have good := ExpansionFacts.expand_ok source (.sequence instructions) expands
  simp only [ExpansionFacts.ExpandedOk, ExpansionFacts.sequenceOk, Bool.and_eq_true] at good
  exact rowsOk_no_host instructions good.1.1

private theorem host_expanded_destination
    (sourceRow : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow)
    (expanded : expand_instruction sourceRow = some rows)
    (restricted : match sourceRow.instruction with
      | .jolt (.VirtualHostIO rd _ _) => isX0 rd = true
      | _ => True)
    (row : JoltInstructionRow) (member : row ∈ rows)
    (dst : Dst) (src : Src) (imm : BitVec 64)
    (instruction : row.instruction = .VirtualHostIO dst src imm) :
    dst = .vreg rdZeroRewriteVReg := by
  obtain ⟨k, inRange, atK⟩ := List.mem_iff_getElem.mp member
  rw [← atK] at instruction
  unfold expand_instruction at expanded
  split at expanded
  · cases expanded
  · next expandedSource instruction' =>
    cases expanded
    simp only [List.length_singleton] at inRange
    have kZero : k = 0 := by omega
    subst kZero
    simp only [List.getElem_cons_zero] at instruction
    exact host_source_native_destination sourceRow.instruction dst src imm restricted
      (by rw [instruction] at instruction'; exact instruction')
  · split at expanded
    · cases expanded
    · next expansionEq condition =>
      rename_i sourceExpansion sequenceInstructions
      cases expanded
      have kLt : k < sequenceInstructions.length := by
        simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using inRange
      have instructionAt : sequenceInstructions[k] = Instr.VirtualHostIO dst src imm := by
        simpa only [stamp_sequence, List.getElem_map, List.getElem_zipIdx] using instruction
      have absent := host_not_in_sequence sourceRow.instruction sequenceInstructions expansionEq
        sequenceInstructions[k] (List.getElem_mem kLt)
      rw [instructionAt] at absent
      exact False.elim absent

/-- A source program whose HostIO calls name x0 has only temporary-40 HostIO
destinations after expansion. This also rules out HostIO inside generated
sequences, without an additional program premise. -/
theorem host_program_destination
    (image : Rv64ProgramImage SourceInstruction)
    (restricted : image.HostCallRdZero)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList)
    (dst : Dst) (src : Src) (imm : BitVec 64)
    (instruction : row.instruction = .VirtualHostIO dst src imm) :
    dst = .vreg rdZeroRewriteVReg := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none =>
    rw [mapped] at expanded
    cases expanded
  | some instructions =>
    rw [mapped, Option.map_some, Option.some.injEq] at expanded
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ instructions mapped
    have listEq : bytecode.toList = instructions.flatten := by
      rw [← expanded, List.toList_toArray]
    rw [listEq] at member
    obtain ⟨rows, inInstructions, inRows⟩ := List.mem_flatten.mp member
    obtain ⟨k, inRange, atK⟩ := List.mem_iff_getElem.mp inInstructions
    have sourceIn : k < image.instructions.size := by
      rw [← Array.length_toList, ← lengths]
      exact inRange
    have expandedSource : expand_instruction image.instructions[k] = some rows := by
      have step := steps k (by rw [Array.length_toList]; exact sourceIn) inRange
      rw [Array.getElem_toList sourceIn, atK] at step
      exact step
    have restrictedSource :
        match image.instructions[k].instruction with
        | .jolt (.VirtualHostIO rd _ _) => isX0 rd = true
        | _ => True := by
      exact restricted image.instructions[k] (Array.getElem_mem sourceIn)
    exact host_expanded_destination image.instructions[k] rows expandedSource
      restrictedSource row inRows dst src imm instruction

end JoltConstraints.Soundness
