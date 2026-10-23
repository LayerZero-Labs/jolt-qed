import JoltConstraints.Soundness.Layer6.PlainRow
import JoltConstraints.Soundness.Layer6.RowStepJalr
import JoltConstraints.Soundness.Layer6.RowStepTerminal
import JoltConstraints.Soundness.Layer6.RowStepMemory

/-! The small row classification and staged non-plain extension rules. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- Preparation after a certified prefix fixes PC and nextPC before the new row
executes; for example, ECALL's final JALR still has ECALL's prepared source PCs.
See jolt/tracer/src/emulator/cpu.rs (`Cpu::tick`) at 5def437f. -/
theorem RawRowEntry.prepared_pc
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {run : UntrustedAnswerRun inst inputs} {next : Fin run.bytecode.size}
    {pre : SailJoltState} (entry : RawRowEntry run next pre) :
    pre.sail.regs.get? Register.PC = some run.bytecode[next].address ∧
      pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
        if source_is_compressed run.bytecode next then 2 else 4) :=
  untrusted_prepared_pc run next pre entry

/-- Every row is plain or one of the five excluded kinds.
For example, AND is plain, while LD has an explicit load branch here. -/
theorem row_kind (instruction : Instr) :
    PlainRow instruction ∨
    (∃ fault destination base imm, instruction = .LD fault destination base imm) ∨
    (∃ base source imm, instruction = .SD base source imm) ∨
    instruction = .VirtualHostIO ∨
    (∃ destination imm, instruction = .JAL destination imm) ∨
    (∃ destination base imm, instruction = .JALR destination base imm) := by
  unfold PlainRow
  split
  · exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))
  · exact Or.inl True.intro

/-- A non-ordinary row can be selected in an unfinished block only as its final
row; for example, ECALL's JALR is selected after its preceding setup rows.
Here ordinary excludes jumps, branches and HostIO.
See jolt/crates/jolt-program/src/expand/metadata.rs (`stamp_sequence_metadata`)
at 5def437f. -/
theorem expansion_nonordinary_terminal
    (image : Rv64ProgramImage SourceInstruction) (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (first : Fin bytecode.size) (starts : bytecode[first].starts_source = true)
    (done : Nat) (unfinished : done < expansionRowCount bytecode first)
    (row : JoltInstructionRow) (atRow : bytecode[first.val + done]? = some row)
    (nonordinary : ExpansionFacts.ordinary row.instruction = false) :
    done + 1 = expansionRowCount bytecode first := by
  obtain ⟨inside, same⟩ := Array.getElem?_eq_some_iff.mp atRow
  have ok := ExpansionRows.expand_program_rowOk image bytecode expanded row
    (same ▸ Array.getElem_mem_toList inside)
  have terminal := ok.ends nonordinary
  have remaining : row.virtual_sequence_remaining.getD 0 = 0 := by
    simpa [JoltInstructionRow.continues] using terminal
  by_contra different
  exact expansion_row_remaining image bytecode expanded first starts done (by omega) row atRow remaining

section Steps

variable {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN inst.program run.rows n)
    (bound : run.rows.size < params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState)
    (indexIs : next.val = first.val + done) (entry : RawRowEntry run next pre)
    (registers : RegisterAgreementOn (ExpansionLive context.bytecode first done)
      witness ⟨run.rows.size, bound⟩ pre)

include joltField assumptions restrictions equations state unfinished honestAdvice indexIs entry registers

/-- An ordinary-RAM LD appends its executed row and preserves the expansion
invariant using only live register agreement; for example, LD may read a base
temporary initialized by an earlier expansion row.
The future proof ports `ld_ram_step` and supplies the shared append contract.
See jolt/tracer/src/instruction/ld.rs (`LD::exec`) at 5def437f. -/
theorem ld_ram_row_step {fault : LoadFaultClass} {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat) :
    PlainRowExtension witness context run first done bound := by
  exact append_ld_row joltField assumptions restrictions witness context equations run first done state
    unfinished honestAdvice bound next pre indexIs entry registers instruction

/-- A device LD appends a load from below RAM and preserves the cut invariant;
for example, an aligned input load reads the agreed input word.
The future proof uses `ld_device_step` with the prefix's restrictions and live base.
See jolt/common/src/jolt_device.rs (`JoltDevice::load`) at 5def437f. -/
theorem ld_device_row_step {fault : LoadFaultClass} {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm)
    (belowRam : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS) :
    PlainRowExtension witness context run first done bound := by
  exact append_ld_row joltField assumptions restrictions witness context equations run first done state
    unfinished honestAdvice bound next pre indexIs entry registers instruction

/-- An ordinary-RAM SD appends its store and preserves the expansion invariant;
for example, a store through an initialized temporary changes one RAM word.
The future proof ports `sd_ram_step_agreement` to live source registers.
See jolt/tracer/src/instruction/sd.rs (`SD::exec`) at 5def437f. -/
theorem sd_ram_row_step {base source : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .SD base source imm)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat) :
    PlainRowExtension witness context run first done bound := by
  exact append_sd_row joltField assumptions restrictions witness context equations run first done state
    unfinished honestAdvice bound next pre indexIs entry registers instruction

/-- A device SD appends its store with the conditional termination invariant;
for example, an output store preserves termination, while a termination store
ends the obligation that its table word remain zero.
The future proof uses `sd_device_step` and the generalized append constructor.
See jolt/common/src/jolt_device.rs (`JoltDevice::store`) at 5def437f. -/
theorem sd_device_row_step {base source : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .SD base source imm)
    (belowRam : (sourceValue base pre + imm).toNat < RAM_START_ADDRESS) :
    PlainRowExtension witness context run first done bound := by
  exact append_sd_row joltField assumptions restrictions witness context equations run first done state
    unfinished honestAdvice bound next pre indexIs entry registers instruction

/-- A terminal HostIO row appends the call certified by `HostCallsSucceed` and
keeps live-register agreement; for example, an advice-write call changes the tape.
Porting `host_call_selected_step` to live agreement belongs to the future proof.
See jolt/tracer/src/instruction/virtual_host_io.rs (`VirtualHostIO::exec`) at 5def437f. -/
theorem host_row_step
    (instruction : run.bytecode[next].instruction = .VirtualHostIO)
    (terminal : done + 1 = expansionRowCount context.bytecode first) :
    PlainRowExtension witness context run first done bound := by
  exact append_host_row joltField restrictions witness context equations run first done state
    unfinished honestAdvice bound next pre indexIs entry registers instruction

variable (pc : pre.sail.regs.get? Register.PC = some run.bytecode[next].address)
    (nextPC : pre.sail.regs.get? Register.nextPC = some (run.bytecode[next].address +
      if source_is_compressed run.bytecode next then 2 else 4))

include pc nextPC

/-- A terminal JAL appends its jump and retains the expansion invariant;
for example, a singleton self-JAL can complete the block at a stable stall.
The future proof ports `jal_step` to live agreement and uses the existing no-wrap
assumption; PC preparation is supplied before execution, not from the new run.
See jolt/tracer/src/instruction/jal.rs (`JAL::exec`) at 5def437f. -/
theorem jal_row_step {destination : Dst} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .JAL destination imm)
    (terminal : done + 1 = expansionRowCount context.bytecode first) :
    PlainRowExtension witness context run first done bound := by
  exact append_jal_row joltField assumptions witness context equations run first done state
    unfinished bound next pre indexIs entry registers pc nextPC instruction

/-- A terminal JALR appends its indirect jump using a live base register;
for example, ECALL's final JALR reads its initialized virtual mtvec base.
The future proof must supply the missing Layer 5 rule and the shared append facts.
See jolt/tracer/src/instruction/jalr.rs (`JALR::exec`) at 5def437f. -/
theorem jalr_row_step {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .JALR destination base imm)
    (terminal : done + 1 = expansionRowCount context.bytecode first) :
    PlainRowExtension witness context run first done bound := by
  exact append_jalr_row joltField assumptions witness context equations run first done state
    unfinished bound next pre indexIs entry registers nextPC instruction

end Steps

end JoltInstance
