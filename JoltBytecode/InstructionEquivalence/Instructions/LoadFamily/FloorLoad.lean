import JoltBytecode.JoltISA.Expansions.LaneWindow
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

namespace LoadFamily

/-- The first row of `laneWindowOpen`, selected by the access width.
For example, word width reads the containing doubleword with `VirtualLoadW`.
Jolt: `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::open`). -/
def floorLoadRow (width : JoltISA.AccessWidth) (dst : JoltISA.Dst)
    (base : JoltISA.Src) (imm : BitVec 64) (faultClass : JoltISA.LoadFaultClass)
    (fault : ExceptionType) : JoltISA.Instr :=
  match JoltISA.laneWindowOpen width dst dst base imm faultClass fault
      (.done RETIRE_SUCCESS) with
  | .instr instruction _ => instruction
  | .done _ => .FENCE

/-- Low effective-address bits that must vanish for the access width.
For example, a word access requires bits zero and one to vanish.
Jolt: `tracer/src/instruction/floor_access.rs` (`addresses`). -/
def alignmentMask : JoltISA.AccessWidth → BitVec 64
  | .byte => 0
  | .halfword => 1
  | .word => 3

/-- A successful floor load writes the containing doubleword into a writable
virtual destination and preserves the rest of the state.
For example, a byte load at address 11 reads the doubleword at address 8.
Jolt: `tracer/src/instruction/floor_access.rs` (`load`). -/
theorem floorLoad_run (width : JoltISA.AccessWidth)
    (vd : JoltISA.VReg) (rs1 : regidx) (imm baseValue value : BitVec 64)
    (faultClass : JoltISA.LoadFaultClass) (fault : ExceptionType) (js : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (halign : (baseValue + imm) &&& alignmentMask width = 0)
    (hmem : JoltISA.Mmu.load_doubleword ((baseValue + imm) &&& ~~~(7 : BitVec 64)) js =
      .ok (.Ok value) js)
    (hwritable : WritableVReg vd) :
    (JoltISA.execInstr
      (floorLoadRow width (.vreg vd) (.xreg rs1) imm faultClass fault)).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js vd value) := by
  unfold WritableVReg at hwritable
  cases width <;>
    simp only [alignmentMask] at halign <;>
    simp only [floorLoadRow, JoltISA.laneWindowOpen, JoltISA.execInstr,
      JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hread]
  all_goals
    simp only [halign, ↓reduceIte, EStateM.bind, hmem]
    simp only [JoltISA.writeDst, writeVReg, hwritable, ↓reduceIte,
      stateAfterVRegWrite, pure, EStateM.pure,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The load assumptions identify the containing doubleword read by each
floor-load width; alignment is required only at that width.
For example, a halfword at address 10 uses the same doubleword facts as a byte
at address 11.
Jolt: `tracer/src/instruction/floor_access.rs` (`load`). -/
theorem floorLoad_of_assumptions (width : JoltISA.AccessWidth)
    (vd : JoltISA.VReg) (hwritable : WritableVReg vd)
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& alignmentMask width = 0) :
    let facts := h.dwordWindowFacts
    let addr := compute_aligned_dword_base_address h.rs1_val imm
    let value := loaded_dword_at js.sail addr facts.bytes facts.aligned.no_ovf
    (JoltISA.execInstr (floorLoadRow width (.vreg vd) (.xreg rs1)
      (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ()))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js vd value) := by
  apply floorLoad_run width vd rs1 _ _ _ _ _ js h.rs1_read halign _ hwritable
  change JoltISA.Mmu.load_doubleword
      (compute_aligned_dword_base_address h.rs1_val imm) js = _
  rw [JoltISA.Mmu.load_doubleword_ram js _ h.dwordWindowFacts.aligned.align
    h.dwordWindowFacts.read_mmio.ram
    (JoltISA.Mmu.effective_address_ok_of_load h.dwordWindowFacts.read_mmio.ram h.jolt_ram)]
  rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail _ h.dwordWindowFacts.bytes
    h.dwordWindowFacts.aligned.no_ovf]

/-- A misaligned floor load raises its supplied exception before any write.
For example, a word access at address 10 reports the fault at address 10.
Jolt: `tracer/src/instruction/floor_access.rs` (`addresses`). -/
theorem floorLoad_misaligned (width : JoltISA.AccessWidth) (dst : JoltISA.Dst)
    (rs1 : regidx) (imm baseValue : BitVec 64) (faultClass : JoltISA.LoadFaultClass)
    (fault : ExceptionType) (js : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hmis : (baseValue + imm) &&& alignmentMask width ≠ 0) :
    (JoltISA.execInstr
      (floorLoadRow width dst (.xreg rs1) imm faultClass fault)).run js =
      .ok (ExecutionResult.Memory_Exception (Virtaddr (baseValue + imm), fault)) js := by
  cases width
  case byte => exact False.elim (hmis (by simp [alignmentMask]))
  all_goals
    simp only [alignmentMask] at hmis
    simp only [floorLoadRow, JoltISA.laneWindowOpen, JoltISA.execInstr,
      JoltISA.readSrc, liftSail, bind, EStateM.bind, EStateM.run, hread]
    simp only [hmis, ↓reduceIte, pure, EStateM.pure]

/-- A misaligned first load stops its entire continuation without running it.
For example, a failing word load does not execute the following mask row. -/
theorem floorLoadBlock_misaligned (width : JoltISA.AccessWidth) (tail : JoltISA.Program)
    (dst : JoltISA.Dst) (rs1 : regidx) (imm baseValue : BitVec 64)
    (faultClass : JoltISA.LoadFaultClass) (fault : ExceptionType) (js : SailJoltState)
    (hread : rX_bits rs1 js.sail = .ok baseValue js.sail)
    (hmis : (baseValue + imm) &&& alignmentMask width ≠ 0) :
    (JoltISA.execProgram
      (.instr (floorLoadRow width dst (.xreg rs1) imm faultClass fault) tail)).run js =
      .ok (ExecutionResult.Memory_Exception (Virtaddr (baseValue + imm), fault)) js :=
  JoltISA.execProgram_instr_run_memory_exception _ tail js js _
    (floorLoad_misaligned width dst rs1 imm baseValue faultClass fault js hread hmis)

/-- A retiring instruction gives a successful singleton program run.
For example, a mask-row execution can be composed with a following extraction. -/
theorem singleRow_run {instruction : JoltISA.Instr} {before after : SailJoltState}
    (h : (JoltISA.execInstr instruction).run before = .ok RETIRE_SUCCESS after) :
    JoltISA.Program.Run (.instr instruction (.done RETIRE_SUCCESS)) before after := by
  unfold JoltISA.Program.Run
  rw [JoltISA.execProgram_instr_run_retire instruction _ before after h]
  rfl

/-- Compose three retiring rows through their two intermediate states.
For example, a floor load, window mask and extraction form a narrow load. -/
theorem threeRows_run {first second third : JoltISA.Instr}
    {before afterFirst afterSecond afterThird : SailJoltState}
    (hfirst : (JoltISA.execInstr first).run before = .ok RETIRE_SUCCESS afterFirst)
    (hsecond : (JoltISA.execInstr second).run afterFirst = .ok RETIRE_SUCCESS afterSecond)
    (hthird : (JoltISA.execInstr third).run afterSecond = .ok RETIRE_SUCCESS afterThird) :
    JoltISA.Program.Run (.instr first (.instr second (.instr third (.done RETIRE_SUCCESS))))
      before afterThird :=
  (singleRow_run hfirst).append ((singleRow_run hsecond).append (singleRow_run hthird))

end LoadFamily
