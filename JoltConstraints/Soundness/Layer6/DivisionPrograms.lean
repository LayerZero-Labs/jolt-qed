import JoltConstraints.Soundness.Layer6.DivisionDefs
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divuw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Rem
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remuw
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionFrame

/-! Results and honest reruns of the eight generated division programs. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

private theorem division_source_read (pre : SailJoltState)
    (present : AllRegistersPresent pre.sail) (rs : regidx) :
    rX_bits rs pre.sail = .ok (sourceValue (.xreg rs) pre) pre.sail := by
  obtain ⟨value, read⟩ := (readable_of_present pre.sail present rs).exists_value
  have lifted := readSrc_xreg_run_of_read rs pre value read
  rw [(lookup_readSrc_value _ _ _ _ lifted).2] at read
  exact read

private theorem division_result_of_unique_advice
    (program : BitVec 64 → Program) (q honest : BitVec 64)
    (pre post : SailJoltState) (expected : SailState)
    (runs : Program.Run (program q) pre post) (unique : q = honest)
    (concrete : ∃ final, Program.Run (program honest) pre final ∧
      final.sail = expected) : post.sail = expected := by
  obtain ⟨final, honestRun, finalResult⟩ := concrete
  subst q
  have equal : post = final := by
    change (execProgram (program honest)).run pre = .ok RETIRE_SUCCESS post at runs
    change (execProgram (program honest)).run pre = .ok RETIRE_SUCCESS final at honestRun
    rw [runs] at honestRun
    cases honestRun
    rfl
  exact congrArg SailJoltState.sail equal |>.trans finalResult

/-- Equality of the device, tape, host settings, and virtual registers outside
instruction temporaries between two states.
For example, writing virtual register 40 preserves this relation. -/
def DivisionFrame (before after : SailJoltState) : Prop :=
  after.jolt_device = before.jolt_device ∧
  after.adviceTape = before.adviceTape ∧
  after.hostIO = before.hostIO ∧
  ∀ register : BitVec 7, ¬ IsInstructionTemporary register.toFin →
    after.vregs register = before.vregs register

/-- A state preserves its own division frame; for example, a zero-row prefix
leaves the device, tape, host settings, and persistent virtual registers equal. -/
theorem divisionFrame_refl (state : SailJoltState) : DivisionFrame state state :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Two consecutive division frames compose; for example, two temporary writes
leave the same persistent virtual registers as before both writes. -/
theorem divisionFrame_trans (a b c : SailJoltState)
    (ab : DivisionFrame a b) (bc : DivisionFrame b c) : DivisionFrame a c := by
  exact ⟨bc.1.trans ab.1, bc.2.1.trans ab.2.1,
    bc.2.2.1.trans ab.2.2.1,
    fun register persistent => (bc.2.2.2 register persistent).trans
      (ab.2.2.2 register persistent)⟩

private theorem divisionFrame_sail (state : SailJoltState) (after : SailState) :
    DivisionFrame state { state with sail := after } :=
  divisionFrame_refl state

/-- An architectural destination or an instruction temporary destination.
For example, x5 and virtual register 40 qualify, while virtual register 48 does not. -/
def DivisionDestinationSafe : Dst → Prop
  | .xreg _ => True
  | .vreg register => IsInstructionTemporary register.toFin

/-- A division arithmetic row whose destination, if present, is safe.
For example, REM's multiplication into virtual register 43 qualifies. -/
def DivisionInstructionSafe (instr : Instr) : Prop :=
  DivisionArithmeticRow instr ∧
  match instr.destination? with
  | some dst => DivisionDestinationSafe dst
  | none => True

/-- A safe division instruction is arithmetic and has a safe destination.
For example, REM's multiplication into temporary 43 has both properties. -/
theorem divisionInstructionSafe_parts (instr : Instr)
    (safe : DivisionInstructionSafe instr) :
    DivisionArithmeticRow instr ∧
    ∀ dst, instr.destination? = some dst → DivisionDestinationSafe dst := by
  refine ⟨safe.1, ?_⟩
  intro dst destination
  unfold DivisionInstructionSafe at safe
  rw [destination] at safe
  exact safe.2

/-- Every instruction in a list is a safe division arithmetic row.
For example, REM's VirtualAdvice and MUL prefix satisfies this predicate. -/
def DivisionRows : List Instr → Prop
  | [] => True
  | instr :: rest => DivisionInstructionSafe instr ∧ DivisionRows rest

private def DivisionFrameFor (keepSail : Bool) (before after : SailJoltState) : Prop :=
  DivisionFrame before after ∧ (keepSail = true → after.sail = before.sail)

private def DivisionDestinationSafeFor (keepSail : Bool) : Dst → Prop
  | .xreg _ => keepSail = false
  | .vreg register => IsInstructionTemporary register.toFin

private def DivisionInstructionSafeFor (keepSail : Bool) (instr : Instr) : Prop :=
  DivisionArithmeticRow instr ∧
  ∀ dst, instr.destination? = some dst → DivisionDestinationSafeFor keepSail dst

private def DivisionRowsFor (keepSail : Bool) : List Instr → Prop
  | [] => True
  | instr :: rest => DivisionInstructionSafeFor keepSail instr ∧ DivisionRowsFor keepSail rest

private theorem divisionFrameFor_refl (keepSail : Bool) (state : SailJoltState) :
    DivisionFrameFor keepSail state state := ⟨divisionFrame_refl state, fun _ => rfl⟩

private theorem divisionFrameFor_trans (keepSail : Bool) (a b c : SailJoltState)
    (ab : DivisionFrameFor keepSail a b) (bc : DivisionFrameFor keepSail b c) :
    DivisionFrameFor keepSail a c :=
  ⟨divisionFrame_trans a b c ab.1 bc.1,
    fun h => (bc.2 h).trans (ab.2 h)⟩

private theorem divisionFrame_read (keepSail : Bool) (src : Src) :
    StatePreservation.Preserves (DivisionFrameFor keepSail) (readSrc src) := by
  cases src with
  | vreg register =>
    intro before after value runs
    simp only [readSrc, readVReg, get, getThe, MonadStateOf.get] at runs
    cases runs
    exact divisionFrameFor_refl keepSail before
  | xreg register =>
    exact StatePreservation.liftSail_rule (sailRelation := fun before after => after = before)
      (fun state after equal => ⟨divisionFrame_sail state after, fun _ => equal⟩)
      (fun before after value runs => rX_bits_pure register before value after runs)

private theorem divisionFrame_write (keepSail : Bool) (dst : Dst)
    (safe : DivisionDestinationSafeFor keepSail dst)
    (value : BitVec 64) :
    StatePreservation.Preserves (DivisionFrameFor keepSail) (writeDst dst value) := by
  cases dst with
  | xreg register =>
    simp only [DivisionDestinationSafeFor] at safe
    subst keepSail
    exact StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
      (fun state after _ => ⟨divisionFrame_sail state after, by simp⟩)
      (fun _ _ _ _ => True.intro)
  | vreg register =>
    intro before after result runs
    simp only [writeDst, writeVReg] at runs
    split at runs
    · cases runs
    · cases runs
      refine ⟨⟨rfl, rfl, rfl, ?_⟩, fun _ => rfl⟩
      intro other persistent
      simp only
      split_ifs with same
      · subst other
        exact False.elim (persistent safe)
      · rfl

private theorem divisionFrame_instr_for (keepSail : Bool) (instr : Instr)
    (arithmetic : DivisionArithmeticRow instr)
    (safe : ∀ dst, instr.destination? = some dst → DivisionDestinationSafeFor keepSail dst) :
    StatePreservation.Preserves (DivisionFrameFor keepSail) (execInstr instr) := by
  cases instr <;> simp [DivisionArithmeticRow] at arithmetic
  all_goals simp only [execInstr]
  all_goals preservation_auto [divisionFrame_read keepSail _,
    divisionFrame_write keepSail _ (safe _ rfl) _,
    StatePreservation.pure_rule (divisionFrameFor_refl keepSail) _,
    StatePreservation.throw_rule (DivisionFrameFor keepSail) _]
    using (StatePreservation.bind_rule (divisionFrameFor_trans keepSail))

/-- Executing a safe arithmetic instruction preserves the division frame.
For example, REM's multiplication can change temporary 43 while retaining the
device, tape, host settings, and persistent virtual registers. -/
theorem divisionFrame_instr (instr : Instr)
    (arithmetic : DivisionArithmeticRow instr)
    (safe : ∀ dst, instr.destination? = some dst → DivisionDestinationSafe dst) :
    StatePreservation.Preserves DivisionFrame (execInstr instr) := by
  intro before after value runs
  have safeFor : ∀ dst, instr.destination? = some dst →
      DivisionDestinationSafeFor false dst := by
    intro dst atDst
    cases dst with
    | xreg _ => rfl
    | vreg register => exact safe _ atDst
  exact (divisionFrame_instr_for false instr arithmetic safeFor before after value runs).1

private theorem divisionFrame_program_for (keepSail : Bool) (program : Program)
    (rows : DivisionRowsFor keepSail program.instrs)
    (pre post : SailJoltState) (runs : Program.Run program pre post) :
    DivisionFrameFor keepSail pre post := by
  induction program generalizing pre post with
  | done result =>
    simp only [Program.Run, execProgram_done, EStateM.run, pure, EStateM.pure] at runs
    cases runs
    exact divisionFrameFor_refl keepSail pre
  | instr instr rest ih =>
    change DivisionInstructionSafeFor keepSail instr ∧
      DivisionRowsFor keepSail rest.instrs at rows
    obtain ⟨head, tail⟩ := rows
    obtain ⟨middle, first, remaining⟩ :=
      execProgram_instr_run_retire_inv instr rest pre post runs
    exact divisionFrameFor_trans keepSail pre middle post
      (divisionFrame_instr_for keepSail instr head.1 head.2 pre middle _ first)
      (ih tail middle post remaining)

private theorem DivisionRows.forFalse {rows : List Instr}
    (safe : DivisionRows rows) : DivisionRowsFor false rows := by
  induction rows with
  | nil => trivial
  | cons instr rest ih =>
    change DivisionInstructionSafe instr ∧ DivisionRows rest at safe
    change DivisionInstructionSafeFor false instr ∧ DivisionRowsFor false rest
    refine ⟨?_, ih safe.2⟩
    obtain ⟨arithmetic, destination⟩ := divisionInstructionSafe_parts instr safe.1
    exact ⟨arithmetic, fun dst atDst => by
      cases dst with
      | xreg _ => rfl
      | vreg register => exact destination _ atDst⟩

/-- A successful program of safe division rows preserves the division frame.
For example, REM's generated program keeps device and persistent virtual
registers unchanged even when its quotient advice changes temporary 40. -/
theorem divisionFrame_program (program : Program)
    (rows : DivisionRows program.instrs)
    (pre post : SailJoltState) (runs : Program.Run program pre post) :
    DivisionFrame pre post := by
  exact (divisionFrame_program_for false program
    (DivisionRows.forFalse rows) pre post runs).1

private theorem division_temporary_facts :
    IsInstructionTemporary (40 : Fin 128) ∧
    IsInstructionTemporary (41 : Fin 128) ∧
    IsInstructionTemporary (42 : Fin 128) ∧
    IsInstructionTemporary (43 : Fin 128) ∧
    IsInstructionTemporary (44 : Fin 128) ∧
    IsInstructionTemporary (45 : Fin 128) ∧
    IsInstructionTemporary (46 : Fin 128) ∧
    IsInstructionTemporary (47 : Fin 128) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [IsInstructionTemporary, joltRegisterSlot]

private theorem division_program_rows_shape (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) :
    DivisionRows (kind.program rd rs1 rs2 q).instrs ∧
      DivisionRowsFor true (kind.program rd rs1 rs2 q).instrs.dropLast := by
  obtain ⟨t40, t41, t42, t43, t44, t45, t46, t47⟩ := division_temporary_facts
  cases kind <;>
    simp only [DivisionKind.program, divProgramAuto, divuProgramAuto, divwProgramAuto,
      divuwProgramAuto, remProgramAuto, remuProgramAuto, remwProgramAuto,
      remuwProgramAuto]
  all_goals by_cases hzero : isX0 rd = true
  all_goals simp only [hzero, ite_true, Program.instrs]
  all_goals simp [Program.instrs, DivisionRows, DivisionRowsFor,
    DivisionInstructionSafeFor, DivisionDestinationSafeFor,
    Encoded.ADDI, DivisionInstructionSafe, DivisionArithmeticRow,
    Instr.destination?, DivisionDestinationSafe, List.dropLast,
    t40, t41, t42, t43, t44, t45, t46, t47]

/-- Every generated division program consists of safe arithmetic rows.
For example, REM's virtual writes use instruction temporaries and its final
architectural write is permitted by `DivisionDestinationSafe`. -/
theorem division_program_rows (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) :
    DivisionRows (kind.program rd rs1 rs2 q).instrs :=
  (division_program_rows_shape kind rd rs1 rs2 q).1

private theorem DivisionRowsFor.take {keepSail : Bool} {rows : List Instr}
    (safe : DivisionRowsFor keepSail rows) (n : Nat) :
    DivisionRowsFor keepSail (rows.take n) := by
  induction n generalizing rows with
  | zero => simp [DivisionRowsFor]
  | succ n ih =>
    cases rows with
    | nil => simp [DivisionRowsFor]
    | cons instr rest =>
      change DivisionInstructionSafeFor keepSail instr ∧
        DivisionRowsFor keepSail rest at safe
      change DivisionInstructionSafeFor keepSail instr ∧
        DivisionRowsFor keepSail (rest.take n)
      exact ⟨safe.1, ih safe.2⟩

/-- The instructions of a straight-line program are its input list.
For example, sequencing REM's advice and multiplication rows returns those
two instructions in that order. -/
theorem divisionProgram_instrs_seq (rows : List Instr) :
    (Program.seq rows).instrs = rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    change head :: (Program.seq tail).instrs = head :: tail
    exact congrArg (head :: ·) ih

private theorem DivisionRowsFor.at {keepSail : Bool} {rows : List Instr}
    (safe : DivisionRowsFor keepSail rows) (offset : Nat)
    (inside : offset < rows.length) :
    DivisionInstructionSafeFor keepSail rows[offset] := by
  induction rows generalizing offset with
  | nil => simp at inside
  | cons instr rest ih =>
    change DivisionInstructionSafeFor keepSail instr ∧
      DivisionRowsFor keepSail rest at safe
    cases offset with
    | zero => exact safe.1
    | succ offset => exact ih safe.2 offset (by simp at inside; omega)

/-- One generated division row preserves the device and persistent registers;
unless it is the last row, it also leaves Sail unchanged.
For example, REM's prefix multiplication may write temporary 43. -/
theorem division_program_row_frame (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) (offset : Nat)
    (inside : offset < (kind.program rd rs1 rs2 q).instrs.length)
    (pre post : SailJoltState)
    (runs : execInstr (kind.program rd rs1 rs2 q).instrs[offset] pre =
      .ok RETIRE_SUCCESS post) :
    DivisionFrame pre post ∧
      (offset + 1 < (kind.program rd rs1 rs2 q).instrs.length → post.sail = pre.sail) := by
  let rows := (kind.program rd rs1 rs2 q).instrs
  change offset < rows.length at inside
  change execInstr rows[offset] pre = .ok RETIRE_SUCCESS post at runs
  have allSafe := (division_program_rows_shape kind rd rs1 rs2 q).1
  change DivisionRows rows at allSafe
  have rowSafe := DivisionRowsFor.at (DivisionRows.forFalse allSafe) offset inside
  have full := divisionFrame_instr_for false rows[offset] rowSafe.1 rowSafe.2
    pre post _ runs
  refine ⟨full.1, ?_⟩
  intro proper
  change offset + 1 < rows.length at proper
  have prefixSafe := (division_program_rows_shape kind rd rs1 rs2 q).2
  change DivisionRowsFor true rows.dropLast at prefixSafe
  have dropInside : offset < rows.dropLast.length := by
    simp [List.length_dropLast]
    omega
  have same : rows.dropLast[offset] = rows[offset] := by
    simp [List.dropLast_eq_take]
  have safe := DivisionRowsFor.at prefixSafe offset dropInside
  rw [same] at safe
  exact (divisionFrame_instr_for true rows[offset] safe.1 safe.2
    pre post _ runs).2 rfl

/-- Executing a proper instruction prefix of a generated division program
preserves the device, tape, host settings, persistent virtual registers, and
the entire Sail state.
For example, executing REM's advice and multiplication rows before its final
architectural write leaves the input Sail state unchanged. -/
theorem division_program_prefix_frame (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (q : BitVec 64) (n : Nat)
    (proper : n < (kind.program rd rs1 rs2 q).instrs.length)
    (pre post : SailJoltState)
    (runs : Program.Run (Program.seq ((kind.program rd rs1 rs2 q).instrs.take n)) pre post) :
    DivisionFrame pre post ∧ post.sail = pre.sail := by
  let rows := (kind.program rd rs1 rs2 q).instrs
  change n < rows.length at proper
  have prefixSafe : DivisionRowsFor true (rows.take n) := by
    have safe := (division_program_rows_shape kind rd rs1 rs2 q).2
    change DivisionRowsFor true rows.dropLast at safe
    rw [List.dropLast_eq_take] at safe
    have same : rows.take n = (rows.take (rows.length - 1)).take n := by
      simp only [List.take_take]
      congr 1
      omega
    rw [same]
    exact safe.take n
  have frame := divisionFrame_program_for true (Program.seq (rows.take n))
    (by rwa [divisionProgram_instrs_seq]) pre post runs
  exact ⟨frame.1, frame.2 rfl⟩

/-- Any successful generated division run has its architectural Sail result.
For example, REM of 7 by zero writes 7 even with quotient advice 5.
The result follows from the eight instruction-equivalence program theorems. -/
theorem division_program_result (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (q : BitVec 64) (pre post : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (runs : Program.Run (kind.program rd rs1 rs2 q) pre post) :
    post.sail = stateAfterWrite pre.sail rd
      (kind.result (sourceValue (.xreg rs1) pre) (sourceValue (.xreg rs2) pre)) := by
  let dividend := sourceValue (.xreg rs1) pre
  let divisor := sourceValue (.xreg rs2) pre
  have hrs1 := division_source_read pre present rs1
  have hrs2 := division_source_read pre present rs2
  cases kind with
  | div =>
    exact division_result_of_unique_advice (divProgramAuto rd rs1 rs2) q
      (sail_div_value dividend divisor false) pre post _ runs
      (divProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs)
      (divProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero)
  | divu =>
    exact division_result_of_unique_advice (divuProgramAuto rd rs1 rs2) q
      (sail_div_value dividend divisor true) pre post _ runs
      (divuProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs)
      (divuProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero)
  | divw =>
    exact division_result_of_unique_advice (divwProgramAuto rd rs1 rs2) q
      (divw_advice_value dividend divisor) pre post _ runs
      (divwProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs)
      (divwProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero)
  | divuw => exact divuwProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs
  | rem => exact remProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs
  | remu => exact remuProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs
  | remw => exact remwProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs
  | remuw => exact remuwProgram_sound rs2 rs1 rd q pre dividend divisor hrs1 hrs2 nonzero post runs

private theorem division_honest_concrete (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (pre : SailJoltState)
    (present : AllRegistersPresent pre.sail) :
    ∃ honestPost,
      Program.Run (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre))
        pre honestPost ∧
      honestPost.sail = stateAfterWrite pre.sail rd
        (kind.result (sourceValue (.xreg rs1) pre)
          (sourceValue (.xreg rs2) pre)) := by
  let dividend := sourceValue (.xreg rs1) pre
  let divisor := sourceValue (.xreg rs2) pre
  have hrs1 := division_source_read pre present rs1
  have hrs2 := division_source_read pre present rs2
  cases kind with
  | div =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      divProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | divu =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      divuProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | divw =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      divwProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | divuw =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      divuwProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | rem =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      remProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | remu =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      remuProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | remw =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      remwProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero
  | remuw =>
    simpa [DivisionKind.program, DivisionKind.honestAdvice, DivisionKind.source,
      DivisionKind.result, SourceInstruction.honestTracerAdvice] using
      remuwProgram_concrete rs2 rs1 rd pre dividend divisor hrs1 hrs2 nonzero

/-- An honest generated division run has the same final state as a witness run
outside instruction temporaries; for example, two REM quotients may differ at
temporary 40 while both runs leave persistent virtual register 48 unchanged. -/
theorem division_program_honest (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (nonzero : rd ≠ .Regidx 0) (q : BitVec 64) (pre witnessPost : SailJoltState)
    (present : AllRegistersPresent pre.sail)
    (runs : Program.Run (kind.program rd rs1 rs2 q) pre witnessPost)
    (result : witnessPost.sail = stateAfterWrite pre.sail rd
      (kind.result (sourceValue (.xreg rs1) pre) (sourceValue (.xreg rs2) pre))) :
    ∃ honestPost : SailJoltState,
      Program.Run (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost ∧
      DivisionFinalAgreement witnessPost honestPost := by
  obtain ⟨honestPost, honestRun, honestResult⟩ :=
    division_honest_concrete kind rd rs1 rs2 nonzero pre present
  have witnessFrame := divisionFrame_program (kind.program rd rs1 rs2 q)
    (division_program_rows kind rd rs1 rs2 q) pre witnessPost runs
  have honestFrame := divisionFrame_program
    (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre))
    (division_program_rows kind rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre))
    pre honestPost honestRun
  refine ⟨honestPost, honestRun, ?_⟩
  exact ⟨honestResult.trans result.symm,
    honestFrame.1.trans witnessFrame.1.symm,
    honestFrame.2.1.trans witnessFrame.2.1.symm,
    honestFrame.2.2.1.trans witnessFrame.2.2.1.symm,
    fun register persistent =>
      (honestFrame.2.2.2 register persistent).trans
        (witnessFrame.2.2.2 register persistent).symm⟩

end JoltInstance
