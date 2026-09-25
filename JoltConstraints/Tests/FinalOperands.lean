import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.witness_helpers.ram_address
import JoltConstraints.Constraints.BytecodeReadSelectors

set_option autoImplicit false
set_option maxRecDepth 4096

namespace FinalOperandChecks

-- Rust e012da54: inline emit_i accepts a u64, and ADDI executes that full word.
-- https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/inline.rs#L204-L218
-- These cases were also executed with Rust's ADDI::execute.
def addiRow (imm : BitVec 64) : JoltProgramRow :=
  { instruction := .ADDI (.vreg 40) (.vreg 41) imm
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 0x80000000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) (imm : BitVec 64) : JoltProgram :=
  { expandedBytecode := #[addiRow imm], initialState := state }

noncomputable def addiVisit (state : SailJoltState) (imm : BitVec 64) :
    JoltTraceRow (program state imm) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := { state with vregs := fun r =>
      if r = 40 then BitVec.ofNat 64 (JoltISA.addWide (state.vregs 41) imm) else state.vregs r }
    executes := rfl
    storeMemoryPresent := True.intro }

example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (addiVisit { state with vregs := fun _ => 10 } 4096) = 4106 ∧
    JoltMetadata.immediate (addiRow 4096).instruction = 4096 ∧
    HonestWitness.instructionLookupIndex (addiRow 4096).instruction 0x80000000
      { state with vregs := fun _ => 10 } state = 4106 := by
  exact ⟨rfl, rfl, rfl⟩

example (state : SailJoltState) :
    (addiVisit { state with vregs := fun _ => 10 } (-1)).postState.vregs 40 = 9 ∧
    (addiVisit { state with vregs := fun _ => -1 } 4096).postState.vregs 40 = 4095 ∧
    (addiVisit { state with vregs := fun _ => 0 } (2^63)).postState.vregs 40 = 2^63 := by
  norm_num [addiVisit, JoltISA.addWide]
  decide +kernel

-- Source ADDI still sign-extends its encoded immediate exactly once.
example : JoltISA.Encoded.ADDI (.vreg 40) (.vreg 41) (-1 : BitVec 12) =
    .ADDI (.vreg 40) (.vreg 41) (-1 : BitVec 64) := rfl

-- A final AUIPC carries the already shifted offset; 4096 must not become 4096 << 12.
example : JoltMetadata.immediate (.AUIPC (.vreg 40) 4096) = 4096 ∧
    JoltISA.Encoded.AUIPC (.vreg 40) (1 : BitVec 20) = .AUIPC (.vreg 40) 4096 := ⟨rfl, rfl⟩

example (state : SailJoltState) :
    HonestWitness.instructionLookupIndex (.AUIPC (.vreg 40) 4096) 0x80000000 state state =
      0x80001000 := rfl

-- Loads/stores preserve signed 64-bit offsets, rather than truncating them to 12 bits.
example (state : SailJoltState) :
    HonestWitness.ramAccessAddress (.LD .normal (.vreg 40) (.vreg 41) (-4096))
      { state with vregs := fun _ => 0x80002000 } = some 0x80001000 ∧
    JoltMetadata.immediate (.SD (.vreg 41) (.vreg 40) (-4096)) = -4096 := by
  norm_num [HonestWitness.ramAccessAddress, JoltISA.sourceValue, JoltMetadata.immediate]
  decide +kernel

-- Alignment assertions read the same virtual register that their selectors name.
example (state : SailJoltState) :
    JoltISA.execInstr
      (.VirtualAssertWordAlignment (.vreg 41) 4096 (.E_Load_Addr_Align ()))
      { state with vregs := fun _ => 8 } =
        .ok (.Retire_Success ()) { state with vregs := fun _ => 8 } := by
  simp [JoltISA.execInstr, JoltISA.readSrc, readVReg, JoltISA.addWide,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, LeanRV64D.Functions.RETIRE_SUCCESS]

example :
    JoltRegisterEncoding.instructionIsCanonical
      (.VirtualAssertWordAlignment (.vreg 41) 4096 (.E_Load_Addr_Align ())) = true ∧
    JoltRegisterEncoding.instructionIsCanonical
      (.VirtualAssertWordAlignment (.vreg 1) 4096 (.E_Load_Addr_Align ())) = false := by
  exact ⟨rfl, rfl⟩

-- FormatB uses signed i128. Compact proof rows accept both signs of u64::MAX,
-- and reject magnitude 2^64. No truncation may hide the sign in the Imm witness.
example :
    JoltMetadata.immediate (.BEQ (.vreg 40) (.vreg 41) (2^63 : BitVec 128)) = 2^63 ∧
    JoltMetadata.immediate (.BEQ (.vreg 40) (.vreg 41) (-(2^63)-1 : BitVec 128)) = -(2^63)-1 := by
  decide

example :
    (JoltISA.Instr.BEQ (.vreg 40) (.vreg 41) (2^64-1)).CompactImmediateFits ∧
    (JoltISA.Instr.BEQ (.vreg 40) (.vreg 41) (-(2^64-1))).CompactImmediateFits ∧
    ¬ (JoltISA.Instr.BEQ (.vreg 40) (.vreg 41) (2^64)).CompactImmediateFits ∧
    ¬ (JoltISA.Instr.VirtualAssertLTE (.vreg 40) (.vreg 41) (-(2^64))).CompactImmediateFits := by
  simp only [JoltISA.Instr.CompactImmediateFits]
  decide

example :
    (JoltISA.Instr.VirtualSRLI (.vreg 40) (.vreg 41) (2^64-1)).OperandsRepresentable ∧
    ¬ (JoltISA.Instr.VirtualSRLI (.vreg 40) (.vreg 41) (2^64)).OperandsRepresentable := by
  simp only [JoltISA.Instr.OperandsRepresentable]
  decide

end FinalOperandChecks
