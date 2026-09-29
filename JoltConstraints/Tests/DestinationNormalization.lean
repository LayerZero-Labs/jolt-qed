import JoltConstraints.metadata
import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.rd_value
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltBytecode.JoltISA.Expansions.System
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace DestinationNormalizationChecks

private def zeroDst : JoltISA.Dst := .xreg (.Regidx 0)

example : (JoltISA.Instr.JAL zeroDst 0).rewriteNative =
    .JAL (.vreg JoltISA.rdZeroRewriteVReg) 0 := rfl

example : (JoltISA.Instr.JALR zeroDst (.xreg (.Regidx 1)) 0).rewriteNative =
    .JALR (.vreg JoltISA.rdZeroRewriteVReg) (.xreg (.Regidx 1)) 0 := rfl

example : (JoltISA.Instr.LD .normal zeroDst (.xreg (.Regidx 1)) 0).rewriteNative =
    .LD .normal (.vreg JoltISA.rdZeroRewriteVReg) (.xreg (.Regidx 1)) 0 := rfl

example : (JoltISA.Instr.VirtualAdviceLoad zeroDst 0).rewriteNative =
    .VirtualAdviceLoad (.vreg JoltISA.rdZeroRewriteVReg) 0 := rfl

example (state : SailJoltState) :
    (HonestWitness.rdValue ((JoltISA.Instr.JAL zeroDst 0).rewriteNative) state : ℚ) =
      (state.vregs JoltISA.rdZeroRewriteVReg).toNat := rfl

example : HonestWitness.capturedDestination (.ADDI zeroDst (.xreg (.Regidx 0)) 0) zeroDst =
    zeroDst := rfl

example : JoltConstraints.bytecodeRdRegister ((JoltISA.Instr.JAL zeroDst 0).rewriteNative) =
    some (HonestWitness.destinationRegisterAddress (.vreg JoltISA.rdZeroRewriteVReg)) := rfl

example : JoltConstraints.bytecodeRdRegister (.ADDI zeroDst (.xreg (.Regidx 0)) 0) =
    some (HonestWitness.destinationRegisterAddress zeroDst) := rfl

example : JoltISA.csrrsProgram .mstatus (.Regidx 0) (.Regidx 0) =
    JoltISA.pureWritebackRdZeroProgram := rfl

-- This synthetic row remains representable by the unrestricted program model.
def csrReadDiscarded : JoltProgramRow :=
  { inputInstruction := JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.vreg 39) 0
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 0x80000000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[csrReadDiscarded]
    initialState := state }

noncomputable def visit (state : SailJoltState) : JoltTraceRow (program state) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := state
    executes := rfl
    storeMemoryPresent := True.intro }

-- Lookup 9 and captured rd 0 falsify the WriteLookupOutputToRD equation for
-- this synthetic row.
example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (visit { state with vregs := fun _ => 9 }) = 9 ∧
    (HonestWitness.rdValue csrReadDiscarded.expandedInstruction state : ℚ) = 0 ∧
    JoltMetadata.opcodeFlag csrReadDiscarded.expandedInstruction .WriteLookupOutputToRD = true :=
  ⟨rfl, rfl, rfl⟩

-- The ordinary source-rewrite no-op has zero result on both sides, even with arbitrary state.
example (state : SailJoltState) :
    (HonestWitness.rdValue (JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.xreg (.Regidx 0)) 0) state : ℚ) = 0 := rfl

end DestinationNormalizationChecks
