import JoltConstraints.metadata
import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.rd_value
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace DestinationNormalizationChecks

-- This is emitted by the built-in Rust CSRRS x0,mstatus,x0 expansion.
-- It remains representable: the model must preserve the emitted instruction.
def csrReadDiscarded : JoltProgramRow :=
  { instruction := JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.vreg 39) 0
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

-- Same concrete values as the Rust tracer check: lookup 9, captured rd 0.
-- This falsifies the WriteLookupOutputToRD equation for this actual expanded row.
example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (visit { state with vregs := fun _ => 9 }) = 9 ∧
    (HonestWitness.rdValue csrReadDiscarded.instruction state : ℚ) = 0 ∧
    JoltMetadata.opcodeFlag csrReadDiscarded.instruction .WriteLookupOutputToRD = true :=
  ⟨rfl, rfl, rfl⟩

-- The ordinary source-rewrite no-op has zero result on both sides, even with arbitrary state.
example (state : SailJoltState) :
    (HonestWitness.rdValue (JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.xreg (.Regidx 0)) 0) state : ℚ) = 0 := rfl

end DestinationNormalizationChecks
