import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.metadata

set_option autoImplicit false

namespace RuntimeAdviceChecks

-- One fixed bytecode slot, like a quotient-advice slot in a DIVU expansion.
-- The nonzero immediate deliberately distinguishes it from the runtime payload.
def adviceTemplate : JoltProgramRow :=
  { instruction := .VirtualAdvice (.vreg 40) 0 7
    registerOperandsCanonical := rfl
    isBytecodeTemplate := rfl
    address := 0x80000000
    virtualSequenceRemaining := some 7
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[adviceTemplate]
    initialState := state }

-- Construct actual successful execution certificates using the existing ISA.
-- This models individual visits to a bytecode slot, not a complete DIVU trace.
def visit (state : SailJoltState) (advice : BitVec 64) : JoltTraceRow (program state) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := advice
    preState := state
    postState := { state with vregs := fun r => if r = 40 then advice else state.vregs r }
    executes := rfl
    storeMemoryPresent := True.intro }

-- The old executes certificate could not admit both of these visits.
example (state : SailJoltState) :
    (visit state 3).rowIndex = (visit state 5).rowIndex ∧
    (visit state 3).postState.vregs 40 = 3 ∧
    (visit state 5).postState.vregs 40 = 5 := by
  exact ⟨rfl, rfl, rfl⟩

-- The witness observes each execution's result rather than the template zero.
example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (visit state 3) = 3 ∧
    HonestWitness.rowLookupOutput (visit state 5) = 5 := by
  exact ⟨rfl, rfl⟩

example (state : SailJoltState) (advice : BitVec 64) :
    HonestWitness.instructionLookupIndex adviceTemplate.instruction adviceTemplate.address
      state (visit state advice).postState = advice.setWidth 128 := by
  rfl

-- Supplying advice cannot replace the bytecode immediate, destination, or flags.
example (advice : BitVec 64) :
    adviceTemplate.instruction.withRuntimeAdvice advice =
      .VirtualAdvice (.vreg 40) advice 7 ∧
    JoltMetadata.immediate (adviceTemplate.instruction.withRuntimeAdvice advice) = 7 ∧
    JoltMetadata.opcodeFlag (adviceTemplate.instruction.withRuntimeAdvice advice) .Advice = true := by
  exact ⟨rfl, rfl, rfl⟩

-- Non-advice rows have only Unit as their runtime input and execute unchanged.
example (instruction : JoltISA.Instr)
    (notAdvice : ∀ dst value imm, instruction ≠ .VirtualAdvice dst value imm)
    (input : instruction.RuntimeAdvice) : instruction.withRuntimeAdvice input = instruction := by
  cases instruction <;> try rfl
  exact False.elim (notAdvice _ _ _ rfl)

-- Execution-specific values cannot leak back into the fixed bytecode template.
example : ¬ (JoltISA.Instr.VirtualAdvice (.vreg 40) 3 7).IsBytecodeTemplate := by
  exact (by decide : (3 : BitVec 64) ≠ 0)

end RuntimeAdviceChecks
