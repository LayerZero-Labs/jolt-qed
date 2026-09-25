import JoltBytecode.InstructionEquivalence.Instructions.Natives.Jalr
import JoltConstraints.metadata
import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.rd_value
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace NativeDispatchChecks

-- Source ADDI x0,x1,7 becomes ADDI x0,x0,0 before witness extraction.
-- Its recorded immediate must describe that replacement.
example :
    JoltMetadata.immediate
      (JoltISA.pureWritebackNativeInstr (.Regidx 0)
        (JoltISA.Encoded.ADDI (.xreg (.Regidx 0)) (.xreg (.Regidx 1)) 7)) = 0 := rfl

-- Source JALR x0,x0,6 writes v40 and sets cpu.pc to 6.
-- Six is not four-byte aligned; Rust's body still executes successfully.
def jumpRow : JoltProgramRow :=
  { instruction := JoltISA.jalrNativeInstr (.Regidx 0) (.Regidx 0) 6
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 0x1000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[jumpRow], initialState := state }

noncomputable def visit (state : SailJoltState)
    (hPC : state.sail.regs.get? Register.nextPC = some 0x1004) :
    JoltTraceRow (program state) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := NativeDispatch.afterDst
      { state with sail := System.setNextPCState state.sail 6 } (.Regidx 0) 0x1004
    executes := by
      exact Natives.jalrNative_run 6 (.Regidx 0) (.Regidx 0) state 0x1004 0 hPC
        (rX_bits_regidx_zero state.sail)
    storeMemoryPresent := True.intro }

-- Witness extraction sees the temporary destination and the computed target.
-- It must not lose the temporary write by projecting to Sail first.
example (state : SailJoltState)
    (hPC : state.sail.regs.get? Register.nextPC = some 0x1004) :
    (HonestWitness.rdValue jumpRow.instruction (visit state hPC).postState : ℚ) = 0x1004 ∧
    HonestWitness.rowLookupOutput (visit state hPC) = 6 := by
  constructor
  · rfl
  · change jolt_jalr_target64 0 6 = 6
    decide

example (state : SailJoltState)
    (hPC : state.sail.regs.get? Register.nextPC = some 0x1004) :
    (visit state hPC).postState.sail.regs.get? Register.nextPC = some 6 ∧
    (visit state hPC).postState.sail.regs.get? Register.PC =
      state.sail.regs.get? Register.PC := by
  simp [visit, NativeDispatch.afterDst, JoltISA.isX0, System.setNextPCState]
  exact System.extDHashMap_get?_insert_of_ne _ _ (h := by decide)

end NativeDispatchChecks
