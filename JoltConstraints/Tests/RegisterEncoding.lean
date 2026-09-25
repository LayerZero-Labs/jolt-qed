import JoltConstraints.trace
import JoltConstraints.witness_helpers.register_address
import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.lookup_index

set_option autoImplicit false

namespace RegisterEncodingChecks

open JoltRegisterEncoding

-- All 128 Rust register addresses remain representable. The existing ISA map
-- determines their storage, and the witness recovers the same numeric address.
set_option maxRecDepth 4096 in
example : ∀ address : Fin 128,
    sourceIsCanonical (source (BitVec.ofNat 7 address.val)) = true ∧
    destinationIsCanonical (destination (BitVec.ofNat 7 address.val)) = true ∧
    HonestWitness.sourceRegisterAddress (source (BitVec.ofNat 7 address.val)) = address ∧
    HonestWitness.destinationRegisterAddress (destination (BitVec.ofNat 7 address.val)) = address := by
  decide +kernel

-- Precisely the architectural addresses reject the raw virtual-storage tag.
example : ∀ address : Fin 128,
    sourceIsCanonical (.vreg (BitVec.ofNat 7 address.val)) = decide (32 ≤ address.val) ∧
    destinationIsCanonical (.vreg (BitVec.ofNat 7 address.val)) = decide (32 ≤ address.val) := by
  decide +kernel

-- The new certificate rules out a previously admissible bytecode instruction.
example (row : JoltProgramRow) :
    row.instruction ≠ JoltISA.Encoded.ADDI (.vreg 40) (.vreg 5) 0 := by
  intro wrongEncoding
  have canonical := row.registerOperandsCanonical
  rw [wrongEncoding] at canonical
  exact Bool.noConfusion canonical

-- Check the other source position, destinations, and captured-but-unused sources.
example : instructionIsCanonical (.ADD (.vreg 40) (.xreg (.Regidx 5)) (.vreg 31)) = false := rfl
example : instructionIsCanonical (JoltISA.Encoded.ADDI (.vreg 5) (.xreg (.Regidx 5)) 0) = false := rfl
example : instructionIsCanonical (.VirtualAdviceLen (.vreg 40) (.vreg 5)) = false := rfl
example : instructionIsCanonical (.VirtualHostIO (.vreg 40) (.vreg 5)) = false := rfl
example : instructionIsCanonical (JoltISA.Encoded.SD (.vreg 5) (.vreg 40) 0) = false := rfl

-- Runtime advice changes only the payload, so it preserves operand validity.
example (instruction : JoltISA.Instr) (advice : instruction.RuntimeAdvice) :
    instructionIsCanonical (instruction.withRuntimeAdvice advice) =
      instructionIsCanonical instruction := by
  cases instruction <;> rfl

-- Rust ADDI v40, x0, 7. Raw virtual slot zero deliberately contains 99;
-- the mapped operand still reads x0=0, and both execution and lookup produce 7.
def bytecodeRow : JoltProgramRow :=
  { instruction := JoltISA.Encoded.ADDI (destination 40) (source 0) 7
    registerOperandsCanonical := rfl
    isBytecodeTemplate := True.intro
    address := 0x80000000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def preState (state : SailJoltState) : SailJoltState :=
  { state with vregs := fun r => if r = 0 then 99 else state.vregs r }

def program (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[bytecodeRow]
    initialState := preState state }

noncomputable def visit (state : SailJoltState) : JoltTraceRow (program state) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := preState state
    postState := { preState state with vregs := fun r =>
      if r = 40 then 7 else (preState state).vregs r }
    executes := rfl
    storeMemoryPresent := True.intro }

example (state : SailJoltState) :
    (visit state).postState.vregs 40 = 7 ∧
    HonestWitness.rowLookupOutput (visit state) = 7 ∧
    HonestWitness.instructionLookupIndex bytecodeRow.instruction bytecodeRow.address
      (visit state).preState (visit state).postState = 7 := ⟨rfl, rfl, rfl⟩

-- A genuinely virtual source retains its ordinary ISA meaning.
example (state : SailJoltState) :
    JoltISA.readSrc (source 32) state = .ok (state.vregs 32) state := rfl

end RegisterEncodingChecks
