import JoltConstraints.witness_helpers.lookup_output
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.witness_helpers.rd_value
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.lookup_table
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace VirtualXORROTL1Checks

-- Values captured from Rust's tracer, lookup query, and table at
-- e012da54c3bb26a6436b5ca74e86c19bb39695ad (RV64).
-- Includes asymmetric operands, top-bit wraparound, and all-one words.
def rustVectors : List (Nat × Nat × Nat × Nat) :=
  [(0, 0, 0, 0),
   (1, 2, 6, 5),
   (0, 9223372036854775808, 85070591730234615865843651857942052864, 1),
   (9223372036854775808, 0, 170141183460469231731687303715884105728, 9223372036854775808),
   (9223372036854775808, 9223372036854775808, 255211775190703847597530955573826158592, 9223372036854775809),
   (18446744073709551615, 18446744073709551615, 340282366920938463463374607431768211455, 0),
   (18446744073709551615, 0, 226854911280625642308916404954512140970, 18446744073709551615),
   (81985529216486895, 18364758544493064720, 113432729467922989895506426423086066090, 18201913995886307790)]

set_option maxRecDepth 4096 in
example : rustVectors.Forall (fun (x, y, index, output) =>
    jolt_virtual_xorrotl1_value (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 output ∧
    HonestWitness.interleaveLookupOperands (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 128 index) := by
  decide +kernel

-- Rust's lookup formula uses XOR for the two disjoint shifted parts.
example (x y : BitVec 64) :
    jolt_virtual_xorrotl1_value x y = x ^^^ (y <<< 1) ^^^ (y >>> 63) := by
  change x ^^^ ((y <<< 1) ||| (y >>> (63 : Nat))) = _
  bv_decide

def instruction (dst : JoltISA.Dst) : JoltISA.Instr :=
  .VirtualXORROTL1 dst (.vreg 32) (.vreg 33)

def bytecodeRow (dst : JoltISA.Dst)
    (canonical : JoltRegisterEncoding.destinationIsCanonical dst = true) : JoltProgramRow :=
  { instruction := instruction dst
    registerOperandsCanonical := by
      simpa [instruction, JoltRegisterEncoding.instructionIsCanonical,
        JoltRegisterEncoding.sourceIsCanonical, JoltISA.joltRegisterSlot] using canonical
    isBytecodeTemplate := True.intro
    address := 0x80000000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) (dst : JoltISA.Dst)
    (canonical : JoltRegisterEncoding.destinationIsCanonical dst = true) : JoltProgram :=
  { expandedBytecode := #[bytecodeRow dst canonical]
    initialState := state }

-- rd aliases rs1: both operands must be read before writing the result.
noncomputable def visit (state : SailJoltState) : JoltTraceRow (program state (.vreg 32) rfl) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := { state with vregs := fun r => if r = 32 then
      jolt_virtual_xorrotl1_value (state.vregs 32) (state.vregs 33) else state.vregs r }
    executes := rfl
    storeMemoryPresent := True.intro }

example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (visit state) =
      jolt_virtual_xorrotl1_value (state.vregs 32) (state.vregs 33) := rfl

example (state : SailJoltState) :
    HonestWitness.instructionLookupIndex (instruction (.vreg 32)) 0x80000000
      state (visit state).postState =
      HonestWitness.interleaveLookupOperands (state.vregs 32) (state.vregs 33) := rfl

-- A discarded architectural write still has a nonzero lookup output.
noncomputable def discardedVisit (state : SailJoltState) :
    JoltTraceRow (program state (.xreg (.Regidx 0)) rfl) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := state
    executes := rfl
    storeMemoryPresent := True.intro }

example (state : SailJoltState) :
    HonestWitness.rowLookupOutput (discardedVisit state) =
      jolt_virtual_xorrotl1_value (state.vregs 32) (state.vregs 33) := rfl

example (state : SailJoltState) :
    (HonestWitness.rdValue (instruction (.xreg (.Regidx 0))) state : ℚ) = 0 := rfl

-- Check every opcode/instruction flag, including the false cases.
example (dst : JoltISA.Dst) (flag : InstructionFlags) :
    JoltMetadata.instructionFlag (instruction dst) flag =
      (flag == .LeftOperandIsRs1Value || flag == .RightOperandIsRs2Value) := by
  cases flag <;> rfl

example (dst : JoltISA.Dst) (flag : CircuitFlags) :
    JoltMetadata.opcodeFlag (instruction dst) flag = (flag == .WriteLookupOutputToRD) := by
  cases flag <;> rfl

example (dst : JoltISA.Dst) :
    JoltMetadata.lookupTable (instruction dst) = some .VirtualXORROTL1 ∧
    JoltMetadata.immediate (instruction dst) = 0 ∧
    JoltMetadata.instructionRafFlag (instruction dst) = false := ⟨rfl, rfl, rfl⟩

example (dst : JoltISA.Dst) :
    JoltConstraints.bytecodeRs1Register (instruction dst) = some 32 ∧
    JoltConstraints.bytecodeRs2Register (instruction dst) = some 33 ∧
    JoltConstraints.bytecodeRdRegister (instruction dst) =
      some (HonestWitness.destinationRegisterAddress dst) := ⟨rfl, rfl, rfl⟩

-- Fixed-table values independently cover operand ordering and bit-63 wrap.
set_option maxRecDepth 4096 in
example : (JoltConstraints.lookupTableEntry .VirtualXORROTL1 ⟨6, by decide⟩ : ℚ) = 5 := by
  decide +kernel

set_option maxRecDepth 4096 in
example : (JoltConstraints.lookupTableEntry .VirtualXORROTL1
    ⟨85070591730234615865843651857942052864, by decide⟩ : ℚ) = 1 := by
  decide +kernel

end VirtualXORROTL1Checks
