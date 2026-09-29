import JoltConstraints.Constraints.LookupEntryProofHelpers

set_option autoImplicit false

/-!
Counterexamples and checks for the per-table lemmas in
`JoltConstraints/Constraints/LookupEntryProofHelpers.lean` left as `sorry`.
Not part of the default build; check with `lake env lean JoltConstraints/Tests/LookupShiftMask.lean`.

Shift/rotate tables (`VirtualSRL`, `VirtualSRA`, `VirtualSRLW`, `VirtualSRAW`,
`VirtualROTR`, `VirtualROTRW`) read the right operand as a right-shift bitmask,
while the honest outputs shift by `ctz` of whatever mask the row carries.
Source `4`, mask `2`: index `interleave 4 2 = 36`; entries 0/0/0/0/4/4 versus
output `2` for all six. `VirtualSRLW` with mask `0` (register form): index 34,
entry 0, output `5`.
-/

open JoltConstraints

#eval (HonestWitness.interleaveLookupOperands 4 2).toNat
#eval (HonestWitness.interleaveLookupOperands 5 0).toNat
#eval (jolt_virtual_srl_value 4 2, jolt_virtual_srli_value 4 2, jolt_virtual_sra_value 4 2,
  jolt_virtual_srlw_value 4 2, jolt_virtual_sraw_value 4 2, jolt_virtual_rotri_value 4 2,
  jolt_virtual_rotriw_value 4 2, jolt_virtual_srlw_value 5 0, jolt_virtual_srliw_value 5 0)

set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualSRL ⟨36, by decide⟩ : ℚ) = 0 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualSRA ⟨36, by decide⟩ : ℚ) = 0 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualSRLW ⟨36, by decide⟩ : ℚ) = 0 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualSRAW ⟨36, by decide⟩ : ℚ) = 0 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualROTR ⟨36, by decide⟩ : ℚ) = 4 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualROTRW ⟨36, by decide⟩ : ℚ) = 4 := by decide +kernel
set_option maxRecDepth 8192 in
example : (lookupTableEntry .VirtualSRLW ⟨34, by decide⟩ : ℚ) = 0 := by decide +kernel

/-! Row-level refutation of `lookupEntryCorrect_VirtualSRL`: a one-row program
`VirtualSRLI v32, v33, 2` (mask immediate `2`, not a right-shift bitmask) run
from any state with `v33 = 4`. `OperandsRepresentable` only asks `2 < 2^64`. -/
namespace SRLICounterexample

def instruction : JoltISA.Instr := .VirtualSRLI (.vreg 32) (.vreg 33) 2

def bytecodeRow : JoltProgramRow :=
  { inputInstruction := instruction
    registerOperandsCanonical := by decide
    isBytecodeTemplate := True.intro
    operandsRepresentable := by
      simp [finalProgramRowInstruction, instruction, JoltISA.Instr.OperandsRepresentable]
    address := 0x80000000
    virtualSequenceRemaining := some 0
    isFirstInSequence := true
    isCompressed := false }

def program (state : SailJoltState) : JoltProgram :=
  { expandedBytecode := #[bytecodeRow]
    initialState := state }

noncomputable def visit (state : SailJoltState) : JoltTraceRow (program state) :=
  { rowIndex := ⟨0, by simp [program]⟩
    runtimeAdvice := ()
    preState := state
    postState := { state with
      vregs := fun r => if r = 32 then (jolt_virtual_srli_value (state.vregs 33) 2) else state.vregs r }
    executes := rfl
    storeMemoryPresent := True.intro }

example (state : SailJoltState) :
    JoltMetadata.lookupTable (rowInstruction (visit state)) = some .VirtualSRL := rfl

example (state : SailJoltState) (h : state.vregs 33 = 4) :
    HonestWitness.rowLookupOutput (visit state) = 2 := by
  change jolt_virtual_srli_value (state.vregs 33) 2 = 2
  rw [h]; decide +kernel

example (state : SailJoltState) (h : state.vregs 33 = 4) :
    rowLookupAddress (visit state) = ⟨36, by decide⟩ := by
  change (HonestWitness.interleaveLookupOperands (state.vregs 33) (BitVec.ofNat 64 2)).toFin = _
  rw [h]; decide +kernel

set_option maxRecDepth 8192 in
theorem not_lookupEntryCorrect (state : SailJoltState) (h : state.vregs 33 = 4) :
    ¬ LookupEntryCorrect ℚ .VirtualSRL (visit state) := by
  unfold LookupEntryCorrect
  have ha : rowLookupAddress (visit state) = ⟨36, by decide⟩ := by
    change (HonestWitness.interleaveLookupOperands (state.vregs 33) (BitVec.ofNat 64 2)).toFin = _
    rw [h]; decide +kernel
  have ho : HonestWitness.rowLookupOutput (visit state) = 2 := by
    change jolt_virtual_srli_value (state.vregs 33) 2 = 2
    rw [h]; decide +kernel
  have he : (lookupTableEntry .VirtualSRL ⟨36, by decide⟩ : ℚ) = 0 := by decide +kernel
  rw [ha, ho, he]
  simp

end SRLICounterexample
