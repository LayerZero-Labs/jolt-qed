import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualMULI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt VirtualMULI + VSEW = Sail SLLIW

Jolt program sequence:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two (= left shift)
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The bridge `extractLsb_mul_pow2` is specific to SLLIW (scalar shamt)
rather than the R-type variant; kept inline here since no other
instruction reuses it.
-/

private theorem extractLsb_mul_pow2 (v : BitVec 64) (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0 =
    shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt := by
  unfold shift_bits_left Sail.BitVec.extractLsb
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem slliw_mul_eq_shift (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [extractLsb_mul_pow2]

abbrev slliw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev slliw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_muli_value v (BitVec.ofNat 64 (2 ^ shamt.toNat))) 31 0)

private theorem slliw_value_eq_sail (shamt : BitVec 5) (v : BitVec 64) :
    slliw_jolt_val shamt v = slliw_sail_operation shamt v := by
  simp only [slliw_jolt_val, slliw_sail_operation, jolt_virtual_muli_value]
  exact slliw_mul_eq_shift v shamt

/-- Main program-level equivalence for `SLLIW`. -/
def slliwProgramEqSailStatement (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.slliwProgramAuto rd rs1 shamt)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run js.sail

/-- Main program-level equivalence for `SLLIW`. -/
theorem slliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    slliwProgramEqSailStatement shamt rs1 rd js h := by
  unfold slliwProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.slliwProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    change System.systemProjectResult
      ((JoltISA.execProgram JoltISA.pureWritebackRdZeroProgram).run js) = _
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    simp only [execute_SHIFTIWOP]
    simp only [EStateM.run_bind]
    simp only [EStateM.run]
    simp only [h_read_rs1, pure, EStateM.pure, wX_bits_regidx_zero]

  have hrd_not_x0 : JoltISA.isX0 rd = false :=
    JoltISA.isX0_eq_false_of_ne_zero hrd
  have h_value :
      jolt_virtual_muliw_value v (BitVec.ofNat 64 (2 ^ shamt.toNat)) =
        slliw_sail_operation shamt v := by
    rw [← slliw_value_eq_sail shamt v]
    simp only [slliw_jolt_val, jolt_virtual_muliw_value, jolt_virtual_muli_value]
    unfold sign_extend
    simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.extractLsb']
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_mul]
  obtain ⟨s', h_write⟩ := wX_shape rd (slliw_sail_operation shamt v) js.sail

  simp only [execute_SHIFTIWOP]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, pure, EStateM.pure, h_write]

  unfold JoltISA.slliwProgramAuto
  rw [hrd_not_x0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [JoltISA.execProgram_instr]
  simp only [JoltISA.execInstr]
  simp only [JoltISA.readSrc, JoltISA.writeDst]
  unfold liftSail
  simp only [bind, EStateM.bind]
  simp only [h_read_rs1, h_value, h_write]
  simpa only [JoltISA.execProgram_done, pure, EStateM.pure, EStateM.run] using
    Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
      (slliw_sail_operation shamt v) h.linkedCSRs h_write

end
