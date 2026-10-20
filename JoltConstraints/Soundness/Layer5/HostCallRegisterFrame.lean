import JoltConstraints.Soundness.Layer5.HostCallRestriction
import JoltConstraints.Soundness.Layer5.Registers

/-! A successful HostIO row preserves Sail state and virtual registers. Its
selected destination table entry can still change, so this file proves
agreement for the other entries. The global induction must account for that
destination until a later write restores agreement. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

private theorem sourceValue_of_host_frame (source : Src)
    (pre post : SailJoltState) (sail : post.sail = pre.sail)
    (vregs : post.vregs = pre.vregs) :
    sourceValue source post = sourceValue source pre := by
  cases source <;> simp only [sourceValue, sail, vregs]

/-- The HostIO x0 rewrite uses register 40, the first register checked by
`tempsReadAfterWrite`. -/
theorem host_call_rewrite_register_is_40 :
    rdZeroRewriteVReg = BitVec.ofNat 7 40 := by rfl

/-- A source HostIO with `rd = x0` expands to a row whose destination is
`rdZeroRewriteVReg`. The caller obtains `zero` from the approved restriction. -/
theorem host_call_zero_destination_is_temp (rd rs1 : regidx) (imm : BitVec 12)
    (zero : isX0 rd = true) :
    (SourceInstruction.jolt (.VirtualHostIO rd rs1 imm)).expand =
      some (.native (.VirtualHostIO (.vreg rdZeroRewriteVReg) (.xreg rs1)
        (sign_extend (m := 64) imm))) := by
  simp [SourceInstruction.expand, ExpandedSource.ofNative, Instr.rewriteNative,
    sideEffectingDst, sideEffectingRdZeroDst, zero]

/-- HostIO cannot disturb agreement away from its selected table destination.
The destination entry itself needs the later temporary-liveness argument. -/
theorem RegisterAgreement.host_call_other
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    {destination : Dst} {source : Src} {imm : BitVec 64}
    (instruction : row.instruction = .VirtualHostIO destination source imm)
    {pre post : SailJoltState}
    (agrees : RegisterAgreement witness t pre)
    (sail : post.sail = pre.sail) (vregs : post.vregs = pre.vregs) :
    AllRegistersPresent post.sail ∧
    ∀ register : Fin 128,
      register ≠ TraceWitness.destinationRegisterAddress destination →
      witness.RegistersVal register ⟨t.val + 1, next⟩ =
        ((sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) post).toNat : F) := by
  refine ⟨sail ▸ agrees.present, ?_⟩
  intro register different
  rw [registersVal_succ_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations register t next chosen selected]
  simp only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    instruction, Instr.destination?, Option.map_some]
  rw [if_neg different, agrees.values]
  rw [sourceValue_of_host_frame _ pre post sail vregs]

end JoltConstraints.Soundness
