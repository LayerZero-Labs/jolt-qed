import JoltConstraints.Soundness.Layer2.State
import JoltConstraints.Soundness.Layer2.ZeroRegister

/-! Register agreement for the execution-prefix induction. Alongside the table
values, retain register presence: `sourceValue` alone defaults missing registers
to zero and would not justify a successful execution read. Initialization and
writes establish and preserve both facts without an honest-trace hypothesis.
The write lemma takes the instruction family's local execution and write-value
facts; these are proof obligations, not new soundness premises. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}

/-- The register table represents the state, and every Sail register is present
so instruction reads can use those values. This is the register part of `Agrees`. -/
structure RegisterAgreement (witness : WitnessType F params)
    (t : Fin params.traceLength) (state : SailJoltState) : Prop where
  present : AllRegistersPresent state.sail
  values : ∀ register : Fin 128,
    witness.RegistersVal register t =
      ((sourceValue (JoltRegisterEncoding.source (BitVec.ofFin register)) state).toNat : F)

/-- The zero table and the instance's initialized state establish register
agreement, including successful-read availability. -/
theorem RegisterAgreement.initial
    (history : registersValEqPrefixRdInc witness)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {state : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some state) :
    RegisterAgreement witness ⟨0, Nat.two_pow_pos _⟩ state :=
  ⟨initial_state_registers_present _ _ _ built, registersVal_initial_state history built⟩

/-- Preparing the next source instruction's PC preserves register agreement. -/
theorem RegisterAgreement.advance_pc {t : Fin params.traceLength} {state : SailJoltState}
    (agrees : RegisterAgreement witness t state) (address : BitVec 64) (compressed : Bool) :
    RegisterAgreement witness t (advance_pc address compressed state) := by
  refine ⟨advance_pc_keeps_registers _ _ _ agrees.present, ?_⟩
  intro register
  rw [sourceValue_advance_pc]
  exact agrees.values register

private theorem readSrc_of_present (source : Src) (state : SailJoltState)
    (present : AllRegistersPresent state.sail) :
    readSrc source state = .ok (sourceValue source state) state := by
  cases source with
  | vreg register => rfl
  | xreg register =>
    obtain ⟨value, read⟩ := (readable_of_present state.sail present register).exists_value
    have lifted := readSrc_xreg_run_of_read register state value read
    rw [(lookup_readSrc_value _ _ _ _ lifted).2] at lifted
    exact lifted

/-- A canonical operand reads successfully, and the value read is represented
by its register-table entry. -/
theorem RegisterAgreement.read {t : Fin params.traceLength} {state : SailJoltState}
    (agrees : RegisterAgreement witness t state) (source : Src)
    (canonical : JoltRegisterEncoding.sourceIsCanonical source = true) :
    readSrc source state = .ok (sourceValue source state) state ∧
      witness.RegistersVal (TraceWitness.sourceRegisterAddress source) t =
        ((sourceValue source state).toNat : F) := by
  refine ⟨readSrc_of_present source state agrees.present, ?_⟩
  simpa only [source_decode_encode source canonical] using
    agrees.values (TraceWitness.sourceRegisterAddress source)

private def destinationSource : Dst → Src
  | .xreg register => .xreg register
  | .vreg register => .vreg register

private theorem source_of_destination (destination : Dst)
    (canonical : JoltRegisterEncoding.destinationIsCanonical destination = true) :
    JoltRegisterEncoding.source
      (BitVec.ofFin (TraceWitness.destinationRegisterAddress destination)) =
        destinationSource destination := by
  cases destination with
  | xreg register => exact source_decode_encode (.xreg register) canonical
  | vreg register => exact source_decode_encode (.vreg register) canonical

private theorem sourceValue_writeDst_other (destination : Dst) (source : Src)
    (value : BitVec 64) (pre post : SailJoltState)
    (different : TraceWitness.sourceRegisterAddress source ≠
      TraceWitness.destinationRegisterAddress destination)
    (present : AllRegistersPresent pre.sail)
    (written : writeDst destination value pre = .ok () post) :
    sourceValue source post = sourceValue source pre := by
  cases destination with
  | xreg rd =>
    simp only [writeDst_xreg, liftSail, wX_bits_stateAfterWrite] at written
    cases written
    cases source with
    | vreg register => rfl
    | xreg rs =>
      have distinct : rd ≠ rs := by
        intro same
        subst rd
        exact different rfl
      obtain ⟨old, read⟩ := (readable_of_present pre.sail present rs).exists_value
      have before := readSrc_xreg_run_of_read rs pre old read
      have after := readSrc_xreg_run_of_read rs
        { pre with sail := stateAfterWrite pre.sail rd value } old
        (rX_bits_stateAfterWrite_of_ne rd rs value old pre.sail distinct read)
      exact (lookup_readSrc_value _ _ _ _ after).2.symm.trans
        (lookup_readSrc_value _ _ _ _ before).2
  | vreg rd =>
    by_cases below32 : rd.toNat < 32
    · simp only [writeDst_vreg, writeVReg, below32, ↓reduceIte,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at written
      cases written
    · simp only [writeDst_vreg, writeVReg, below32, ↓reduceIte,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at written
      cases written
      cases source with
      | xreg register => rfl
      | vreg rs =>
        have distinct : rs ≠ rd := by
          intro same
          subst rs
          exact different rfl
        simp only [sourceValue, distinct, ↓reduceIte]

private theorem sourceValue_writeDst_same (destination : Dst)
    (value : BitVec 64) (pre post : SailJoltState)
    (nonzero : TraceWitness.destinationRegisterAddress destination ≠ 0)
    (written : writeDst destination value pre = .ok () post) :
    sourceValue (destinationSource destination) post = value := by
  cases destination with
  | xreg rd =>
    simp only [writeDst_xreg, liftSail, wX_bits_stateAfterWrite] at written
    cases written
    have distinct : rd ≠ .Regidx 0 := by
      intro same
      subst rd
      exact nonzero rfl
    have read := readSrc_xreg_run_of_read rd
      { pre with sail := stateAfterWrite pre.sail rd value } value
      (rX_after_stateAfterWrite rd value pre.sail distinct)
    exact (lookup_readSrc_value _ _ _ _ read).2.symm
  | vreg rd =>
    by_cases below32 : rd.toNat < 32
    · simp only [writeDst_vreg, writeVReg, below32, ↓reduceIte,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at written
      cases written
    · simp only [writeDst_vreg, writeVReg, below32, ↓reduceIte,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at written
      cases written
      simp only [destinationSource, sourceValue, ↓reduceIte]

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- A selected instruction's successful destination write extends register
agreement to the next cycle when its value matches `RdWriteValue`. Canonicality
comes from expansion. The x0 case uses the proved zero-table invariant, since
Sail discards that write. The final cycle has no next register-table column. -/
theorem RegisterAgreement.write
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} (next : t.val + 1 < params.traceLength)
    (chosen : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode chosen.val = some row)
    {destination : Dst} (destinationIs : row.instruction.destination? = some destination)
    {pre post : SailJoltState} (agrees : RegisterAgreement witness t pre)
    (value : BitVec 64) (encoded : witness.RdWriteValue t = (value.toNat : F))
    (written : writeDst destination value pre = .ok () post) :
    RegisterAgreement witness ⟨t.val + 1, next⟩ post := by
  refine ⟨RegistersKept.write_rule destination value pre post () written agrees.present, ?_⟩
  intro register
  by_cases zero : register = 0
  · subst register
    rw [registersVal_x0 charAbove2pow128 context equations]
    change (0 : F) = ((0 : BitVec 64).toNat : F)
    simp
  have canonical := instruction_destination_canonical _ _
    (bytecodeRow_rowOk context rowIs).canonical destinationIs
  rw [registersVal_succ_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations register t next chosen selected]
  simp only [rowIs, Option.bind_some, bytecodeRdRegister_eq_destination,
    destinationIs, Option.map_some]
  by_cases same : register = TraceWitness.destinationRegisterAddress destination
  · subst register
    rw [if_pos rfl, encoded, source_of_destination destination canonical,
      sourceValue_writeDst_same destination value pre post zero written]
  · rw [if_neg same, agrees.values]
    rw [sourceValue_writeDst_other destination _ value pre post
      (by simpa only [source_encode_decode, BitVec.toFin_ofFin] using same)
      agrees.present written]

end JoltConstraints.Soundness
