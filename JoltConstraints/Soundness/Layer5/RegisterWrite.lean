import JoltConstraints.Soundness.Layer2.RegisterMap

/-! A concrete post-state for a destination write. Expanded bytecode uses
canonical operands, so a virtual destination cannot name a protected index
below 32. Architectural x0 writes follow Sail and leave x0 unchanged. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- The state after a destination write: architectural writes use Sail's
register update and virtual writes replace one virtual-register value. -/
noncomputable def afterWriteDst (destination : Dst) (value : BitVec 64)
    (state : SailJoltState) : SailJoltState :=
  match destination with
  | .xreg register => { state with sail := stateAfterWrite state.sail register value }
  | .vreg register =>
      { state with vregs := fun r => if r = register then value else state.vregs r }

private theorem canonical_vreg_writable (register : JoltISA.VReg)
    (canonical : JoltRegisterEncoding.destinationIsCanonical (.vreg register) = true) :
    WritableVReg register := by
  intro below32
  have same : TraceWitness.destinationRegisterAddress (.vreg register) =
      TraceWitness.destinationRegisterAddress (.xreg (.Regidx (register.setWidth 5))) := by
    apply Fin.ext
    change register.toNat = ((register.setWidth 5).setWidth 7).toNat
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt below32, Nat.mod_eq_of_lt register.isLt]
  have impossible := destinationRegisterAddress_injective canonical rfl same
  cases impossible

/-- Every canonical destination write succeeds with the concrete post-state.
Canonicality is supplied by the selected bytecode row, not an execution premise. -/
theorem writeDst_afterWriteDst (destination : Dst)
    (canonical : JoltRegisterEncoding.destinationIsCanonical destination = true)
    (value : BitVec 64) (state : SailJoltState) :
    writeDst destination value state = .ok () (afterWriteDst destination value state) := by
  cases destination with
  | xreg register =>
    simp only [writeDst_xreg, liftSail, wX_bits_stateAfterWrite, afterWriteDst]
  | vreg register =>
    exact writeVReg_run_of_writable register value state
      (canonical_vreg_writable register canonical)

end JoltConstraints.Soundness
