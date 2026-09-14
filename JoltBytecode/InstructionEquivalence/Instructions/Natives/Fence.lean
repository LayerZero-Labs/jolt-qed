import Mathlib.Tactic.FinCases
import LeanRV64D.InstsEnd
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.JoltISA.Semantics

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `FENCE` equivalence statement. -/
def fenceInstrEqSailStatement
    (js : SailJoltState)
    (_h : FenceProgramEqSailAssumptions js) : Prop :=
  ∀ (fm pred succ : BitVec 4) (rs1 rd : regidx),
    System.systemProjectResult
      ((JoltISA.execInstr .FENCE).run js) =
      ((execute_FENCE fm pred succ rs1 rd).run js.sail)

/-- Native `FENCE` agrees with Sail `execute_FENCE`.

Sail computes an effective fence set and executes a backend barrier, but in the
generated Lean model the barrier is pure and the instruction returns success. -/
theorem fenceInstr_eq_sail
    (js : SailJoltState)
    (h : FenceProgramEqSailAssumptions js) :
    fenceInstrEqSailStatement js h := by
  unfold fenceInstrEqSailStatement
  intro fm pred succ rs1 rd
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js
      h.toNoSourceReadWithLinkedCSRs.linkedCSRs
  have h_jolt :
      (JoltISA.execInstr .FENCE).run js =
        .ok RETIRE_SUCCESS js := by
    rfl
  rw [h_jolt]
  simp only [System.systemProjectResult, h_project_initial]
  unfold execute_FENCE is_fiom_active Sail.readReg PreSail.readReg
  simp only [h.cur_privilege.value, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]
  simp only [effective_fence_set, Bool.false_eq_true, ↓reduceIte]
  generalize hp : Sail.BitVec.extractLsb pred 1 0 = p
  generalize hs : Sail.BitVec.extractLsb succ 1 0 = q
  cases p with
  | ofFin pfin =>
    cases q with
    | ofFin qfin =>
      fin_cases pfin <;> fin_cases qfin <;>
        simp only [Sail.ConcurrencyInterfaceV1.sail_barrier,
          PreSail.ConcurrencyInterfaceV1.sail_barrier, pure] <;>
        rfl

end Natives

end
