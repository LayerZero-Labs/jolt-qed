import JoltConstraints.Soundness.Layer5.RamInitialization
import JoltConstraints.Soundness.Layer5.RegisterWrite
import JoltConstraints.Soundness.Layer3.Access
import JoltConstraints.Soundness.Layer3.Address

/-! Agreement between an ordinary-RAM table column and the interpreter's
byte-map words. The fixed layout identifies the table's address grid. This
relation says nothing about device words below RAM_START_ADDRESS. It is an
induction invariant: initialization proves it, and step lemmas preserve it.
The same relation applies to a cycle column or to RamValFinal. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

variable {F : Type} [Field F] {size : Nat}

/-- Ordinary-RAM entries of a table column encode the corresponding byte-map
words, with zero for absent bytes as in Jolt's RAM implementation. -/
def OrdinaryRamAgreement (layout : MemoryLayout) (values : Fin size → F)
    (state : SailJoltState) : Prop :=
  ∀ index, RAM_START_ADDRESS ≤ ramLowestAddress layout + 8 * index.val →
    values index = ((Mmu.ram_doubleword state.sail.mem
      (ramLowestAddress layout + 8 * index.val)).toNat : F)

/-- Preparing a source instruction's PC preserves all ordinary-RAM words. -/
theorem OrdinaryRamAgreement.advance_pc {layout : MemoryLayout} {values : Fin size → F}
    {state : SailJoltState} (agrees : OrdinaryRamAgreement layout values state)
    (address : BitVec 64) (compressed : Bool) :
    OrdinaryRamAgreement layout values (advance_pc address compressed state) := agrees

/-- A destination-register write preserves ordinary-RAM agreement with the
same table column, including architectural x0 and virtual destinations. -/
theorem OrdinaryRamAgreement.afterWriteDst {layout : MemoryLayout} {values : Fin size → F}
    {state : SailJoltState} (agrees : OrdinaryRamAgreement layout values state)
    (destination : Dst) (value : BitVec 64) :
    OrdinaryRamAgreement layout values (afterWriteDst destination value state) := by
  cases destination <;> exact agrees

variable {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- The initialized RAM table agrees with actual ordinary-RAM reads. The
disjointness of advice/input overlays is proved from the checked layout. -/
theorem OrdinaryRamAgreement.initial
    (context : ConstraintContext joltInstance privateInputs params)
    (history : ramValEqInitialPlusPrefixRamInc context.initialRam witness)
    {state : SailJoltState} (built : joltInstance.initial_state privateInputs = some state) :
    OrdinaryRamAgreement context.io.memory_layout
      (fun index => witness.RamVal index ⟨0, Nat.two_pow_pos _⟩) state := by
  intro index inRam
  change witness.RamVal index ⟨0, Nat.two_pow_pos _⟩ = _
  rw [ramVal_initial_state context history built index,
    initialRamWord_eq_ram_doubleword context built index.val inRam]

/-- The read column at a selected ordinary-RAM address is the actual byte-map
word. This uses agreement at the current cycle, not an honest-witness premise. -/
theorem OrdinaryRamAgreement.read
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {state : SailJoltState}
    (agrees : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) state)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1)
    (address : BitVec 64) (encoded : witness.RamAddress t = (address.toNat : F))
    (inRam : RAM_START_ADDRESS ≤ address.toNat) :
    witness.RamReadValue t = ((Mmu.ram_doubleword state.sail.mem address.toNat).toNat : F) := by
  have addressIs := ramAddress_eq_of_selected charAbove2pow127 context equations t chosen selected
    address encoded
  rw [ramReadValue_of_selected charAbove2pow127 context equations t chosen selected, addressIs]
  exact agrees chosen (by rwa [← addressIs])

/-- Zero RAM effects and an unchanged byte map preserve agreement at a
successor cycle and at the final column. Load and non-memory callers derive
the zero effects from their selected instruction's flags. -/
theorem OrdinaryRamAgreement.noEffect
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {pre post : SailJoltState}
    (agrees : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (sameMemory : post.sail.mem = pre.sail.mem)
    (zero : ∀ index, witness.RamRa index t * witness.RamInc t = 0) :
    (∀ next : t.val + 1 < params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) post) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  constructor
  · intro next index inRam
    change witness.RamVal index ⟨t.val + 1, next⟩ = _
    rw [ramVal_succ equations.ramValEqInitialPlusPrefixRamInc index t next, zero, add_zero]
    simpa only [sameMemory] using agrees index inRam
  · intro last index inRam
    rw [ramValFinal_eq_last_update equations.ramValEqInitialPlusPrefixRamInc
      equations.ramValFinalEqInitialPlusRamInc index t last, zero, add_zero]
    simpa only [sameMemory] using agrees index inRam

/-- A selected non-memory cycle has no RAM selector, so an unchanged byte map
preserves ordinary-RAM agreement through the next or final column. -/
theorem OrdinaryRamAgreement.noAccess
    (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    {t : Fin params.traceLength} {pre post : SailJoltState}
    (agrees : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (sameMemory : post.sail.mem = pre.sail.mem)
    (noLoad : witness.OpFlags .Load t = 0)
    (noStore : witness.OpFlags .Store t = 0) :
    (∀ next : t.val + 1 < params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) post) ∧
    (∀ _last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal post) := by
  have zeroAddress := ramAddress_zero_of_not_load_store
    equations.ramAddrEqZeroIfNotLoadStore t noLoad noStore
  have zeroSelector := (ramRa_zero_iff_address_zero charAbove2pow127
    context equations t).mpr zeroAddress
  exact agrees.noEffect context equations sameMemory (fun index => by
    simp only [zeroSelector index, zero_mul])

end JoltConstraints.Soundness
