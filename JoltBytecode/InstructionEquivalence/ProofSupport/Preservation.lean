import JoltBytecode.JoltISA.Core

/-
Rules for proving that successful stateful computations preserve a relation
between their initial and final states. The relation can express equality of
selected fields, preservation of an invariant, or inclusion of a memory domain.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace StatePreservation

def Preserves {ε σ α : Type} (relation : σ → σ → Prop) (step : EStateM ε σ α) : Prop :=
  ∀ before after value, step before = .ok value after → relation before after

theorem pure_rule {ε σ α : Type} {relation : σ → σ → Prop}
    (refl : ∀ state, relation state state) (value : α) :
    Preserves relation (pure value : EStateM ε σ α) := by
  intro before after result runs
  cases runs
  exact refl before

theorem bind_rule {ε σ α β : Type} {relation : σ → σ → Prop}
    (trans : ∀ before middle after, relation before middle → relation middle after →
      relation before after)
    {first : EStateM ε σ α} {next : α → EStateM ε σ β}
    (keepsFirst : Preserves relation first)
    (keepsNext : ∀ value, Preserves relation (next value)) :
    Preserves relation (first >>= next) := by
  intro before after result runs
  cases firstRun : first before with
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    cases runs
  | ok value middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    exact trans before middle after (keepsFirst before middle value firstRun)
      (keepsNext value middle after result runs)

theorem get_rule {ε σ : Type} {relation : σ → σ → Prop}
    (refl : ∀ state, relation state state) :
    Preserves relation (get : EStateM ε σ σ) := by
  intro before after value runs
  cases runs
  exact refl before

theorem throw_rule {ε σ α : Type} (relation : σ → σ → Prop) (failure : ε) :
    Preserves relation (throw failure : EStateM ε σ α) := by
  intro before after value runs
  cases runs

theorem modify_rule {ε σ : Type} {relation : σ → σ → Prop} (change : σ → σ)
    (keeps : ∀ state, relation state (change state)) :
    Preserves relation (modify change : EStateM ε σ Unit) := by
  intro before after value runs
  cases runs
  exact keeps before

theorem liftSail_rule {α : Type} {relation : SailJoltState → SailJoltState → Prop}
    {sailRelation : SailState → SailState → Prop} {step : SailM α}
    (lift : ∀ state after, sailRelation state.sail after →
      relation state { state with sail := after })
    (keeps : Preserves sailRelation step) : Preserves relation (liftSail step) := by
  intro before after value runs
  unfold liftSail at runs
  cases stepRun : step before.sail with
  | error failure sail => rw [stepRun] at runs; cases runs
  | ok result sail =>
    rw [stepRun] at runs
    cases runs
    exact lift before sail (keeps before.sail sail _ stepRun)

end StatePreservation

-- Each use supplies its leaf rules and the bind rule for its state relation.
macro "preservation_auto" "[" rules:term,* "]" "using" bindRule:term : tactic => do
  let mut step ← `(tactic| first | split | refine ($bindRule) ?_ (fun _ => ?_))
  for rule in rules.getElems.reverse do
    let previous ← `(tacticSeq| $step:tactic)
    step ← `(tactic| first | with_reducible exact $rule | $previous)
  let sequence ← `(tacticSeq| $step:tactic)
  `(tactic| repeat' $sequence)
