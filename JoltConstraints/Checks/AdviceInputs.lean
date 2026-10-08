import JoltConstraints.advice_inputs
import Lean.Util.CollectAxioms

-- These facts about what the relation observes must not use admitted results
-- or compiler evaluation, even while other completeness proofs remain open.
run_cmd do
  for name in #[`JoltInstance.initial_states_agree_on_trusted_advice,
      `JoltInstance.initial_state_with_advice_tape,
      `JoltConstraints.AllConstraints.advice_tape_irrelevant] do
    let axioms ← Lean.collectAxioms name
    if axioms.contains `sorryAx then
      throwError "{name} depends on sorryAx"
    if axioms.contains `Lean.ofReduceBool then
      throwError "{name} depends on compiler evaluation"
