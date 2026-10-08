import JoltConstraints.Completeness.All
import Lean.Util.CollectAxioms
import Lean

-- The old statement admitted arbitrary pre-states. Its replacement must be
-- proved, and the honest witness must use it to obtain the store's old word.
run_cmd do
  let env ← Lean.getEnv
  if env.contains `HonestTraceRow.store_word_present then
    throwError "the unrestricted store_word_present lemma must not exist"
  unless env.contains `HonestTrace.store_word_present do
    throwError "the trace-indexed store_word_present lemma is missing"
  let axioms ← Lean.collectAxioms `HonestTrace.store_word_present
  if axioms.contains `sorryAx then
    throwError "HonestTrace.store_word_present depends on sorryAx"
  for name in #[`HonestTrace.honestWitness, `HonestTrace.allConstraints_rust_sizes] do
    let (_, dependencies) := ((Lean.CollectAxioms.collect name).run env).run {}
    unless dependencies.visited.contains `HonestTrace.store_word_present do
      throwError "{name} lost its dependency on HonestTrace.store_word_present"
