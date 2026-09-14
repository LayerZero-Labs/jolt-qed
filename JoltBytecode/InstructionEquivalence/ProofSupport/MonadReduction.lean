import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
TODO: Not sure these are being used anymore.
# Shared monadic reduction lemmas

These lemmas isolate the small `EStateM.run` manipulations that appear when
unfolding Sail instruction definitions. The goal is to discharge the plumbing
once, so instruction proofs can return quickly to pure state facts.
-/

-- If running `m` from `s` succeeds with value `a` and state `s'`, then
-- binding `m` into `f` is the same as running `f a` from `s'`.
theorem run_bind_eq_ok
    {ε σ α β : Type} {m : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {a : α}
    (h : EStateM.run m s = .ok a s') :
    EStateM.run (m.bind f) s = EStateM.run (f a) s' := by
  change (match EStateM.run m s with
    | .ok a' s'' => EStateM.run (f a') s''
    | .error e s'' => .error e s'') = EStateM.run (f a) s'
  rw [h]

-- A pure computation at the front of a monadic run can be removed directly.
theorem run_bind_pure
    {ε σ α β : Type} {a : α} {f : α → EStateM ε σ β} {s : σ} :
    EStateM.run ((EStateM.pure a).bind f) s = EStateM.run (f a) s := by
  change (match EStateM.run (EStateM.pure a) s with
    | .ok a' s' => EStateM.run (f a') s'
    | .error e s' => .error e s') = EStateM.run (f a) s
  rfl



end
