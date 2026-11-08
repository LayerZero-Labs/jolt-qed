import JoltConstraints.WholeRun.Blocks

/-!
# Chaining Sail steps along the blocks of a run

`HonestTrace.blocks` cuts an honest Jolt trace into one block per source
instruction. This file turns a per-block simulation into a whole-run one: if
every block's Jolt step is matched by one `try_step` under a relation `R`,
then `sailRun` over the blocks ends in a Sail state related to the trace's last
Jolt state.

The relation is a parameter here. `docs/riscv-alignment.md`, section 9, says
which relation the whole-run theorem uses and what each block obligation rests
on.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- One block's Jolt step is matched by one Sail step: from every Sail state
related to the block's first Jolt state, `try_step` succeeds and lands in a
state related to the block's last Jolt state. -/
def BlockSimulates (R : SailJoltState → SailState → Prop) (b : Block) : Prop :=
  ∀ s, R b.pre s → ∃ (v : Bool) (s' : SailState), try_step 0 false s = .ok v s' ∧ R b.post s'

theorem sailRun_succ (k : Nat) (s s' : SailState) (v : Bool)
    (h : try_step 0 false s = .ok v s') : sailRun (k + 1) s = sailRun k s' := by
  simp only [sailRun, h]

/-- **Blocks chain into a Sail run.** -/
theorem sailRun_of_chain (R : SailJoltState → SailState → Prop) :
    ∀ (bs : List Block), bs.IsChain (fun b c => b.post = c.pre) →
      (∀ b ∈ bs, BlockSimulates R b) →
      ∀ (first : Block), bs.head? = some first →
      ∀ (s : SailState), R first.pre s →
      ∃ (last : Block) (s' : SailState), bs.getLast? = some last ∧
        sailRun bs.length s = .ok () s' ∧ R last.post s'
  | [], _, _, _, hfirst, _, _ => by simp at hfirst
  | [b], _, hsim, first, hfirst, s, hs => by
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      subst hfirst
      obtain ⟨v, s', hstep, hs'⟩ := hsim b (by simp) s hs
      refine ⟨b, s', by simp, ?_, hs'⟩
      simp only [List.length_singleton, sailRun_succ 0 s s' v hstep, sailRun]
  | b :: c :: rest, hchain, hsim, first, hfirst, s, hs => by
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      subst hfirst
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hlink, hchain'⟩ := hchain
      obtain ⟨v, s', hstep, hs'⟩ := hsim b (by simp) s hs
      have hs'c : R c.pre s' := hlink ▸ hs'
      obtain ⟨last, s'', hlast, hrun, hrel⟩ :=
        sailRun_of_chain R (c :: rest) hchain'
          (fun d hd => hsim d (List.mem_cons_of_mem _ hd)) c rfl s' hs'c
      refine ⟨last, s'', ?_, ?_, hrel⟩
      · simpa [List.getLast?_cons_cons] using hlast
      · simp only [List.length_cons] at hrun ⊢
        rw [sailRun_succ _ s s' v hstep]
        exact hrun

/-- **An honest trace is a Sail run, given a block simulation.** If `R` relates
the trace's initial Jolt state to `s₀`, and every block of the trace's
decomposition is simulated, then `sailRun` from `s₀` succeeds and ends in a
state related to the trace's final Jolt state. -/
theorem HonestTrace.sailRun {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (R : SailJoltState → SailState → Prop)
    (hsim : ∀ b : Block, b.Runs joltInstance.program → BlockSimulates R b)
    (s₀ : SailState) (h₀ : R trace.initialState s₀) :
    ∃ (n : Nat) (final : SailJoltState) (s : SailState),
      trace.rows.back?.map (·.postState) = some final ∧
      sailRun n s₀ = .ok () s ∧ R final s := by
  obtain ⟨bs, hne, hruns, hhead, hchain, hlast, -⟩ := HonestTrace.blocks trace
  obtain ⟨first, hfirst⟩ : ∃ first, bs.head? = some first := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b _ => exact ⟨b, rfl⟩
  have hpre : first.pre = trace.initialState := by
    rw [hfirst] at hhead
    simpa using hhead
  obtain ⟨last, s, hl, hrun, hrel⟩ :=
    sailRun_of_chain R bs hchain (fun b hb => hsim b (hruns b hb)) first hfirst s₀
      (hpre ▸ h₀)
  refine ⟨bs.length, last.post, s, ?_, hrun, hrel⟩
  rw [← hlast, hl]
  rfl

end WholeRun
