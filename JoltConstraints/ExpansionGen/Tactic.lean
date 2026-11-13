import JoltConstraints.expansions
import Mathlib.Tactic.IntervalCases

/-!
# Proof support for the generated expansion recipes

`JoltConstraints/ExpansionGen/Equiv.lean` proves, kind by kind, that
`SourceInstruction.expand` equals the recipe that the T6 generator derived from
Jolt (`JoltConstraints/ExpansionGen/Generated.lean`).
Both sides branch only on register identity (`isX0`, `sameXReg`), on the CSR,
and on the five-bit constant of the immediate CSR forms.
The tactics below unfold both sides, split every `if`, turn each register
condition into an equation or a disequation between registers, substitute the
equations, and close each branch by `rfl` or by a contradiction among the
hypotheses.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open JoltISA

set_option autoImplicit false

namespace ExpansionGen

/-- `isX0 r` holds exactly when `r` is `x0`.
For example, `isX0 (regidx.Regidx 0) = true` and `isX0 (regidx.Regidx 5) = false`. -/
theorem isX0_eq_true (r : regidx) : isX0 r = true ↔ r = regidx.Regidx 0 := by
  rcases r with ⟨b⟩
  simp only [isX0, decide_eq_true_eq, regidx.Regidx.injEq]
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl
    rfl

/-- `isX0 r` fails exactly when `r` is not `x0`.
For example, `isX0 (regidx.Regidx 5) = false`. -/
theorem isX0_eq_false (r : regidx) : isX0 r = false ↔ ¬ r = regidx.Regidx 0 := by
  rw [← isX0_eq_true, Bool.not_eq_true]

/-- `sameXReg a b` holds exactly when `a` and `b` are the same register.
For example, `sameXReg (regidx.Regidx 3) (regidx.Regidx 3) = true`. -/
theorem sameXReg_eq_true (a b : regidx) : sameXReg a b = true ↔ a = b := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  simp only [sameXReg, decide_eq_true_eq, regidx.Regidx.injEq]

/-- `sameXReg a b` fails exactly when `a` and `b` differ.
For example, `sameXReg (regidx.Regidx 3) (regidx.Regidx 4) = false`. -/
theorem sameXReg_eq_false (a b : regidx) : sameXReg a b = false ↔ ¬ a = b := by
  rw [← sameXReg_eq_true, Bool.not_eq_true]

/-- Every five-bit vector is `BitVec.ofNat 5 n` for some `n < 32`.
For example, `5#5 = BitVec.ofNat 5 5`. -/
theorem bitVec_exists_ofNat {w : Nat} (u : BitVec w) :
    ∃ n, n < 2 ^ w ∧ u = BitVec.ofNat w n :=
  ⟨u.toNat, u.isLt, by simp⟩

/-- Closes a goal after every `if` is split: rewrites the register conditions
into (dis)equations, substitutes the equations and finishes by `rfl` or by a
contradiction. -/
syntax "recipe_close" : tactic

macro_rules
  | `(tactic| recipe_close) => `(tactic| (
      (try split_ifs) <;>
      (try simp only [isX0_eq_true, isX0_eq_false, sameXReg_eq_true, sameXReg_eq_false,
          Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_false_iff,
          Bool.not_eq_false', not_and, not_not] at *) <;>
      (try subst_vars) <;>
      first
        | rfl
        | (exfalso; simp_all)
        | simp_all))

/-- Unfolds `SourceInstruction.expand`, the generated recipe and the model's
expansion programs (the extra names), then closes the goal with
`recipe_close`. -/
syntax "recipe" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| recipe [$extra,*]) => `(tactic| (
      simp only [SourceInstruction.expand, ExpandedSource.ofNative, ExpandedSource.ofProgram,
        ExpandedSource.ofPureProgram, Program.instrs, Instr.rewriteNative, Instr.destination?,
        sideEffectingDst, sideEffectingRdZeroDst, pureWritebackRdZeroProgram, $extra,*]
      all_goals recipe_close))

/-- Enumerates a bit vector of a small width `w`: replaces `u` by
`BitVec.ofNat w n` for each `n < 2 ^ w`. -/
syntax "bitvec_cases " ident : tactic

macro_rules
  | `(tactic| bitvec_cases $u) => `(tactic| (
      obtain ⟨n, hn, h⟩ := bitVec_exists_ofNat $u
      subst h
      norm_num at hn
      interval_cases n))

end ExpansionGen
