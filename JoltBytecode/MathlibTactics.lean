import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Use

/-!
The Mathlib tactics that JoltBytecode and JoltConstraints proofs use.

Import this file instead of `Mathlib.Tactic` or `Mathlib`. Each of those
umbrella imports loads several thousand Mathlib modules into every downstream
module, which roughly doubles each module's import time and triples its
memory use. When a proof needs another Mathlib tactic, add its module here;
when it needs a Mathlib lemma, import the module that states it.
-/
