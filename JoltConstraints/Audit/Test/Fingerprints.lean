import JoltConstraints.Audit.Commands
import JoltConstraints.Audit.Test.PrivateA
import JoltConstraints.Audit.Test.PrivateB
import JoltConstraints.Audit.Test.Gate

/-!
# Regression tests for the statement fingerprints of `#audit_statements`

Each test computes the fingerprint table of `JoltConstraints/Audit/Commands.lean`
(`actualTable`) for a few roots declared in the fixture modules of this folder, and fails the
build when the table could hide a changed definition:

1. Two private declarations with the same name in different modules (`PrivateA.lean`,
   `PrivateB.lean`) get one table line each. A table keyed by the name without the private
   prefix would keep one line for both, and a change to the other would not show.
2. The fingerprint of an owner covers every member that any root reaches. In `Gate.lean`,
   `rootFull` reaches the projection `Gate.width` and `rootPartial` does not; listing
   `rootPartial` after `rootFull` must not drop `Gate.width` from the fingerprint of `Gate`.
3. The fingerprint lines do not depend on the order of the roots.
-/

open Lean Elab Command

namespace JoltConstraints.Audit.Test

-- Test 1: the two private `allowed` declarations each have their own line, under a key that
-- keeps the private module.
run_cmd do
  let (table, _) ← actualTable #[``rootA, ``rootB]
  let lines := table.fingerprints.filter (·.1.endsWith "Test.allowed")
  unless lines.size == 2 do
    throwError "expected two fingerprint lines for the private `allowed` of PrivateA.lean and \
      PrivateB.lean, got {lines.toList}"
  unless lines.all (·.1.startsWith "_private.") do
    throwError "the key of a private declaration must keep its private module, got \
      {lines.toList.map (·.1)}"
  unless lines[0]!.2 != lines[1]!.2 do
    throwError "the two private `allowed` declarations have different values, but the same \
      fingerprint {lines[0]!.2}"

-- Test 2: listing `rootPartial` after `rootFull` keeps `Gate.width` in the fingerprint of
-- `Gate`, which is then the same as for `rootFull` alone.
run_cmd do
  let gate (roots : Array Name) : CommandElabM (Option String) := do
    let (table, _) ← actualTable roots
    return (table.fingerprints.find? (·.1 == "JoltConstraints.Audit.Test.Gate")).map (·.2)
  let full ← gate #[``rootFull]
  let both ← gate #[``rootFull, ``rootPartial]
  let partial_ ← gate #[``rootPartial]
  unless full.isSome && full != partial_ do
    throwError "the fixture is wrong: the fingerprint of Gate should depend on whether the \
      roots reach Gate.width ({full} for rootFull, {partial_} for rootPartial)"
  unless both == full do
    throwError "the fingerprint of Gate for [rootFull, rootPartial] is {both}, but for rootFull \
      alone it is {full}: a later root dropped Gate.width"

-- Test 3: the fingerprint lines and the users of each line do not depend on the order of the
-- roots.
run_cmd do
  let roots := #[``rootFull, ``rootPartial, ``rootA, ``rootB]
  let (forward, forwardUsers) ← actualTable roots
  let (backward, backwardUsers) ← actualTable roots.reverse
  unless forward.fingerprints == backward.fingerprints do
    throwError "the fingerprint lines depend on the order of the roots:\n\
      {forward.fingerprints.toList}\nreversed:\n{backward.fingerprints.toList}"
  let sorted (users : Std.HashMap String (Array Name)) : List (String × List Name) :=
    (users.toArray.qsort (·.1 < ·.1)).toList.map fun (key, names) =>
      (key, (names.qsort Name.lt).toList)
  unless sorted forwardUsers == sorted backwardUsers do
    throwError "the users of the fingerprint lines depend on the order of the roots"

end JoltConstraints.Audit.Test
