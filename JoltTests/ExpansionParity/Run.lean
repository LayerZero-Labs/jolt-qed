import JoltTests.ExpansionParity.Main

/-!
# Runner for the expansion-parity comparator

`lake env lean JoltTests/ExpansionParity/Run.lean` runs `ExpansionParity.cli`
on the space-separated arguments in `EXPANSION_PARITY_ARGS` (usage in `Main.lean`).
The `#eval` throws when the comparison reports a disagreement, so `lean` exits
with a nonzero status.
No module imports this file; building the `JoltTests` library never runs it.
-/

#eval show IO Unit from do
  let args := ((← IO.getEnv "EXPANSION_PARITY_ARGS").getD "").splitOn " "
  let code ← ExpansionParity.cli (args.filter (!·.isEmpty))
  if code != 0 then
    throw <| IO.userError s!"expansion-parity: exit status {code}"
