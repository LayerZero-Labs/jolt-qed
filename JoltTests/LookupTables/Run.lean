import JoltTests.LookupTables.Main

/-!
# Runner for the lookup-table comparator

`lake env lean JoltTests/LookupTables/Run.lean` runs `LookupTables.cli` on the
space-separated arguments in `LOOKUP_TABLES_ARGS` (usage in `Main.lean`).
The `#eval` throws when the comparison reports a disagreement, so `lean` exits
with a nonzero status.
No module imports this file; building the `JoltTests` library never runs it.
-/

#eval show IO Unit from do
  let args := ((← IO.getEnv "LOOKUP_TABLES_ARGS").getD "").splitOn " "
  let code ← LookupTables.cli (args.filter (!·.isEmpty))
  if code != 0 then throw <| IO.userError s!"lookup-tables: exit status {code}"
