import JoltTests.ExpansionParity.RoundTrip

/-!
# expansion-parity: Lean side of T1 and the inline round trip

Usage (from the repository root, after `lake build JoltTests.ExpansionParity.Main`):

```
EXPANSION_PARITY_ARGS="t1 ROWS.jsonl OUT_DIR" lake env lean JoltTests/ExpansionParity/Run.lean
EXPANSION_PARITY_ARGS="inline ROWS.jsonl TEMPLATES.json OUT_DIR [TRIPLES] [SEED]" lake env lean JoltTests/ExpansionParity/Run.lean
EXPANSION_PARITY_ARGS="mutation ROWS.jsonl [TEMPLATES.json]" lake env lean JoltTests/ExpansionParity/Run.lean
```

The arguments travel in an environment variable because `Run.lean` runs the
comparison with `#eval` (see `cli` below for why there is no executable).

`ROWS.jsonl` and `TEMPLATES.json` are the driver's `rows.jsonl` and
`inline_templates.json` (`scripts/expansion-parity/README.md`).

* `t1` compares every non-inline record with `expand_instruction` and
  `metadata.lean`, and writes `OUT_DIR/t1-mismatches.jsonl` and
  `OUT_DIR/t1-summary.txt`. A record whose Rust source kind has no Lean
  `SourceInstruction` constructor (NoOp, Unimpl and most Virtual* kinds) forms
  the separate class "row metadata compared, no Lean source constructor": each
  of its Rust rows is compared with `metadata.lean` for the row's kind and stamp.
  A record whose source kind is neither mapped to Lean nor listed in
  `noLeanSourceKinds` is reported as an unknown kind, and a record whose
  `result` is not exactly one of a rows array and an error string stops the run.
* `inline` compares every `inline_fixture` record, flags included, and every
  inline template at the driver's two triples and `TRIPLES` (default 300)
  seeded random triples per case, with the generated Lean rows. It also checks
  that the inputs are complete (`inlineCoverage`): every inline has a `normal`
  template and all eight fixture records. It writes
  `OUT_DIR/inline-mismatches.jsonl` and `OUT_DIR/inline-summary.txt`.
* `mutation` corrupts one field of one row of a T1 record and of an inline
  fixture record, once per compared field, and one metadata field of a record
  in the row-metadata class, and checks that the comparisons report each
  corruption. It also replaces the
  source kind with an unknown one and the `result` object with malformed ones,
  on a T1 record, a row-metadata record and a record both sides reject, and
  checks that each of these records is flagged. Given `TEMPLATES`, it also
  drops a `normal` template and drops, repeats or changes inline fixture
  records, and checks that the round trip reports each change.

`Run.lean` fails (and `lean` exits with 1) when a mode finds a disagreement.
-/

open Lean

namespace ExpansionParity

def runT1 (rowsPath outDir : String) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let lines ← readLines rowsPath
  let mut all : Array Mismatch := #[]
  let mut summary : Summary := {}
  let mut perGroup : Std.HashMap String Nat := {}
  let mut agreeGroup : Std.HashMap String Nat := {}
  let mut rejectHow : Std.HashMap String Nat := {}
  let mut inlineSkipped := 0
  let mut sourceKinds : Std.HashSet String := {}
  -- The class "row metadata compared, no Lean source constructor".
  let mut metaAll : Array Mismatch := #[]
  let mut metaSummary : Summary := {}
  let mut metaGroup : Std.HashMap String Nat := {}
  let mut metaAgree : Std.HashMap String Nat := {}
  let mut metaKinds : Std.HashSet String := {}
  let mut metaRows := 0
  for line in lines do
    let r ← parseRecord line
    sourceKinds := sourceKinds.insert r.source.kind
    match compareT1 r with
    | .inline => inlineSkipped := inlineSkipped + 1
    | .bothReject how =>
        perGroup := bump perGroup r.group
        agreeGroup := bump agreeGroup r.group
        rejectHow := bump rejectHow s!"{r.source.kind}: Rust {r.error.getD "?"}; Lean: {how}"
    | .compared ms =>
        perGroup := bump perGroup r.group
        if ms.isEmpty then agreeGroup := bump agreeGroup r.group
        for m in ms do
          all := all.push m
          summary := summary.add m
    | .metadataOnly ms =>
        metaGroup := bump metaGroup r.group
        metaKinds := metaKinds.insert r.source.kind
        metaRows := metaRows + (r.rows.map List.length).getD 0
        if ms.isEmpty then metaAgree := bump metaAgree r.group
        for m in ms do
          metaAll := metaAll.push m
          metaSummary := metaSummary.add m
  writeMismatches (outDir ++ "/t1-mismatches.jsonl") (all ++ metaAll)
  let records (ms : Array Mismatch) := (ms.map (fun m => (m.case, m.allocator))).toList.eraseDups.length
  let mismatched := records all
  let total (m : Std.HashMap String Nat) := m.fold (fun acc _ n => acc + n) 0
  let absentZicsr := zicsrRemainingKinds.filter (!sourceKinds.contains ·)
  let metaKindList := (metaKinds.toArray.qsort (· < ·)).toList
  let text :=
    s!"T1 expansion parity: {rowsPath}\n" ++
    s!"records compared per group: {renderCounts perGroup}\n" ++
    s!"records that agree per group: {renderCounts agreeGroup}\n" ++
    s!"inline records left to the inline round trip: {inlineSkipped}\n" ++
    s!"records with a disagreement: {mismatched}; field mismatches: {all.size}\n" ++
    s!"Lean source kinds with no record in this input: {absentZicsr}\n\n" ++
    "Rejected by both sides:\n" ++
    String.join ((rejectHow.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map
      fun (k, n) => s!"- {k} ({n} records)\n") ++
    "\nDisagreements by cause:\n" ++ summary.render ++
    "\nRow metadata compared, no Lean source constructor:\n" ++
    s!"records per group: {renderCounts metaGroup} (total {total metaGroup}, {metaRows} rows)\n" ++
    s!"records that agree per group: {renderCounts metaAgree} (total {total metaAgree})\n" ++
    s!"records with a disagreement: {records metaAll}; field mismatches: {metaAll.size}\n" ++
    s!"source kinds ({metaKindList.length}): {metaKindList}\n" ++
    "Disagreements by cause:\n" ++ metaSummary.render
  IO.FS.writeFile (outDir ++ "/t1-summary.txt") text
  IO.println text
  return if all.isEmpty && metaAll.isEmpty then 0 else 1

/-- The mutation check on the first T1 record with at least ten rows, on the
first record of the row-metadata class whose row 0 carries circuit and
instruction flags and a table and agrees with `metadata.lean`, and on the first
record that both sides reject because Lean has no constructor for its kind, and
on the first inline fixture record. Given the templates file, it also deletes
and repeats inputs of the inline round trip (`coverageMutationCheck`). -/
def runMutation (rowsPath : String) (templatesPath : Option String) : IO UInt32 := do
  let mut t1Rec : Option Json := none
  for line in ← readLines rowsPath do
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (RecordInfo.ofJson j)
    if r.source.kind != "Inline" && (r.rows.map List.length).getD 0 ≥ 10 then
      t1Rec := some j
      break
  let some tj := t1Rec | throw <| IO.userError "no T1 record with 10 rows"
  let t1cmp (r : RecordInfo) : List Mismatch :=
    match compareT1 r with
    | .compared ms => ms
    | _ => []
  let metaCmp (r : RecordInfo) : List Mismatch :=
    match compareT1 r with
    | .metadataOnly ms => ms
    | _ => []
  let mut metaRec : Option Json := none
  for line in ← readLines rowsPath do
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (RecordInfo.ofJson j)
    let flagged := match r.rows with
      | some (row :: _) =>
          !(row.circuitFlags.getD []).isEmpty && !(row.instructionFlags.getD []).isEmpty &&
            (row.lookupTable.getD none).isSome
      | _ => false
    if let .metadataOnly [] := compareT1 r then
      if flagged then
        metaRec := some j
        break
  let some mj := metaRec | throw <| IO.userError "no agreeing row-metadata record"
  let mut rejRec : Option Json := none
  for line in ← readLines rowsPath do
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (RecordInfo.ofJson j)
    if let .bothReject _ := compareT1 r then
      if noLeanSourceKinds.contains r.source.kind then
        rejRec := some j
        break
  let some rj := rejRec | throw <| IO.userError "no record that both sides reject by kind"
  let ok ← mutationCheck "t1" tj t1cmp
  let ok := (← mutationCheck "t1_metadata" mj metaCmp metadataMutations) && ok
  let ok := (← recordMutationCheck "t1 record" tj (recordMutations tj)) && ok
  let ok := (← recordMutationCheck "t1_metadata record" mj (recordMutations mj)) && ok
  let ok := (← recordMutationCheck "both-reject record" rj (recordMutations rj)) && ok
  let ok := (← mutationCheck "inline" (← firstInlineFixture rowsPath) compareInlineFixture) && ok
  let ok ← match templatesPath with
    | some t => pure ((← coverageMutationCheck rowsPath t) && ok)
    | none => pure ok
  IO.println (if ok then "mutation check: every corruption detected" else "mutation check: FAILED")
  return if ok then 0 else 1

/-- The command line. `LeanRV64D.lean` declares a root `main` (the Sail model's
entry point), so no executable that imports the model can declare its own;
`Run.lean` calls this function instead. -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["t1", rows, out] => runT1 rows out
  | ["inline", rows, templates, out] => runInline rows templates out 300 1949392621
  | ["inline", rows, templates, out, n] => runInline rows templates out n.toNat! 1949392621
  | ["inline", rows, templates, out, n, seed] => runInline rows templates out n.toNat! seed.toNat!
  | ["mutation", rows] => runMutation rows none
  | ["mutation", rows, templates] => runMutation rows (some templates)
  | _ =>
    IO.eprintln "usage: EXPANSION_PARITY_ARGS='t1 ROWS OUT | inline ROWS TEMPLATES OUT [TRIPLES [SEED]] | mutation ROWS [TEMPLATES]'"
    return 2

end ExpansionParity
