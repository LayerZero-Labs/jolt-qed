import JoltTests.InlineKat.Manifest
import Lean.Data.Json.Parser

/-!
# `inline-kat`: Jolt's hash inlines against their specifications

`lake exe inline-kat [--jolt-commit SHA] CASES.json` reads the cases that `scripts/inline-kat`
recorded from Jolt's tracer and checks each one against the specifications in
`JoltBytecode/Inlines`.

For each case the JSON holds the bytes at `rs1` and `rs2` before and after the inline ran.
`JoltTests.InlineKat.Layout` turns the bytes before into the specification's arguments and its
result back into bytes. A judged case passes when:

- the bytes the tracer left at `rs1` equal the specification's result;
- the bytes at `rs2` did not change;
- the bytes at `rs1` start with the published answer, when the case has one;
- the registers `x1` to `x31` did not change;
- the tracer ran as many rows as the inline's expansion has.

The program decides itself which cases are judged: every case is, except a `BLAKE2` case whose
final-block flag is outside {0, 1}, which the specification does not cover. Such a case is
reported as informational. A case whose `judged` field disagrees fails.

The corpus as a whole must also be complete. It fails when:

- its `jolt_commit` is not `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`, or the commit given with
  `--jolt-commit`;
- its table of inlines is not exactly the five hash inlines;
- an inline has fewer judged cases than `requiredInlines` asks, or two cases with one name;
- a case of `JoltTests.InlineKat.Manifest` is missing, has another input, lacks its published
  answer or records another one, or the tracer's result does not start with that answer.

The program prints one line per case, a summary per inline and the corpus failures, and exits
with status 1 if anything failed.
-/
open Lean JoltTests.InlineKat JoltSpec

namespace JoltTests.InlineKat.Main

/-- What the BLAKE2 builder computes for any flag value: the model's compression with
`0 - flag` XORed into word 14 of the work vector.

This is not a specification. With flag 1 the mask is all ones and this is
`Blake2b.Spec.compress 12 h m t true`, and with flag 0 it is the same with `false`. The program
uses it only to describe the informational cases, whose flags the specification does not cover. -/
def blake2WithMask (h : Vector Blake2b.Spec.Word 8) (m : Vector Blake2b.Spec.Word 16)
    (t : BitVec 128) (mask : Blake2b.Spec.Word) : Vector Blake2b.Spec.Word 8 :=
  let v : Vector Blake2b.Spec.Word 16 := h ++ Blake2b.IV.map UInt64.toBitVec
  let v := v.set 12 (v[12] ^^^ t.setWidth 64)
  let v := v.set 13 (v[13] ^^^ (t >>> 64).setWidth 64)
  let v := v.set 14 (v[14] ^^^ mask)
  let v := Blake2b.Spec.rounds m v 12
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- The size of the words the state is made of: 4 bytes for SHA-256, 8 for the others. -/
def wordSize (inline : String) : Nat :=
  if inline.startsWith "SHA256" then 4 else 8

/-- The first word at which two byte strings differ, as `word i: tracer 0x.., spec 0x..`,
reading each word little-endian as the inline stores it. -/
def firstDifference (inline : String) (tracer spec : ByteArray) : String :=
  let n := wordSize inline
  let words := (max tracer.size spec.size + n - 1) / n
  match (List.range words).find? (fun i => leNat tracer (n * i) n ≠ leNat spec (n * i) n) with
  | some i =>
    let hex (v : Nat) := "0x" ++ toHex ⟨(leBytes v n).reverse.toArray⟩
    s!"word {i}: tracer {hex (leNat tracer (n * i) n)}, spec {hex (leNat spec (n * i) n)}"
  | none => s!"sizes differ: tracer {tracer.size} bytes, spec {spec.size} bytes"

/-- One case of the JSON file. -/
structure Case where
  inline : String
  name : String
  group : String
  judged : Bool
  rs1Before : ByteArray
  rs2Before : ByteArray
  rs1After : ByteArray
  rs2After : ByteArray
  rows : Nat
  registersPreserved : Bool
  expected : Option (ByteArray × String)

/-- Read a hexadecimal field. -/
def hexField (j : Json) (key : String) : Except String ByteArray := do
  let s ← j.getObjValAs? String key
  match ofHex? s with
  | some b => pure b
  | none => throw s!"field {key} is not hexadecimal"

/-- Read one case. -/
def Case.ofJson (j : Json) : Except String Case := do
  let expected ← match j.getObjVal? "expected_rs1_after_prefix" with
    | .ok _ => do
      let bytes ← hexField j "expected_rs1_after_prefix"
      let source ← j.getObjValAs? String "expected_source"
      pure (some (bytes, source))
    | .error _ => pure none
  return {
    inline := ← j.getObjValAs? String "inline"
    name := ← j.getObjValAs? String "name"
    group := ← j.getObjValAs? String "group"
    judged := ← j.getObjValAs? Bool "judged"
    rs1Before := ← hexField j "rs1_before"
    rs2Before := ← hexField j "rs2_before"
    rs1After := ← hexField j "rs1_after"
    rs2After := ← hexField j "rs2_after"
    rows := ← j.getObjValAs? Nat "rows"
    registersPreserved := ← j.getObjValAs? Bool "registers_preserved"
    expected
  }

/-- The specification's result at `rs1` for a judged case, or why there is none. -/
def specResult (c : Case) : Except String ByteArray :=
  match c.inline with
  | "SHA256" => .ok (sha256Result c.rs1Before c.rs2Before)
  | "SHA256_INIT" => .ok (sha256InitResult c.rs2Before)
  | "KECCAK256" => .ok (keccak256Result c.rs1Before)
  | "KECCAK256_ABSORB_PERMUTE" => .ok (keccak256AbsorbResult c.rs1Before c.rs2Before)
  | "BLAKE2" =>
    match blake2Flag c.rs2Before with
    | 0 => .ok (blake2Result c.rs1Before c.rs2Before false)
    | 1 => .ok (blake2Result c.rs1Before c.rs2Before true)
    | f => .error s!"final-block flag {f} is outside the specification"
  | other => .error s!"unknown inline {other}"

/-- Whether `pre` is a prefix of `bytes`. -/
def isPrefix (pre bytes : ByteArray) : Bool :=
  pre.size ≤ bytes.size && (List.range pre.size).all fun i => pre[i]! == bytes[i]!

/-- The failed checks of a judged case; empty when it passes. -/
def failures (c : Case) : List String := Id.run do
  let mut out := []
  match specResult c with
  | .error e => out := out ++ [e]
  | .ok spec =>
    if spec.data != c.rs1After.data then
      out := out ++ [s!"rs1 differs from the specification at {firstDifference c.inline c.rs1After spec}"]
  if c.rs2After.data != c.rs2Before.data then
    out := out ++ ["the bytes at rs2 changed"]
  if let some (pre, source) := c.expected then
    if !isPrefix pre c.rs1After then
      out := out ++ [s!"rs1 does not start with the published answer ({source})"]
  if !c.registersPreserved then
    out := out ++ ["a register among x1 to x31 changed"]
  return out

/-- A description of an informational BLAKE2 case: which computations the tracer's result
matches. -/
def describeInformational (c : Case) : String :=
  if c.inline != "BLAKE2" then "not judged" else
  let h := blake2Words 8 c.rs1Before 0
  let m := blake2Words 16 c.rs2Before 0
  let t := BitVec.ofNat 128 (blake2Counter c.rs2Before)
  let f := blake2Flag c.rs2Before
  let same (r : ByteArray) := r.data == c.rs1After.data
  let asFinal := same (blake2Result c.rs1Before c.rs2Before true)
  let asNotFinal := same (blake2Result c.rs1Before c.rs2Before false)
  let asMask := same (blake2Bytes (blake2WithMask h m t (0 - BitVec.ofNat 64 f)))
  s!"flag {f}: equals spec with f = true: {asFinal}; with f = false: {asNotFinal}; " ++
    s!"with word 14 XORed by 0 - flag: {asMask}"

/-- Whether the specification covers the case: everything but a `BLAKE2` case whose
final-block flag is outside {0, 1}. -/
def isJudged (c : Case) : Bool :=
  c.inline != "BLAKE2" || blake2Flag c.rs2Before ≤ 1

/-- The failures of a case against its manifest entry. -/
def manifestFailures (k : KnownCase) (c : Case) : List String :=
  let input (what : String) (want : Option ByteArray) (have_ : ByteArray) : List String :=
    match want with
    | some b => if b.data == have_.data then [] else [s!"{what} is not the known-answer input"]
    | none => []
  input "rs1" k.rs1 c.rs1Before ++ input "rs2" k.rs2 c.rs2Before ++
  (match c.expected with
    | none => [s!"the published answer ({k.source}) is missing"]
    | some (b, _) =>
      if b.data == k.answer.data then [] else [s!"the recorded answer is not the published one"]) ++
  (if isPrefix k.answer c.rs1After then [] else
    [s!"rs1 does not start with the published answer ({k.source})"])

/-- Per-inline counts. -/
structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  info : Nat := 0
  rows : List Nat := []
  names : List String := []

end JoltTests.InlineKat.Main

open JoltTests.InlineKat.Main in
/-- Check a corpus; the result is the exit status. -/
def checkCorpus (expectedCommit text : String) : IO UInt32 := do
  let mut corpus : List String := []
  let .ok json := Json.parse text
    | IO.println "FAIL corpus | the file is not JSON"; return 1
  match json.getObjValAs? String "format" with
  | .ok "jolt-qed inline-kat v1" => pure ()
  | _ => corpus := corpus ++ ["the format is not \"jolt-qed inline-kat v1\""]
  let commit := (json.getObjValAs? String "jolt_commit").toOption.getD "missing"
  IO.println s!"inline-kat: cases from Jolt commit {commit}"
  if commit != expectedCommit then
    corpus := corpus ++ [s!"the cases come from Jolt commit {commit}, not {expectedCommit}"]
  let mut sequenceRows : List (String × Nat) := []
  for i in (json.getObjValAs? (Array Json) "inlines").toOption.getD #[] do
    match i.getObjValAs? String "name", i.getObjValAs? Nat "sequence_rows" with
    | .ok name, .ok rows => sequenceRows := sequenceRows ++ [(name, rows)]
    | _, _ => corpus := corpus ++ ["an entry of the inline table lacks its name or row count"]
  let names := sequenceRows.map (·.1)
  let required := requiredInlines.map (·.1)
  if names.length != required.length || required.any (· ∉ names) then
    corpus := corpus ++ [s!"the inline table lists {names}, not {required}"]
  let cases := (json.getObjValAs? (Array Json) "cases").toOption.getD #[]
  let mut tallies : List (String × Tally) := required.map fun n => (n, {})
  let mut seen : List (String × String) := []
  let mut anyFailure := false
  for j in cases do
    let parsed := Case.ofJson j
    if let .error e := parsed then
      anyFailure := true
      IO.println s!"FAIL ? | a case cannot be read: {e}"
    let .ok c := parsed | continue
    let mut tally := (tallies.lookup c.inline).getD {}
    if c.rows ∉ tally.rows then
      tally := { tally with rows := tally.rows ++ [c.rows] }
    let mut fs : List String := []
    if c.name ∈ tally.names then
      fs := fs ++ ["another case of this inline has the same name"]
    tally := { tally with names := tally.names ++ [c.name] }
    match sequenceRows.lookup c.inline with
    | some n => if c.rows != n then fs := fs ++ [s!"{c.rows} rows ran, the expansion has {n}"]
    | none => fs := fs ++ ["the inline is not in the inline table"]
    if let some k := manifest.find? (fun k => k.inline == c.inline && k.name == c.name) then
      fs := fs ++ manifestFailures k c
      seen := seen ++ [(c.inline, c.name)]
    let judged := isJudged c
    if c.judged != judged then
      fs := fs ++ [if judged then
        "the corpus marks the case as not judged, but the specification covers it"
      else "the corpus marks the case as judged, but its final-block flag is outside {0, 1}"]
    if judged then fs := fs ++ failures c
    match fs, judged with
    | [], true =>
      IO.println s!"PASS {c.inline} | {c.name}"
      tally := { tally with pass := tally.pass + 1 }
    | [], false =>
      IO.println s!"INFO {c.inline} | {c.name} | {describeInformational c}"
      tally := { tally with info := tally.info + 1 }
    | _, _ =>
      anyFailure := true
      IO.println s!"FAIL {c.inline} | {c.name} | {"; ".intercalate fs}"
      tally := { tally with fail := tally.fail + 1 }
    tallies := (tallies.filter (·.1 != c.inline)) ++ [(c.inline, tally)]
  for k in manifest do
    if (k.inline, k.name) ∉ seen then
      corpus := corpus ++ [s!"the known-answer case {k.inline} | {k.name} is missing"]
  IO.println "inline-kat: summary"
  for (name, minimum) in requiredInlines do
    let t := (tallies.lookup name).getD {}
    let seqRows := (sequenceRows.lookup name).map toString |>.getD "unknown"
    IO.println s!"  {name}: {t.pass} passed, {t.fail} failed, {t.info} informational; \
      rows per call {t.rows} (expansion length {seqRows})"
    if t.pass + t.fail < minimum then
      corpus := corpus ++ [s!"{name} has {t.pass + t.fail} judged cases, fewer than {minimum}"]
  for (name, _) in tallies do
    if name ∉ required then
      corpus := corpus ++ [s!"the cases name an unknown inline {name}"]
  for e in corpus do
    IO.println s!"FAIL corpus | {e}"
  return if anyFailure || !corpus.isEmpty then 1 else 0

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lake exe inline-kat [--jolt-commit SHA] CASES.json"
  let (commit, path) ← match args with
    | ["--jolt-commit", sha, path] => pure (sha, path)
    | [path] => pure (JoltTests.InlineKat.defaultJoltCommit, path)
    | _ => IO.eprintln usage; return 2
  checkCorpus commit (← IO.FS.readFile path)
