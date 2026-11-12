import JoltTests.ExpansionParity.Source

/-!
# Record-level comparisons

`compareT1` takes one non-inline record of the driver's `rows.jsonl`, maps its
source to Lean, runs `expand_instruction` (`JoltConstraints/program.lean`, which
calls `SourceInstruction.expand` and `stamp_sequence`) and compares every row.
-/

open Lean LeanRV64D

namespace ExpansionParity

/-- One disagreement. `cause` groups disagreements that one explanation covers. -/
structure Mismatch where
  check : String
  case : String
  group : String
  allocator : String
  sourceKind : String
  row : Option Nat
  field : String
  rust : String
  lean : String
  cause : String

def Mismatch.toJson (m : Mismatch) : Json :=
  Json.mkObj
    [ ("check", m.check), ("case", m.case), ("group", m.group), ("allocator", m.allocator),
      ("source_kind", m.sourceKind),
      ("row", match m.row with | some r => Json.num (r : Int) | none => Json.null),
      ("field", m.field), ("rust", m.rust), ("lean", m.lean), ("cause", m.cause) ]

/-- The record's identifying fields. -/
structure RecordInfo where
  case : String
  group : String
  allocator : String
  source : SourceView
  /-- `none` when Rust returned an error; the error string is in `error`. -/
  rows : Option (List RowView)
  error : Option String

def RecordInfo.ofJson (j : Json) : Except String RecordInfo := do
  let result ← getField j "result"
  let rows ← match result.getObjVal? "rows" with
    | .ok arr => some <$> ((← arr.getArr?).toList.mapM RowView.ofRustJson)
    | .error _ => pure none
  let error := match result.getObjVal? "error" with
    | .ok e => e.getStr?.toOption
    | .error _ => none
  pure
    { case := ← (← getField j "case").getStr?
      group := ← (← getField j "group").getStr?
      allocator := ← (← getField j "allocator").getStr?
      source := ← SourceView.ofJson (← getField j "source")
      rows, error }

def RecordInfo.mismatch (r : RecordInfo) (check : String) (row : Option Nat)
    (field rust lean cause : String) : Mismatch :=
  { check, case := r.case, group := r.group, allocator := r.allocator,
    sourceKind := r.source.kind, row, field, rust, lean, cause }

/-- Compares two row lists position by position, and their lengths. -/
def compareRowLists (r : RecordInfo) (check : String) (rust lean : List RowView) :
    List Mismatch := Id.run do
  let mut out : Array Mismatch := #[]
  if rust.length != lean.length then
    out := out.push <| r.mismatch check none "row_count" (toString rust.length)
      (toString lean.length) s!"row count of {r.source.kind}"
  for (i, (rr, lr)) in (List.range (min rust.length lean.length)).zip (rust.zip lean) do
    for d in compareRows rr lr do
      let cause :=
        if d.field == "kind" then s!"kind: Rust {rr.kind}, Lean {lr.kind}"
        else s!"{d.field} of {rr.kind} rows (Rust {d.rust}, Lean {d.lean})"
      -- Field values that vary per row (registers, immediates) would split one
      -- cause into many groups; keep the kind and field only for those.
      let cause :=
        if d.field ∈ ["rd", "rs1", "rs2", "imm", "address", "vsr"] then
          s!"{d.field} of {rr.kind} rows"
        else cause
      out := out.push <| r.mismatch check (some i) d.field d.rust d.lean cause
  return out.toList

/-- The outcome of one T1 record. -/
inductive T1Outcome where
  /-- An `Inline` record: compared by the inline round trip instead. -/
  | inline
  /-- Rust rejects the source and Lean rejects it too, in the way described. -/
  | bothReject (how : String)
  /-- Rows compared; the list holds every disagreement (empty when they agree). -/
  | compared (mismatches : List Mismatch)
  /-- Lean has no source constructor for the Rust kind, so the expansion cannot
  be compared. Each Rust row's flags, table and RAF bit are compared with
  `metadata.lean` for the row's kind and stamp instead
  (`RowView.leanMetadataOf`); the list holds every disagreement. -/
  | metadataOnly (mismatches : List Mismatch)

def leanRowsOf (src : SourceInstruction) (s : SourceView) : Option (List JoltInstructionRow) :=
  expand_instruction
    { address := BitVec.ofNat 64 s.address, instruction := src, is_compressed := s.compressed }

/-- Compares each Rust row's flags, table and RAF bit with `metadata.lean`. -/
def compareRowMetadata (r : RecordInfo) (rust : List RowView) : List Mismatch :=
  (List.range rust.length).zip rust |>.flatMap fun (i, rr) =>
    match rr.leanMetadataOf with
    | none =>
        [r.mismatch "t1_metadata" (some i) "kind" rr.kind "no JoltISA.Instr constructor"
          s!"no Lean row constructor for row kind {rr.kind}"]
    | some lr =>
        (compareRows rr lr).map fun d =>
          r.mismatch "t1_metadata" (some i) d.field d.rust d.lean
            s!"{d.field} of {rr.kind} rows (Rust {d.rust}, Lean {d.lean})"

def compareT1 (r : RecordInfo) : T1Outcome :=
  let s := r.source
  if s.kind == "Inline" then .inline else
  match s.toLean, r.rows with
  | .error why, none =>
      .bothReject s!"no Lean source instruction: {why.describe}"
  | .error (.kind _), some rustRows => .metadataOnly (compareRowMetadata r rustRows)
  | .error why, some _ =>
      let cause := match why with
        | .kind k => s!"gap: no Lean SourceInstruction for Rust source kind {k}"
        | .operand k _ => s!"gap: Lean {k} cannot hold Jolt's operands"
      .compared [r.mismatch "t1" none "source" "accepted" why.describe cause]
  | .ok src, none =>
      match leanRowsOf src s with
      | none => .bothReject "expand_instruction returns none"
      | some rows =>
          .compared [r.mismatch "t1" none "result" (r.error.getD "error")
            s!"{rows.length} rows" s!"Lean expands, Rust rejects: {s.kind}"]
  | .ok src, some rustRows =>
      match leanRowsOf src s with
      | none =>
          .compared [r.mismatch "t1" none "result" s!"{rustRows.length} rows"
            "expand_instruction returns none" s!"Lean rejects, Rust expands: {s.kind}"]
      | some rows => .compared (compareRowLists r "t1" rustRows (rows.map RowView.ofLeanRow))

end ExpansionParity
