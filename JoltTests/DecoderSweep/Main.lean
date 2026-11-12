import JoltBytecode.Decode.Jolt
import JoltTests.ExpansionParity.Source
import JoltTests.ExpansionParity.Report
import JoltTests.ExpansionParity.Row

/-!
# decoder-sweep: the T2 comparator

The Rust driver `scripts/expansion-parity/src/bin/decoder-sweep.rs` writes what
Jolt's program-image decoder does with every 16-bit parcel and with a sweep of
32-bit words (`scripts/expansion-parity/DECODER-SWEEP.md`).
This module runs Lean's `Decode.joltUncompress` and `Decode.joltDecode`
(`JoltBytecode/Decode/Jolt.lean`) on the same inputs and compares.

Usage (from the repository root, after `lake build JoltTests.DecoderSweep.Main`):

```
DECODER_SWEEP_ARGS="compare OUT_DIR REPORT_DIR" lake env lean JoltTests/DecoderSweep/Run.lean
DECODER_SWEEP_ARGS="mutation OUT_DIR" lake env lean JoltTests/DecoderSweep/Run.lean
```

`OUT_DIR` holds the driver's `decoder_parcels.tsv` and `decoder_words.tsv`.
`compare` writes `REPORT_DIR/decoder-mismatches.tsv` (one line per disagreeing
input) and `REPORT_DIR/decoder-summary.txt` (counts by class and by cause).

## What agreement means

`ImageDecoded` (`JoltConstraints/WholeRun/Decoded.lean`) assumes that every
RISC-V row of the committed bytecode is `joltDecode w advice` of the image's word
`w`, or of `joltUncompress h` for a compressed parcel `h`.
For each input the comparator classifies the pair (Jolt result, Lean result):

* both reject: Jolt returns an error and `joltDecode` returns `none`;
* both accept: Jolt returns a source instruction, T1's `SourceView.toLean` maps it
  to `.riscv j`, and `joltDecode w 0` is `some i` with `i` equal to `j` once the
  fields Jolt's record does not carry are settled: the division advice of `i` is
  set to 0, and the atomic `aq`/`rl` bits of `j` are taken from the word's bits
  26 and 25;
* Jolt-only kind: Jolt accepts with a Jolt-specific kind (`toLean` maps it to a
  `.jolt` source instruction, such as the advice loads, or the kind is in T1's
  list `noLeanSourceKinds`, or it is `Inline`), and `joltDecode` returns `none`;
  Lean's decoder covers standard RISC-V only, and `ImageDecoded` constrains only
  `.riscv` rows;
* rejected by Jolt's expansion: Jolt's decoder accepts a Zicsr instruction whose
  CSR address is not one of the six Jolt supports, Jolt's expansion rejects it
  (`rejectedAtExpansion`), and `joltDecode` returns `none`; the two pipelines
  reject the word at different stages;
* otherwise a mismatch, with its cause.

For a parcel the comparator first compares the two uncompressed words, then the
decode of the uncompressed word (Jolt decodes it with `is_compressed = true`).
-/

open Lean LeanRV64D ExpansionParity

namespace DecoderSweep

deriving instance BEq for JoltISA.SystemCSR
deriving instance BEq for RiscvInstruction

/-- Set the division and remainder advice to 0. `ImageDecoded` quantifies the
advice existentially and the encoding does not carry it, so the comparison
fixes it on the Lean side. -/
def eraseAdvice : RiscvInstruction → RiscvInstruction
  | .DIV d a b _ => .DIV d a b 0
  | .DIVU d a b _ => .DIVU d a b 0
  | .REM d a b _ => .REM d a b 0
  | .REMU d a b _ => .REMU d a b 0
  | .DIVW d a b _ => .DIVW d a b 0
  | .DIVUW d a b _ => .DIVUW d a b 0
  | .REMW d a b _ => .REMW d a b 0
  | .REMUW d a b _ => .REMUW d a b 0
  | i => i

/-- Set the atomic ordering bits of an atomic instruction. Jolt's source record
does not carry them, and `SourceView.toLean` sets both to false; the comparison
takes the expected values from the word itself (`aq` is bit 26 and `rl` is
bit 25 in the RISC-V A extension), so a decoder that drops or swaps them is
reported. -/
def withOrdering (aq rl : Bool) : RiscvInstruction → RiscvInstruction
  | .LR_W d a _ _ => .LR_W d a aq rl
  | .LR_D d a _ _ => .LR_D d a aq rl
  | .SC_W d a b _ _ => .SC_W d a b aq rl
  | .SC_D d a b _ _ => .SC_D d a b aq rl
  | .AMOSWAP_W d a b _ _ => .AMOSWAP_W d a b aq rl
  | .AMOSWAP_D d a b _ _ => .AMOSWAP_D d a b aq rl
  | .AMOADD_W d a b _ _ => .AMOADD_W d a b aq rl
  | .AMOADD_D d a b _ _ => .AMOADD_D d a b aq rl
  | .AMOAND_W d a b _ _ => .AMOAND_W d a b aq rl
  | .AMOAND_D d a b _ _ => .AMOAND_D d a b aq rl
  | .AMOOR_W d a b _ _ => .AMOOR_W d a b aq rl
  | .AMOOR_D d a b _ _ => .AMOOR_D d a b aq rl
  | .AMOXOR_W d a b _ _ => .AMOXOR_W d a b aq rl
  | .AMOXOR_D d a b _ _ => .AMOXOR_D d a b aq rl
  | .AMOMIN_W d a b _ _ => .AMOMIN_W d a b aq rl
  | .AMOMIN_D d a b _ _ => .AMOMIN_D d a b aq rl
  | .AMOMAX_W d a b _ _ => .AMOMAX_W d a b aq rl
  | .AMOMAX_D d a b _ _ => .AMOMAX_D d a b aq rl
  | .AMOMINU_W d a b _ _ => .AMOMINU_W d a b aq rl
  | .AMOMINU_D d a b _ _ => .AMOMINU_D d a b aq rl
  | .AMOMAXU_W d a b _ _ => .AMOMAXU_W d a b aq rl
  | .AMOMAXU_D d a b _ _ => .AMOMAXU_D d a b aq rl
  | i => i

/-- The constructor name of a Lean instruction, for reports. -/
def ctorName (i : RiscvInstruction) : String :=
  ((toString (repr i)).splitOn " ").headD "?" |>.replace "RiscvInstruction." ""

/-- Jolt's decode result, as the driver writes it. -/
inductive JoltResult where
  | err (message : String)
  | ok (view : SourceView)

def parseReg (s : String) : Except String (Option Nat) :=
  if s == "-" then pure none
  else match s.toNat? with
    | some n => pure (some n)
    | none => throw s!"bad register field {s}"

/-- Parse the result columns `E msg` or `K kind rd rs1 rs2 imm`. -/
def parseResult (cols : List String) (compressed : Bool) : Except String JoltResult :=
  match cols with
  | "E" :: rest => pure (.err (" ".intercalate rest))
  | ["K", kind, rd, rs1, rs2, imm] => do
      let imm ← intOfString "imm" imm
      pure (.ok { kind, address := 0x80000000, rd := ← parseReg rd, rs1 := ← parseReg rs1,
                  rs2 := ← parseReg rs2, imm, compressed, inlineName := none })
  | _ => throw s!"bad result columns {cols}"

def parseHex (s : String) : Except String Nat :=
  s.foldl (fun acc c => do
    let a ← acc
    let d ← if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else throw s!"bad hex digit in {s}"
    pure (16 * a + d)) (pure 0)

/-- The outcome of comparing one decode. -/
inductive Outcome where
  | bothReject
  | bothAccept (kind : String)
  | joltOnly (kind : String)
  | expansionRejects (kind : String)
  | mismatch (cause : String) (detail : String)

def hex32 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (8 - s.length) ++ s

def jsonOf (r : JoltResult) : String :=
  match r with
  | .err m => s!"Jolt error ({m})"
  | .ok v => s!"Jolt {v.kind} rd={showOpt v.rd} rs1={showOpt v.rs1} rs2={showOpt v.rs2} imm={v.imm}"

/-- Source kinds that only Jolt's decoder produces, besides T1's
`noLeanSourceKinds`: `Inline`, which `decode_instruction` returns for the custom
opcodes 0x0b and 0x2b. The model handles inline sequences through the inline
templates, not through `joltDecode`. -/
def joltOnlyDecodeKinds : List String := ["Inline"]

/-- The Zicsr kinds, whose CSR address Jolt checks at expansion, not at decode. -/
def csrKinds : List String := ["CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"]

/-- Jolt's decoder accepts a Zicsr instruction with any CSR address
(`decode_system` in `crates/jolt-program/src/image/decode.rs`). Jolt's expansion
reads the address as `imm & 0xfff` (`csr_address` in
`crates/jolt-program/src/expand/operands.rs`) and rejects it with
`ExpansionError::UnsupportedCsr` unless it is one of the six that
`virtual_register_for_csr` maps (`crates/jolt-program/src/expand/allocator.rs`).
Lean's `joltDecode` makes the same six-address check at decode.
This recognizes a record for word `w` that Jolt's expansion rejects for that
reason: its kind is a Zicsr kind, its immediate is a sign-extended 12-bit value
whose low 12 bits are the word's bits 31..20, that address is not one of the six,
and the same record at address 0x300 (mstatus) maps to a Lean RISC-V
instruction, so the address is its only obstacle. -/
def rejectedAtExpansion (w : BitVec 32) (v : SourceView) : Bool :=
  let address := (v.imm % 4096).toNat
  csrKinds.contains v.kind && (sext v.kind 12 v.imm matches .ok _) &&
    address == (w.extractLsb 31 20).toNat &&
    !(systemCSRs.any (·.address.toNat == address)) &&
    ({ v with imm := 0x300 }.toLean matches .ok (.riscv _))

/-- Compare Jolt's result for word `w` with Lean's decode `lean` of it. -/
def compareWith (w : BitVec 32) (lean : Option RiscvInstruction) (jolt : JoltResult) : Outcome :=
  match jolt, lean with
  | .err _, none => .bothReject
  | .err m, some i =>
      .mismatch s!"Lean accepts {ctorName i}, Jolt rejects ({m})" (reprStr i)
  | .ok v, none =>
      match v.toLean with
      | .ok (.jolt _) => .joltOnly v.kind
      | .error (.kind k) =>
          if noLeanSourceKinds.contains k || joltOnlyDecodeKinds.contains k then .joltOnly k
          else .mismatch s!"Jolt accepts unknown kind {k}, Lean rejects" (jsonOf jolt)
      | _ =>
        if rejectedAtExpansion w v then .expansionRejects v.kind
        else .mismatch s!"Jolt accepts {v.kind}, Lean rejects" (jsonOf jolt)
  | .ok v, some i =>
      match v.toLean with
      | .ok (.riscv j) =>
          let expected := withOrdering (w.getLsbD 26) (w.getLsbD 25) j
          if eraseAdvice i == expected then .bothAccept v.kind
          else .mismatch s!"both accept {v.kind}, operands differ"
            s!"{jsonOf jolt}; expected {reprStr expected}; Lean {reprStr i}"
      | .ok (.jolt _) => .mismatch s!"Jolt gives custom {v.kind}, Lean gives {ctorName i}" (reprStr i)
      | .error e => .mismatch s!"Jolt {v.kind} has no Lean source form ({e.describe}), Lean gives {ctorName i}"
          (reprStr i)

/-- Compare Jolt's result for word `w` with `joltDecode w 0`. -/
def compareDecode (w : BitVec 32) (jolt : JoltResult) : Outcome :=
  compareWith w (Decode.joltDecode w 0) jolt

structure Tally where
  inputs : Nat := 0
  bothReject : Nat := 0
  bothAccept : Nat := 0
  joltOnly : Nat := 0
  expansionRejects : Nat := 0
  mismatches : Nat := 0
  acceptKinds : Std.HashMap String Nat := {}
  joltOnlyKinds : Std.HashMap String Nat := {}
  expansionRejectKinds : Std.HashMap String Nat := {}
  causes : Std.HashMap String Nat := {}
  examples : Std.HashMap String String := {}

def Tally.add (t : Tally) (input : String) (o : Outcome) : Tally :=
  let t := { t with inputs := t.inputs + 1 }
  match o with
  | .bothReject => { t with bothReject := t.bothReject + 1 }
  | .bothAccept k => { t with bothAccept := t.bothAccept + 1, acceptKinds := bump t.acceptKinds k }
  | .joltOnly k => { t with joltOnly := t.joltOnly + 1, joltOnlyKinds := bump t.joltOnlyKinds k }
  | .expansionRejects k =>
      { t with expansionRejects := t.expansionRejects + 1,
               expansionRejectKinds := bump t.expansionRejectKinds k }
  | .mismatch c d =>
      { t with mismatches := t.mismatches + 1, causes := bump t.causes c,
               examples := if t.examples.contains c then t.examples
                 else t.examples.insert c s!"{input}: {d}" }

def Tally.render (title : String) (t : Tally) : String := Id.run do
  let mut s := s!"{title}: {t.inputs} inputs, {t.bothReject} both reject, " ++
    s!"{t.bothAccept} both accept, {t.joltOnly} Jolt-only kind, " ++
    s!"{t.expansionRejects} rejected by Jolt's expansion (unsupported CSR), {t.mismatches} mismatches\n"
  s := s ++ s!"  accepted kinds: {t.acceptKinds.size}\n"
  if t.expansionRejects > 0 then
    s := s ++ s!"  rejected by Jolt's expansion: {renderCounts t.expansionRejectKinds}\n"
  if t.joltOnly > 0 then
    s := s ++ s!"  Jolt-only kinds: {renderCounts t.joltOnlyKinds}\n"
  let causes := t.causes.toList.toArray.qsort (fun a b => a.1 < b.1)
  for (c, n) in causes do
    s := s ++ s!"  mismatch x{n}: {c}\n    first: {t.examples.getD c ""}\n"
  return s

/-- One parsed line of `decoder_words.tsv`. -/
def parseWordLine (line : String) : Except String (Nat × JoltResult) := do
  match line.splitOn "\t" with
  | w :: rest => pure (← parseHex w, ← parseResult rest false)
  | [] => throw "empty line"

/-- One parsed line of `decoder_parcels.tsv`. -/
def parseParcelLine (line : String) : Except String (Nat × Nat × JoltResult) := do
  match line.splitOn "\t" with
  | h :: w :: rest => pure (← parseHex h, ← parseHex w, ← parseResult rest true)
  | _ => throw s!"bad parcel line {line}"

/-- Compare one parcel: the uncompressed word, then its decode. -/
def compareParcel (h w : Nat) (jolt : JoltResult) : Outcome × Option String :=
  let lw := (Decode.joltUncompress (BitVec.ofNat 16 h)).toNat
  if lw != w then
    (.mismatch "uncompressed words differ" s!"Jolt {hex32 w}, Lean {hex32 lw}", some "uncompress")
  else (compareDecode (BitVec.ofNat 32 w) jolt, none)

def opcodeClass (w : Nat) : String := s!"opcode 0x{String.ofList (Nat.toDigits 16 (w % 128))}"

def runCompare (outDir reportDir : String) : IO UInt32 := do
  IO.FS.createDirAll reportDir
  let mut mism : Array String := #[]
  -- Parcels.
  let mut parcelT : Tally := {}
  let mut quadrant3T : Tally := {}
  let mut uncompressSame := 0
  for line in ← readLines s!"{outDir}/decoder_parcels.tsv" do
    let (h, w, jolt) ← IO.ofExcept (parseParcelLine line)
    let (o, _) := compareParcel h w jolt
    let input := s!"parcel {(hex32 h).drop 4} (word {hex32 w})"
    if let .mismatch c d := o then mism := mism.push s!"{input}\t{c}\t{d}"
    else uncompressSame := uncompressSame + 1
    if h % 4 == 3 then quadrant3T := quadrant3T.add input o
    else parcelT := parcelT.add input o
  -- Words, tallied overall and per opcode class.
  let mut wordT : Tally := {}
  let mut perClass : Std.HashMap String Tally := {}
  for line in ← readLines s!"{outDir}/decoder_words.tsv" do
    let (w, jolt) ← IO.ofExcept (parseWordLine line)
    let o := compareDecode (BitVec.ofNat 32 w) jolt
    let input := s!"word {hex32 w}"
    if let .mismatch c d := o then mism := mism.push s!"{input}\t{c}\t{d}"
    wordT := wordT.add input o
    let k := opcodeClass w
    perClass := perClass.insert k ((perClass.getD k {}).add input o)
  IO.FS.writeFile s!"{reportDir}/decoder-mismatches.tsv"
    ("\n".intercalate mism.toList ++ (if mism.isEmpty then "" else "\n"))
  let mut s := parcelT.render "compressed parcels (low bits != 0b11)"
  s := s ++ quadrant3T.render "parcels with low bits 0b11 (not compressed; compared for completeness)"
  s := s ++ wordT.render "32-bit words"
  let classes := perClass.toList.toArray.qsort (fun a b => a.1 < b.1)
  s := s ++ "per opcode class:\n"
  for (k, t) in classes do
    s := s ++ s!"  {k}: {t.inputs} words, {t.bothReject} both reject, {t.bothAccept} both accept, " ++
      s!"{t.joltOnly} Jolt-only kind, {t.expansionRejects} rejected by Jolt's expansion, " ++
      s!"{t.mismatches} mismatches\n"
  IO.FS.writeFile s!"{reportDir}/decoder-summary.txt" s
  IO.println s
  let bad := parcelT.mismatches + quadrant3T.mismatches + wordT.mismatches
  IO.println s!"decoder-sweep: {bad} mismatches; details in {reportDir}/decoder-mismatches.tsv"
  return if bad == 0 then 0 else 1

/-- Corrupt inputs in memory and check that each corruption is reported. -/
def runMutation (outDir : String) : IO UInt32 := do
  -- Stream the words until one example of each needed shape is found.
  let h ← IO.FS.Handle.mk s!"{outDir}/decoder_words.tsv" .read
  let mut firstAccept : Option (Nat × SourceView) := none
  let mut firstReject : Option Nat := none
  let mut firstCsr : Option (Nat × SourceView) := none
  let mut firstLater : Option (Nat × SourceView) := none
  let mut firstAmo : Option (Nat × SourceView) := none
  repeat
    let line := (← h.getLine).trimAsciiEnd.toString
    if line.isEmpty then break
    let (w, r) ← IO.ofExcept (parseWordLine line)
    match r with
    | .ok v =>
        let std := (v.toLean matches .ok (.riscv _)) && v.rd.isSome
        if firstAccept.isNone && std then firstAccept := some (w, v)
        if firstCsr.isNone && std && v.kind == "CSRRW" then firstCsr := some (w, v)
        if firstLater.isNone && rejectedAtExpansion (BitVec.ofNat 32 w) v then
          firstLater := some (w, v)
        if firstAmo.isNone && std && v.kind.startsWith "AMO" then firstAmo := some (w, v)
    | .err _ => if firstReject.isNone then firstReject := some w
    if firstAccept.isSome && firstReject.isSome && firstCsr.isSome && firstLater.isSome &&
        firstAmo.isSome then break
  let some (aw, av) := firstAccept | throw <| IO.userError "no accepted standard word"
  let some rw := firstReject | throw <| IO.userError "no rejected word"
  let some (cw, cv) := firstCsr | throw <| IO.userError "no accepted CSRRW word"
  let some (lw, lv) := firstLater | throw <| IO.userError "no word rejected at expansion"
  let some (mw, mv) := firstAmo | throw <| IO.userError "no accepted AMO word"
  let mword := BitVec.ofNat 32 mw
  let some mlean := Decode.joltDecode mword 0 | throw <| IO.userError "Lean rejects the AMO word"
  let lAddress := (lw / 2 ^ 20) % 4096
  let detected (o : Outcome) : Bool := o matches .mismatch _ _
  let cases : List (String × Bool) :=
    [ ("rd changed", detected (compareDecode (BitVec.ofNat 32 aw)
        (.ok { av with rd := av.rd.map (fun r => (r + 1) % 32) }))),
      ("immediate changed", detected (compareDecode (BitVec.ofNat 32 aw)
        (.ok { av with imm := av.imm + 4096 * 2 ^ 20 + 2 }))),
      ("kind changed", detected (compareDecode (BitVec.ofNat 32 aw)
        (.ok { av with kind := if av.kind == "ADD" then "SUB" else "ADD",
                       rs2 := av.rs2.orElse (fun _ => some 0) }))),
      ("accepted turned into error", detected (compareDecode (BitVec.ofNat 32 aw) (.err "mutated"))),
      ("error turned into ADDI", detected (compareDecode (BitVec.ofNat 32 rw)
        (.ok { kind := "ADDI", address := 0x80000000, rd := some 1, rs1 := some 1, rs2 := none,
               imm := 1, compressed := false, inlineName := none }))),
      ("supported CSR address changed to an unsupported one", detected (compareDecode
        (BitVec.ofNat 32 cw) (.ok { cv with imm := 0x301 }))),
      ("unsupported CSR address changed to mstatus", detected (compareDecode
        (BitVec.ofNat 32 lw) (.ok { lv with imm := 0x300 }))),
      ("CSR immediate not a 12-bit value", detected (compareDecode
        (BitVec.ofNat 32 lw) (.ok { lv with imm := lv.imm + 0x1000 }))),
      ("CSR address differs from the word's", detected (compareDecode
        (BitVec.ofNat 32 lw) (.ok { lv with imm := if lAddress == 0x301 then 0x302 else 0x301 }))),
      ("Lean's aq bit flipped", detected (compareWith mword
        (some (withOrdering (!mword.getLsbD 26) (mword.getLsbD 25) mlean)) (.ok mv))),
      ("Lean's rl bit flipped", detected (compareWith mword
        (some (withOrdering (mword.getLsbD 26) (!mword.getLsbD 25) mlean)) (.ok mv))) ]
  let parcels ← readLines s!"{outDir}/decoder_parcels.tsv"
  let (ph, pw, pr) ← IO.ofExcept (parseParcelLine (parcels[1]!))
  let cases := cases ++
    [("uncompressed word changed", detected (compareParcel ph (pw ^^^ 0x80) pr).1)]
  let mut ok := true
  for (name, d) in cases do
    IO.println s!"  {name}: {if d then "detected" else "MISSED"}"
    ok := ok && d
  IO.println (if ok then "mutation check: every corruption detected" else "mutation check: FAILED")
  return if ok then 0 else 1

/-- The command line, called by `Run.lean` (see `JoltTests/ExpansionParity/Main.lean`
for why there is no executable). -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["compare", out, report] => runCompare out report
  | ["mutation", out] => runMutation out
  | _ =>
    IO.eprintln "usage: DECODER_SWEEP_ARGS='compare OUT_DIR REPORT_DIR | mutation OUT_DIR'"
    return 2

end DecoderSweep
