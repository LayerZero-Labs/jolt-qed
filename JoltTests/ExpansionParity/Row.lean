import Lean.Data.Json.Parser
import Lean.Data.Json.Basic
import JoltConstraints.metadata

/-!
# Rows in the expansion-parity schema

The Rust driver (`scripts/expansion-parity`) writes each final Jolt row as a JSON
object with the fields `kind`, `address`, `rd`, `rs1`, `rs2`, `imm`, `vsr`,
`first`, `compressed`, `circuit_flags`, `instruction_flags`, `lookup_table` and
`raf`. This module reads such a row, renders a Lean row (`JoltInstructionRow`)
into the same shape, and compares the two field by field.

The renderer is written from the constructors of `JoltISA.Instr`
(`JoltBytecode/JoltISA/Instruction.lean`), not from the generator in
`scripts/expansion-parity/src/lean.rs`. Each constructor's destination is `rd`,
its first register source is `rs1` and its second register source is `rs2`.
Registers render in Jolt's flat numbering: `x0..x31` as `0..31` and a virtual
register as its 7-bit address. The immediate is `JoltMetadata.immediate`, the
model's statement of the row's `NormalizedOperands.imm`.
-/

open Lean LeanRV64D

namespace ExpansionParity

/-- One row in the driver's schema. Fields that a comparison does not cover are
`none` (inline templates carry no flags). -/
structure RowView where
  kind : String
  address : Nat
  rd : Option Nat
  rs1 : Option Nat
  rs2 : Option Nat
  imm : Int
  vsr : Option Nat
  first : Bool
  compressed : Bool
  circuitFlags : Option (List String) := none
  instructionFlags : Option (List String) := none
  lookupTable : Option (Option String) := none
  raf : Option Bool := none
  deriving Inhabited

/-! ## Reading the driver's JSON -/

def getField (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

def optNat (j : Json) (key : String) : Except String (Option Nat) := do
  match ← getField j key with
  | .null => pure none
  | v => some <$> v.getNat?

def intOfString (field s : String) : Except String Int :=
  match s.toInt? with
  | some i => pure i
  | none => throw s!"{field}: not a decimal integer: {s}"

def strList (j : Json) : Except String (List String) := do
  let arr ← j.getArr?
  arr.toList.mapM (·.getStr?)

/-- Reads a final row as the Rust driver writes it. -/
def RowView.ofRustJson (j : Json) : Except String RowView := do
  let lookupTable ← match ← getField j "lookup_table" with
    | .null => pure (none : Option String)
    | v => some <$> v.getStr?
  pure
    { kind := ← (← getField j "kind").getStr?
      address := ← (← getField j "address").getNat?
      rd := ← optNat j "rd"
      rs1 := ← optNat j "rs1"
      rs2 := ← optNat j "rs2"
      imm := ← intOfString "imm" (← (← getField j "imm").getStr?)
      vsr := ← optNat j "vsr"
      first := ← (← getField j "first").getBool?
      compressed := ← (← getField j "compressed").getBool?
      circuitFlags := some (← strList (← getField j "circuit_flags"))
      instructionFlags := some (← strList (← getField j "instruction_flags"))
      lookupTable := some lookupTable
      raf := some (← (← getField j "raf").getBool?) }

/-! ## Rendering Lean rows -/

def regOfSrc : JoltISA.Src → Nat
  | .xreg (regidx.Regidx b) => b.toNat
  | .vreg v => v.toNat

def regOfDst : JoltISA.Dst → Nat
  | .xreg (regidx.Regidx b) => b.toNat
  | .vreg v => v.toNat

/-- The kind name and register operands of a final row, from the constructor:
destination, first register source, second register source. -/
def operands : JoltISA.Instr → String × Option Nat × Option Nat × Option Nat
  | .ADDI d s _ => ("ADDI", some (regOfDst d), some (regOfSrc s), none)
  | .ADDIW d s _ => ("ADDIW", some (regOfDst d), some (regOfSrc s), none)
  | .ANDI d s _ => ("ANDI", some (regOfDst d), some (regOfSrc s), none)
  | .ORI d s _ => ("ORI", some (regOfDst d), some (regOfSrc s), none)
  | .XORI d s _ => ("XORI", some (regOfDst d), some (regOfSrc s), none)
  | .SLTI d s _ => ("SLTI", some (regOfDst d), some (regOfSrc s), none)
  | .SLTIU d s _ => ("SLTIU", some (regOfDst d), some (regOfSrc s), none)
  | .LUI d _ => ("LUI", some (regOfDst d), none, none)
  | .AUIPC d _ => ("AUIPC", some (regOfDst d), none, none)
  | .JAL d _ => ("JAL", some (regOfDst d), none, none)
  | .JALR d s _ => ("JALR", some (regOfDst d), some (regOfSrc s), none)
  | .BEQ a b _ => ("BEQ", none, some (regOfSrc a), some (regOfSrc b))
  | .BNE a b _ => ("BNE", none, some (regOfSrc a), some (regOfSrc b))
  | .BLT a b _ => ("BLT", none, some (regOfSrc a), some (regOfSrc b))
  | .BGE a b _ => ("BGE", none, some (regOfSrc a), some (regOfSrc b))
  | .BLTU a b _ => ("BLTU", none, some (regOfSrc a), some (regOfSrc b))
  | .BGEU a b _ => ("BGEU", none, some (regOfSrc a), some (regOfSrc b))
  | .FENCE => ("FENCE", none, none, none)
  | .ADD d a b => ("ADD", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .ADDW d a b => ("ADDW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .SUB d a b => ("SUB", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .SUBW d a b => ("SUBW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .MUL d a b => ("MUL", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .MULW d a b => ("MULW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .MULHU d a b => ("MULHU", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .ANDN d a b => ("ANDN", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualMULI d s _ => ("VirtualMULI", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualMULIW d s _ => ("VirtualMULIW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualPow2 d s _ => ("VirtualPow2", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualPow2W d s _ => ("VirtualPow2W", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualPow2I d _ => ("VirtualPow2I", some (regOfDst d), none, none)
  | .VirtualPow2IW d _ => ("VirtualPow2IW", some (regOfDst d), none, none)
  | .VirtualShiftRightBitmask d s _ =>
      ("VirtualShiftRightBitmask", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualShiftRightBitmaskI d _ => ("VirtualShiftRightBitmaskI", some (regOfDst d), none, none)
  | .VirtualShiftRightBitmaskW d s _ =>
      ("VirtualShiftRightBitmaskW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualSRLI d s _ => ("VirtualSRLI", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualSRAI d s _ => ("VirtualSRAI", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualSRLIW d s _ => ("VirtualSRLIW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualSRAIW d s _ => ("VirtualSRAIW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualSRL d a b => ("VirtualSRL", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualSRA d a b => ("VirtualSRA", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualSRLW d a b => ("VirtualSRLW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualSRAW d a b => ("VirtualSRAW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualROTRI d s _ => ("VirtualROTRI", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualROTRIW d s _ => ("VirtualROTRIW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualRev8W d s _ => ("VirtualRev8W", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualXORROT32 d a b =>
      ("VirtualXORROT32", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROT24 d a b =>
      ("VirtualXORROT24", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROT16 d a b =>
      ("VirtualXORROT16", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROT63 d a b =>
      ("VirtualXORROT63", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTL1 d a b =>
      ("VirtualXORROTL1", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW16 d a b =>
      ("VirtualXORROTW16", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW12 d a b =>
      ("VirtualXORROTW12", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW8 d a b =>
      ("VirtualXORROTW8", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW7 d a b =>
      ("VirtualXORROTW7", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW22 d a b =>
      ("VirtualXORROTW22", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW19 d a b =>
      ("VirtualXORROTW19", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualXORROTW6 d a b =>
      ("VirtualXORROTW6", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .OR d a b => ("OR", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .XOR d a b => ("XOR", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .AND d a b => ("AND", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .SLT d a b => ("SLT", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .SLTU d a b => ("SLTU", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualWindowMaskB d s _ => ("VirtualWindowMaskB", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualWindowMaskH d s _ => ("VirtualWindowMaskH", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualWindowMaskW d s _ => ("VirtualWindowMaskW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualPext d a b => ("VirtualPext", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualPextSigned d a b =>
      ("VirtualPextSigned", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualShiftDataB d a b _ =>
      ("VirtualShiftDataB", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualShiftDataH d a b _ =>
      ("VirtualShiftDataH", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualShiftDataW d a b _ =>
      ("VirtualShiftDataW", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualSignExtendWord d s _ =>
      ("VirtualSignExtendWord", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualZeroExtendWord d s _ =>
      ("VirtualZeroExtendWord", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualMovsign d s _ => ("VirtualMovsign", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualLoadB _ d s _ _ => ("VirtualLoadB", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualLoadH _ d s _ _ => ("VirtualLoadH", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualLoadW _ d s _ _ => ("VirtualLoadW", some (regOfDst d), some (regOfSrc s), none)
  | .VirtualStoreB a b _ _ => ("VirtualStoreB", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualStoreH a b _ _ => ("VirtualStoreH", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualStoreW a b _ _ => ("VirtualStoreW", none, some (regOfSrc a), some (regOfSrc b))
  | .LD _ d s _ => ("LD", some (regOfDst d), some (regOfSrc s), none)
  | .SD a b _ => ("SD", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualAdvice d _ _ => ("VirtualAdvice", some (regOfDst d), none, none)
  | .VirtualAdviceLoad d _ => ("VirtualAdviceLoad", some (regOfDst d), none, none)
  | .VirtualHostIO => ("VirtualHostIO", none, none, none)
  | .VirtualAssertEQ a b _ => ("VirtualAssertEQ", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualAssertValidDiv0 a b _ =>
      ("VirtualAssertValidDiv0", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualNegateIf d a b =>
      ("VirtualNegateIf", some (regOfDst d), some (regOfSrc a), some (regOfSrc b))
  | .VirtualAssertValidUnsignedRemainder a b _ =>
      ("VirtualAssertValidUnsignedRemainder", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualAssertMulUNoOverflow a b _ =>
      ("VirtualAssertMulUNoOverflow", none, some (regOfSrc a), some (regOfSrc b))
  | .VirtualAssertLTE a b _ => ("VirtualAssertLTE", none, some (regOfSrc a), some (regOfSrc b))

/-- Circuit flags in the order of Rust's `CIRCUIT_FLAGS`
(`crates/jolt-riscv/src/flags.rs:73-87` at the pin). -/
def circuitFlagNames : List (CircuitFlags × String) :=
  [(.AddOperands, "AddOperands"), (.SubtractOperands, "SubtractOperands"),
   (.MultiplyOperands, "MultiplyOperands"), (.Load, "Load"), (.Store, "Store"),
   (.Jump, "Jump"), (.WriteLookupOutputToRD, "WriteLookupOutputToRD"),
   (.VirtualInstruction, "VirtualInstruction"), (.Assert, "Assert"),
   (.DoNotUpdateUnexpandedPC, "DoNotUpdateUnexpandedPC"), (.Advice, "Advice"),
   (.IsCompressed, "IsCompressed"), (.IsFirstInSequence, "IsFirstInSequence"),
   (.IsLastInSequence, "IsLastInSequence")]

/-- Instruction flags in enum order, as the driver lists them. -/
def instructionFlagNames : List (InstructionFlags × String) :=
  [(.LeftOperandIsPC, "LeftOperandIsPC"), (.RightOperandIsImm, "RightOperandIsImm"),
   (.LeftOperandIsRs1Value, "LeftOperandIsRs1Value"),
   (.RightOperandIsRs2Value, "RightOperandIsRs2Value"), (.Branch, "Branch"),
   (.IsNoop, "IsNoop"), (.RightOperandIsRdWriteValue, "RightOperandIsRdWriteValue")]

deriving instance Repr for LookupTableKind

/-- The constructor name, which by construction is Rust's `LookupTableKind`
variant name. -/
def lookupTableName (t : LookupTableKind) : String :=
  let s := toString (repr t)
  (s.splitOn ".").getLast!

/-- A Lean row rendered into the driver's schema, flags included. -/
def RowView.ofLeanRow (row : JoltInstructionRow) : RowView :=
  let (kind, rd, rs1, rs2) := operands row.instruction
  { kind, rd, rs1, rs2
    address := row.address.toNat
    imm := JoltMetadata.immediate row.instruction
    vsr := row.virtual_sequence_remaining.map (·.toNat)
    first := row.is_first_in_sequence
    compressed := row.is_compressed
    circuitFlags := some <| circuitFlagNames.filterMap fun (f, n) =>
      if JoltMetadata.circuitFlag row f then some n else none
    instructionFlags := some <| instructionFlagNames.filterMap fun (f, n) =>
      if JoltMetadata.instructionFlag row.instruction f then some n else none
    lookupTable := some ((JoltMetadata.lookupTable row.instruction).map lookupTableName)
    raf := some (JoltMetadata.instructionRafFlag row.instruction) }

/-- The rows of a straight-line program, written here rather than taken from
`JoltISA.Program.instrs` so the test does not depend on the model's helper. -/
def programRows : JoltISA.Program → List JoltISA.Instr
  | .done _ => []
  | .instr i next => i :: programRows next

/-! ## Comparison -/

/-- One field on which the two sides disagree. -/
structure FieldDiff where
  field : String
  rust : String
  lean : String

def showOpt {α : Type} [ToString α] : Option α → String
  | some a => toString a
  | none => "null"

def showList (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

/-- Field-by-field comparison. A field that either side leaves out
(`none` in an optional field) is not compared. -/
def compareRows (rust lean : RowView) : List FieldDiff := Id.run do
  let mut out : Array FieldDiff := #[]
  if rust.kind != lean.kind then out := out.push ⟨"kind", rust.kind, lean.kind⟩
  if rust.address != lean.address then
    out := out.push ⟨"address", toString rust.address, toString lean.address⟩
  if rust.rd != lean.rd then out := out.push ⟨"rd", showOpt rust.rd, showOpt lean.rd⟩
  if rust.rs1 != lean.rs1 then out := out.push ⟨"rs1", showOpt rust.rs1, showOpt lean.rs1⟩
  if rust.rs2 != lean.rs2 then out := out.push ⟨"rs2", showOpt rust.rs2, showOpt lean.rs2⟩
  if rust.imm != lean.imm then out := out.push ⟨"imm", toString rust.imm, toString lean.imm⟩
  if rust.vsr != lean.vsr then out := out.push ⟨"vsr", showOpt rust.vsr, showOpt lean.vsr⟩
  if rust.first != lean.first then
    out := out.push ⟨"first", toString rust.first, toString lean.first⟩
  if rust.compressed != lean.compressed then
    out := out.push ⟨"compressed", toString rust.compressed, toString lean.compressed⟩
  if let (some r, some l) := (rust.circuitFlags, lean.circuitFlags) then
    if r != l then out := out.push ⟨"circuit_flags", showList r, showList l⟩
  if let (some r, some l) := (rust.instructionFlags, lean.instructionFlags) then
    if r != l then out := out.push ⟨"instruction_flags", showList r, showList l⟩
  if let (some r, some l) := (rust.lookupTable, lean.lookupTable) then
    if r != l then out := out.push ⟨"lookup_table", showOpt r, showOpt l⟩
  if let (some r, some l) := (rust.raf, lean.raf) then
    if r != l then out := out.push ⟨"raf", toString r, toString l⟩
  return out.toList

end ExpansionParity
