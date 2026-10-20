/-
Instruction temporaries used by Rust's built-in expansions are registers 40–47.
The reserved virtual registers 32–39 carry machine state, including the LR/SC
reservations at 32 and 33, and are deliberately excluded here.
See : jolt/crates/jolt-program/src/expand/allocator.rs:1-15, 115-139, 184-199
      (8bbb2357)
-/
import JoltConstraints.expansions

set_option autoImplicit false

namespace ExpansionTempLiveness

open JoltISA

/-- The explicit operands read by a final row. A destination is not a read
unless it also occurs as a source operand. -/
def readSources : Instr → List Src
  | .ADDI _ src _ | .ADDIW _ src _ | .ANDI _ src _ | .ORI _ src _
  | .XORI _ src _ | .SLTI _ src _ | .SLTIU _ src _ | .JALR _ src _
  | .VirtualMULI _ src _ | .VirtualMULIW _ src _
  | .VirtualPow2 _ src _ | .VirtualPow2W _ src _
  | .VirtualShiftRightBitmask _ src _ | .VirtualShiftRightBitmaskW _ src _
  | .VirtualSRLI _ src _ | .VirtualSRAI _ src _
  | .VirtualSRLIW _ src _ | .VirtualSRAIW _ src _
  | .VirtualROTRI _ src _ | .VirtualROTRIW _ src _ | .VirtualRev8W _ src _
  | .VirtualAlignAddr _ src _ | .VirtualWindowMaskB _ src _
  | .VirtualWindowMaskH _ src _ | .VirtualWindowMaskW _ src _
  | .VirtualSignExtendWord _ src _ | .VirtualZeroExtendWord _ src _
  | .VirtualMovsign _ src _ | .LD _ _ src _ | .VirtualHostIO _ src _
  | .VirtualAssertHalfwordAlignment src _ _
  | .VirtualAssertWordAlignment src _ _ => [src]
  | .ADD _ lhs rhs | .ADDW _ lhs rhs | .SUB _ lhs rhs | .SUBW _ lhs rhs
  | .MUL _ lhs rhs | .MULW _ lhs rhs | .MULHU _ lhs rhs | .ANDN _ lhs rhs
  | .OR _ lhs rhs | .XOR _ lhs rhs | .AND _ lhs rhs
  | .SLT _ lhs rhs | .SLTU _ lhs rhs
  | .VirtualSRL _ lhs rhs | .VirtualSRA _ lhs rhs
  | .VirtualSRLW _ lhs rhs | .VirtualSRAW _ lhs rhs
  | .VirtualXORROT32 _ lhs rhs | .VirtualXORROT24 _ lhs rhs
  | .VirtualXORROT16 _ lhs rhs | .VirtualXORROT63 _ lhs rhs
  | .VirtualXORROTL1 _ lhs rhs | .VirtualXORROTW16 _ lhs rhs
  | .VirtualXORROTW12 _ lhs rhs | .VirtualXORROTW8 _ lhs rhs
  | .VirtualXORROTW7 _ lhs rhs | .VirtualXORROTW22 _ lhs rhs
  | .VirtualXORROTW19 _ lhs rhs | .VirtualXORROTW6 _ lhs rhs
  | .VirtualPext _ lhs rhs | .VirtualPextSigned _ lhs rhs
  | .VirtualShiftDataB _ lhs rhs | .VirtualShiftDataH _ lhs rhs
  | .VirtualShiftDataW _ lhs rhs | .VirtualNegateIf _ lhs rhs
  | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _ | .BGE lhs rhs _
  | .BLTU lhs rhs _ | .BGEU lhs rhs _ | .SD lhs rhs _
  | .VirtualAssertEQ lhs rhs _ | .VirtualAssertValidDiv0 lhs rhs _
  | .VirtualAssertValidUnsignedRemainder lhs rhs _
  | .VirtualAssertMulUNoOverflow lhs rhs _ | .VirtualAssertLTE lhs rhs _ => [lhs, rhs]
  | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .FENCE
  | .VirtualPow2I _ _ | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmaskI _ _ | .VirtualAdvice _ _ _
  | .VirtualAdviceLoad _ _ => []

def reads (register : JoltISA.VReg) (row : Instr) : Bool :=
  (readSources row).any fun source =>
    match source with
    | .vreg address => address == register
    | .xreg _ => false

def writes (register : JoltISA.VReg) (row : Instr) : Bool :=
  match row.destination? with
  | some (.vreg address) => address == register
  | _ => false

/-- Before the first write to this temporary, no row may read it. Reads on a
row that also writes it count as reads before that row's write. -/
def firstAccessIsWrite (register : JoltISA.VReg) : List Instr → Bool
  | [] => true
  | row :: rest =>
      !reads register row &&
        (writes register row || firstAccessIsWrite register rest)

/-- Every short-lived instruction temporary is initialized before use within
one source instruction's expansion. This is independent of the starting value
of each temporary, including a value written by an earlier HostIO call. -/
def tempsReadAfterWrite (rows : List Instr) : Bool :=
  (List.range 8).all fun index =>
    firstAccessIsWrite (BitVec.ofNat 7 (40 + index)) rows

/-- The per-expansion check includes the HostIO rewrite register. -/
theorem hostTemp_firstAccessIsWrite (rows : List Instr)
    (ok : tempsReadAfterWrite rows = true) :
    firstAccessIsWrite rdZeroRewriteVReg rows = true := by
  have checked := List.all_eq_true.mp ok 0 (by simp)
  simpa only [Nat.add_zero] using checked

/-- A pending temporary is not read by the first row of an expansion. -/
theorem firstAccessIsWrite_head_no_read (register : JoltISA.VReg) (row : Instr)
    (rest : List Instr)
    (ok : firstAccessIsWrite register (row :: rest) = true) :
    reads register row = false := by
  simp only [firstAccessIsWrite, Bool.and_eq_true] at ok
  cases h : reads register row with
  | false => rfl
  | true => simp [h] at ok

/-- If the first row does not write the pending temporary, the rest of the
expansion still has to write it before reading it. -/
theorem firstAccessIsWrite_tail (register : JoltISA.VReg) (row : Instr)
    (rest : List Instr)
    (ok : firstAccessIsWrite register (row :: rest) = true)
    (noWrite : writes register row = false) :
    firstAccessIsWrite register rest = true := by
  simp only [firstAccessIsWrite, Bool.and_eq_true, Bool.or_eq_true] at ok
  rcases ok.2 with wrote | pending
  · rw [noWrite] at wrote
    cases wrote
  · exact pending

def ExpandedTempsOk : ExpandedSource → Prop
  | .native row => tempsReadAfterWrite [row] = true
  | .sequence rows => tempsReadAfterWrite rows = true

def firstRow? : ExpandedSource → Option Instr
  | .native row => some row
  | .sequence rows => rows.head?

/-- The first row of a checked source expansion does not read the HostIO
rewrite register before it can be written. -/
theorem hostTemp_firstRow_noRead (expanded : ExpandedSource)
    (ok : ExpandedTempsOk expanded) (row : Instr)
    (first : firstRow? expanded = some row) :
    reads rdZeroRewriteVReg row = false := by
  cases expanded with
  | native instruction =>
    simp only [firstRow?, Option.some.injEq] at first
    subst row
    exact firstAccessIsWrite_head_no_read _ _ []
      (hostTemp_firstAccessIsWrite [instruction] ok)
  | sequence rows =>
    cases rows with
    | nil => simp [firstRow?] at first
    | cons instruction rest =>
      simp only [firstRow?, List.head?_cons, Option.some.injEq] at first
      subst row
      exact firstAccessIsWrite_head_no_read _ _ rest
        (hostTemp_firstAccessIsWrite (instruction :: rest) ok)

end ExpansionTempLiveness
