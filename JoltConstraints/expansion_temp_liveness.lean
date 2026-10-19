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

def ExpandedTempsOk : ExpandedSource → Prop
  | .native row => tempsReadAfterWrite [row] = true
  | .sequence rows => tempsReadAfterWrite rows = true

end ExpansionTempLiveness
