import JoltConstraints.Soundness.Layer5.Arithmetic
import JoltConstraints.Soundness.Layer5.WordArithmetic
import JoltConstraints.Soundness.Layer5.BitwiseBinary
import JoltConstraints.Soundness.Layer5.RegisterComparison
import JoltConstraints.Soundness.Layer5.VirtualBinary
import JoltConstraints.Soundness.Layer5.XorRotation
import JoltConstraints.Soundness.Layer5.ImmediateArithmetic
import JoltConstraints.Soundness.Layer5.ImmediateLogic
import JoltConstraints.Soundness.Layer5.AddressMasks
import JoltConstraints.Soundness.Layer5.UnaryWord
import JoltConstraints.Soundness.Layer5.ImmediateShift
import JoltConstraints.Soundness.Layer5.ImmediatePowerMask
import JoltConstraints.Soundness.Layer5.LoadUpperImmediate
import JoltConstraints.Soundness.Layer5.Auipc
import JoltConstraints.Soundness.Layer5.SetLessThanImmediate
import JoltConstraints.Soundness.Layer5.XorImmediate
import JoltConstraints.Soundness.Layer5.Movsign
import JoltConstraints.Soundness.Layer5.AssertionsAlignment
import JoltConstraints.Soundness.Layer5.RegisterShift
import JoltConstraints.expansion_temp_liveness

/-! The register-writing families with a local selected-row execution rule. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- A register-writing row described by its existing Layer 5 family and operands.
For example, AND is a bitwise row and VirtualSRLI is an immediate-shift row. -/
inductive PlainWriteKind where
  | arithmetic (operation : RegisterArithmetic) (destination : Dst) (lhs rhs : Src)
  | word (operation : WordArithmetic) (destination : Dst) (lhs rhs : Src)
  | bitwise (operation : BitwiseBinary) (destination : Dst) (lhs rhs : Src)
  | comparison (operation : RegisterComparison) (destination : Dst) (lhs rhs : Src)
  | virtualBinary (operation : VirtualBinary) (destination : Dst) (lhs rhs : Src)
  | xorRotation (operation : XorRotation) (destination : Dst) (lhs rhs : Src)
  | immediate (operation : ImmediateArithmetic) (destination : Dst) (source : Src) (imm : BitVec 64)
  | logic (operation : ImmediateLogic) (destination : Dst) (source : Src) (imm : BitVec 64)
  | address (operation : AddressMask) (destination : Dst) (source : Src) (imm : BitVec 64)
  | unary (operation : UnaryWord) (destination : Dst) (source : Src) (imm : BitVec 64)
  | shift (operation : ImmediateShift) (destination : Dst) (source : Src) (imm : Nat)
  | power (operation : ImmediatePowerMask) (destination : Dst) (imm : Nat)
  | lui (destination : Dst) (imm : BitVec 64)
  | auipc (destination : Dst) (imm : BitVec 64)
  | sltiu (destination : Dst) (source : Src) (imm : BitVec 64)
  | xori (destination : Dst) (source : Src) (imm : BitVec 64)
  | movsign (destination : Dst) (source : Src) (imm : BitVec 64)

/-- Recover the instruction of a register-writing family member.
For example, the `bitwise .and` member constructs an AND instruction. -/
def PlainWriteKind.instruction : PlainWriteKind → Instr
  | .arithmetic operation destination lhs rhs => operation.instruction destination lhs rhs
  | .word operation destination lhs rhs => operation.instruction destination lhs rhs
  | .bitwise operation destination lhs rhs => operation.instruction destination lhs rhs
  | .comparison operation destination lhs rhs => operation.instruction destination lhs rhs
  | .virtualBinary operation destination lhs rhs => operation.instruction destination lhs rhs
  | .xorRotation operation destination lhs rhs => operation.instruction destination lhs rhs
  | .immediate operation destination source imm => operation.instruction destination source imm
  | .logic operation destination source imm => operation.instruction destination source imm
  | .address operation destination source imm => operation.instruction destination source imm
  | .unary operation destination source imm => operation.instruction destination source imm
  | .shift operation destination source imm => operation.instruction destination source imm
  | .power operation destination imm => operation.instruction destination imm
  | .lui destination imm => .LUI destination imm
  | .auipc destination imm => .AUIPC destination imm
  | .sltiu destination source imm => .SLTIU destination source imm
  | .xori destination source imm => .XORI destination source imm
  | .movsign destination source imm => .VirtualMovsign destination source imm

/-- The destination written by a family member; for example, AND writes its `destination`. -/
def PlainWriteKind.destination : PlainWriteKind → Dst
  | .arithmetic _ destination _ _ => destination
  | .word _ destination _ _ => destination
  | .bitwise _ destination _ _ => destination
  | .comparison _ destination _ _ => destination
  | .virtualBinary _ destination _ _ => destination
  | .xorRotation _ destination _ _ => destination
  | .immediate _ destination _ _ => destination
  | .logic _ destination _ _ => destination
  | .address _ destination _ _ => destination
  | .unary _ destination _ _ => destination
  | .shift _ destination _ _ => destination
  | .power _ destination _ => destination
  | .lui destination _ => destination
  | .auipc destination _ => destination
  | .sltiu destination _ _ => destination
  | .xori destination _ _ => destination
  | .movsign destination _ _ => destination

/-- The explicit sources read by a family member; for example, AND reads `[lhs, rhs]`. -/
def PlainWriteKind.sources : PlainWriteKind → List Src
  | .arithmetic _ _ lhs rhs => [lhs, rhs]
  | .word _ _ lhs rhs => [lhs, rhs]
  | .bitwise _ _ lhs rhs => [lhs, rhs]
  | .comparison _ _ lhs rhs => [lhs, rhs]
  | .virtualBinary _ _ lhs rhs => [lhs, rhs]
  | .xorRotation _ _ lhs rhs => [lhs, rhs]
  | .immediate _ _ source _ => [source]
  | .logic _ _ source _ => [source]
  | .address _ _ source _ => [source]
  | .unary _ _ source _ => [source]
  | .shift _ _ source _ => [source]
  | .power _ _ _ => []
  | .lui _ _ => []
  | .auipc _ _ => []
  | .sltiu _ source _ => [source]
  | .xori _ source _ => [source]
  | .movsign _ source _ => [source]

/-- A family description has the same destination and sources as its instruction,
and carries no runtime advice; for example, AND reads two sources and writes one destination. -/
theorem PlainWriteKind.shape (kind : PlainWriteKind) :
    kind.instruction.destination? = some kind.destination ∧
    kind.instruction.adviceValue? = none ∧
    ExpansionTempLiveness.readSources kind.instruction = kind.sources := by
  cases kind with
  | arithmetic operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | word operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | bitwise operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | comparison operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | virtualBinary operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | xorRotation operation destination lhs rhs => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | immediate operation destination source imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | logic operation destination source imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | address operation destination source imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | unary operation destination source imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | shift operation destination source imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | power operation destination imm => cases operation <;> exact ⟨rfl, rfl, rfl⟩
  | lui destination imm => exact ⟨rfl, rfl, rfl⟩
  | auipc destination imm => exact ⟨rfl, rfl, rfl⟩
  | sltiu destination source imm => exact ⟨rfl, rfl, rfl⟩
  | xori destination source imm => exact ⟨rfl, rfl, rfl⟩
  | movsign destination source imm => exact ⟨rfl, rfl, rfl⟩

/-- These register-writing families never consume a tape answer.
For example, VirtualPow2I ignores the answer even when its destination is a temporary. -/
theorem PlainWriteKind.noTape (kind : PlainWriteKind) (destination : Dst) (width : BitVec 64) :
    kind.instruction ≠ .VirtualAdviceLoad destination width := by
  cases kind with
  | arithmetic operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | word operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | bitwise operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | comparison operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | virtualBinary operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | xorRotation operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | immediate operation dst source imm => cases operation <;> intro impossible <;> cases impossible
  | logic operation dst source imm => cases operation <;> intro impossible <;> cases impossible
  | address operation dst source imm => cases operation <;> intro impossible <;> cases impossible
  | unary operation dst source imm => cases operation <;> intro impossible <;> cases impossible
  | shift operation dst source imm => cases operation <;> intro impossible <;> cases impossible
  | power operation dst imm => cases operation <;> intro impossible <;> cases impossible
  | lui dst imm => intro impossible; cases impossible
  | auipc dst imm => intro impossible; cases impossible
  | sltiu dst source imm => intro impossible; cases impossible
  | xori dst source imm => intro impossible; cases impossible
  | movsign dst source imm => intro impossible; cases impossible

/-- Plain rows whose execution uses answer zero, grouped by their existing rule.
For example, VirtualSRL needs the prepared mask while FENCE has no destination. -/
inductive OtherScalarKind where
  | write (kind : PlainWriteKind)
  | shift (operation : RegisterShift) (destination : Dst) (lhs rhs : Src)
  | assertEq (lhs rhs : Src) (imm : BitVec 128)
  | alignment (kind : AlignmentAssertion) (base : Src) (imm : BitVec 64) (fault : ExceptionType)
  | fence

/-- Recover a scalar row's instruction.
For example, `assertEq lhs rhs imm` constructs VirtualAssertEQ. -/
def OtherScalarKind.instruction : OtherScalarKind → Instr
  | .write kind => kind.instruction
  | .shift operation destination lhs rhs => operation.instruction destination lhs rhs
  | .assertEq lhs rhs imm => .VirtualAssertEQ lhs rhs imm
  | .alignment kind base imm fault => kind.instruction base imm fault
  | .fence => .FENCE

/-- Scalar rows do not read tape; for example, a register shift ignores its answer. -/
theorem OtherScalarKind.noTape (kind : OtherScalarKind) (destination : Dst) (width : BitVec 64) :
    kind.instruction ≠ .VirtualAdviceLoad destination width := by
  cases kind with
  | write kind => exact kind.noTape destination width
  | shift operation dst lhs rhs => cases operation <;> intro impossible <;> cases impossible
  | alignment kind base imm fault => cases kind <;> intro impossible <;> cases impossible
  | assertEq lhs rhs imm => intro impossible; cases impossible
  | fence => intro impossible; cases impossible

/-- Classify the remaining scalar instructions by their Layer 5 family.
For example, AND becomes a bitwise family member; BEQ and VirtualAdviceLoad return `none`.
The twelve division kinds are handled separately by the existing division dispatcher. -/
def otherScalarKind? : Instr → Option OtherScalarKind
  | .ADD destination lhs rhs => some (.write (.arithmetic .add destination lhs rhs))
  | .ADDW destination lhs rhs => some (.write (.word .addw destination lhs rhs))
  | .SUBW destination lhs rhs => some (.write (.word .subw destination lhs rhs))
  | .MULW destination lhs rhs => some (.write (.word .mulw destination lhs rhs))
  | .MULHU destination lhs rhs => some (.write (.word .mulhu destination lhs rhs))
  | .AND destination lhs rhs => some (.write (.bitwise .and destination lhs rhs))
  | .OR destination lhs rhs => some (.write (.bitwise .or destination lhs rhs))
  | .ANDN destination lhs rhs => some (.write (.bitwise .andn destination lhs rhs))
  | .SLT destination lhs rhs => some (.write (.comparison .signed destination lhs rhs))
  | .SLTU destination lhs rhs => some (.write (.comparison .unsigned destination lhs rhs))
  | .VirtualPext destination lhs rhs => some (.write (.virtualBinary .pext destination lhs rhs))
  | .VirtualPextSigned destination lhs rhs => some (.write (.virtualBinary .pextSigned destination lhs rhs))
  | .VirtualShiftDataB destination lhs rhs => some (.write (.virtualBinary .shiftDataB destination lhs rhs))
  | .VirtualShiftDataH destination lhs rhs => some (.write (.virtualBinary .shiftDataH destination lhs rhs))
  | .VirtualShiftDataW destination lhs rhs => some (.write (.virtualBinary .shiftDataW destination lhs rhs))
  | .VirtualXORROT32 destination lhs rhs => some (.write (.xorRotation .r32 destination lhs rhs))
  | .VirtualXORROT24 destination lhs rhs => some (.write (.xorRotation .r24 destination lhs rhs))
  | .VirtualXORROT16 destination lhs rhs => some (.write (.xorRotation .r16 destination lhs rhs))
  | .VirtualXORROT63 destination lhs rhs => some (.write (.xorRotation .r63 destination lhs rhs))
  | .VirtualXORROTL1 destination lhs rhs => some (.write (.xorRotation .l1 destination lhs rhs))
  | .VirtualXORROTW16 destination lhs rhs => some (.write (.xorRotation .w16 destination lhs rhs))
  | .VirtualXORROTW12 destination lhs rhs => some (.write (.xorRotation .w12 destination lhs rhs))
  | .VirtualXORROTW8 destination lhs rhs => some (.write (.xorRotation .w8 destination lhs rhs))
  | .VirtualXORROTW7 destination lhs rhs => some (.write (.xorRotation .w7 destination lhs rhs))
  | .VirtualXORROTW22 destination lhs rhs => some (.write (.xorRotation .w22 destination lhs rhs))
  | .VirtualXORROTW19 destination lhs rhs => some (.write (.xorRotation .w19 destination lhs rhs))
  | .VirtualXORROTW6 destination lhs rhs => some (.write (.xorRotation .w6 destination lhs rhs))
  | .ADDIW destination source imm => some (.write (.immediate .addiw destination source imm))
  | .VirtualMULI destination source imm => some (.write (.immediate .muli destination source imm))
  | .VirtualMULIW destination source imm => some (.write (.immediate .muliw destination source imm))
  | .ANDI destination source imm => some (.write (.logic .andi destination source imm))
  | .ORI destination source imm => some (.write (.logic .ori destination source imm))
  | .SLTI destination source imm => some (.write (.logic .slti destination source imm))
  | .VirtualAlignAddr destination source imm => some (.write (.address .align destination source imm))
  | .VirtualWindowMaskB destination source imm => some (.write (.address .byte destination source imm))
  | .VirtualWindowMaskH destination source imm => some (.write (.address .halfword destination source imm))
  | .VirtualWindowMaskW destination source imm => some (.write (.address .word destination source imm))
  | .VirtualPow2 destination source imm => some (.write (.unary .pow2 destination source imm))
  | .VirtualPow2W destination source imm => some (.write (.unary .pow2W destination source imm))
  | .VirtualShiftRightBitmask destination source imm => some (.write (.unary .shiftMask destination source imm))
  | .VirtualShiftRightBitmaskW destination source imm => some (.write (.unary .shiftMaskW destination source imm))
  | .VirtualRev8W destination source imm => some (.write (.unary .rev8w destination source imm))
  | .VirtualSRLI destination source imm => some (.write (.shift .srl destination source imm))
  | .VirtualSRAI destination source imm => some (.write (.shift .sra destination source imm))
  | .VirtualSRLIW destination source imm => some (.write (.shift .srlw destination source imm))
  | .VirtualSRAIW destination source imm => some (.write (.shift .sraw destination source imm))
  | .VirtualPow2I destination imm => some (.write (.power .pow2I destination imm))
  | .VirtualPow2IW destination imm => some (.write (.power .pow2IW destination imm))
  | .VirtualShiftRightBitmaskI destination imm => some (.write (.power .shiftMaskI destination imm))
  | .LUI destination imm => some (.write (.lui destination imm))
  | .AUIPC destination imm => some (.write (.auipc destination imm))
  | .SLTIU destination source imm => some (.write (.sltiu destination source imm))
  | .XORI destination source imm => some (.write (.xori destination source imm))
  | .VirtualMovsign destination source imm => some (.write (.movsign destination source imm))
  | .VirtualSRL destination lhs rhs => some (.shift .srl destination lhs rhs)
  | .VirtualSRA destination lhs rhs => some (.shift .sra destination lhs rhs)
  | .VirtualSRLW destination lhs rhs => some (.shift .srlw destination lhs rhs)
  | .VirtualSRAW destination lhs rhs => some (.shift .sraw destination lhs rhs)
  | .VirtualAssertEQ lhs rhs imm => some (.assertEq lhs rhs imm)
  | .VirtualAssertHalfwordAlignment base imm fault => some (.alignment .halfword base imm fault)
  | .VirtualAssertWordAlignment base imm fault => some (.alignment .word base imm fault)
  | .FENCE => some (.fence)
  | _ => none

end JoltInstance
