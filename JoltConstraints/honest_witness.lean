import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_trace
import JoltConstraints.witness_helpers
import JoltConstraints.trace_interface
import JoltConstraints.witness_domain
import JoltConstraints.execution_conditions

set_option autoImplicit false

-- Rust: [oracle_table](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/crates/jolt-witness/src/backend/trace/oracle.rs).
-- The honest witness: every column read from one honest trace. Positions beyond
-- trace.rows.size are padding. The sizes `p` are any WitnessParams; the completeness
-- theorems use Rust's (HonestTrace.witness_params) and the facts proved about them.
noncomputable def HonestTrace.honestWitness {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : WitnessType F p :=
  {
    PC := HonestWitness.PC p trace
    UnexpandedPC := HonestWitness.UnexpandedPC p trace
    Imm := HonestWitness.Imm p trace
    Rs1Value := HonestWitness.Rs1Value p trace
    Rs2Value := HonestWitness.Rs2Value p trace
    RdWriteValue := HonestWitness.RdWriteValue p trace
    RamAddress := HonestWitness.RamAddress p trace
    RamReadValue := HonestWitness.RamReadValue p trace
    RamWriteValue := HonestWitness.RamWriteValue p trace
    LeftInstructionInput := HonestWitness.LeftInstructionInput p trace
    RightInstructionInput := HonestWitness.RightInstructionInput p trace
    LeftLookupOperand := HonestWitness.LeftLookupOperand p trace
    RightLookupOperand := HonestWitness.RightLookupOperand p trace
    LookupOutput := HonestWitness.LookupOutput p trace
    Product := HonestWitness.Product p trace
    ShouldBranch := HonestWitness.ShouldBranch p trace
    ShouldJump := HonestWitness.ShouldJump p trace
    NextUnexpandedPC := HonestWitness.NextUnexpandedPC p trace
    NextPC := HonestWitness.NextPC p trace
    NextIsVirtual := HonestWitness.NextIsVirtual p trace
    NextIsFirstInSequence := HonestWitness.NextIsFirstInSequence p trace
    NextIsNoop := HonestWitness.NextIsNoop p trace
    OpFlags := HonestWitness.OpFlags p trace
    InstructionFlags := HonestWitness.InstructionFlags p trace
    LookupTableFlag := HonestWitness.LookupTableFlag p trace
    InstructionRafFlag := HonestWitness.InstructionRafFlag p trace
    RdInc := HonestWitness.RdInc p trace
    RamInc := HonestWitness.RamInc p trace
    RamHammingWeight := HonestWitness.RamHammingWeight p trace
    Rs1Ra := HonestWitness.Rs1Ra p trace
    Rs2Ra := HonestWitness.Rs2Ra p trace
    RdWa := HonestWitness.RdWa p trace
    RegistersVal := HonestWitness.RegistersVal p trace
    RamRa := HonestWitness.RamRa p trace
    RamVal := HonestWitness.RamVal p trace
    RamValFinal := HonestWitness.RamValFinal p trace
    InstructionRaChunk := HonestWitness.InstructionRaChunk p trace
    BytecodeRaChunk := HonestWitness.BytecodeRaChunk p trace
    RamRaChunk := HonestWitness.RamRaChunk p trace
    InstructionRa := HonestWitness.InstructionRa p trace }
