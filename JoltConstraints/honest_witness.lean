import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_trace
import JoltConstraints.witness_helpers
import JoltConstraints.honest_witness_helpers.ram_read_value
import JoltConstraints.honest_witness_helpers.ram_inc
import JoltConstraints.honest_witness_helpers.ram_val
import JoltConstraints.trace_interface
import JoltConstraints.witness_domain
import JoltConstraints.execution_conditions

set_option autoImplicit false

-- Every column comes from an honest trace. The result remains a term of the
-- unrestricted WitnessType used by the relation; it carries no proof fields.
noncomputable def HonestTrace.honestWitness {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : WitnessType F p :=
  {
    PC := TraceWitness.PC p trace
    UnexpandedPC := TraceWitness.UnexpandedPC p trace
    Imm := TraceWitness.Imm p trace
    Rs1Value := TraceWitness.Rs1Value p trace
    Rs2Value := TraceWitness.Rs2Value p trace
    RdWriteValue := TraceWitness.RdWriteValue p trace
    RamAddress := TraceWitness.RamAddress p trace
    RamReadValue := HonestWitness.RamReadValue p trace
    RamWriteValue := TraceWitness.RamWriteValue p trace
    LeftInstructionInput := TraceWitness.LeftInstructionInput p trace
    RightInstructionInput := TraceWitness.RightInstructionInput p trace
    LeftLookupOperand := TraceWitness.LeftLookupOperand p trace
    RightLookupOperand := TraceWitness.RightLookupOperand p trace
    LookupOutput := TraceWitness.LookupOutput p trace
    Product := TraceWitness.Product p trace
    ShouldBranch := TraceWitness.ShouldBranch p trace
    ShouldJump := TraceWitness.ShouldJump p trace
    NextUnexpandedPC := TraceWitness.NextUnexpandedPC p trace
    NextPC := TraceWitness.NextPC p trace
    NextIsVirtual := TraceWitness.NextIsVirtual p trace
    NextIsFirstInSequence := TraceWitness.NextIsFirstInSequence p trace
    NextIsNoop := TraceWitness.NextIsNoop p trace
    OpFlags := TraceWitness.OpFlags p trace
    InstructionFlags := TraceWitness.InstructionFlags p trace
    LookupTableFlag := TraceWitness.LookupTableFlag p trace
    InstructionRafFlag := TraceWitness.InstructionRafFlag p trace
    RdInc := TraceWitness.RdInc p trace
    RamInc := HonestWitness.RamInc p trace
    RamHammingWeight := TraceWitness.RamHammingWeight p trace
    Rs1Ra := TraceWitness.Rs1Ra p trace
    Rs2Ra := TraceWitness.Rs2Ra p trace
    RdWa := TraceWitness.RdWa p trace
    RegistersVal := TraceWitness.RegistersVal p trace
    RamRa := TraceWitness.RamRa p trace
    RamVal := HonestWitness.RamVal p trace
    RamValFinal := TraceWitness.RamValFinal p trace
    InstructionRaChunk := TraceWitness.InstructionRaChunk p trace
    BytecodeRaChunk := TraceWitness.BytecodeRaChunk p trace
    RamRaChunk := TraceWitness.RamRaChunk p trace
    InstructionRa := TraceWitness.InstructionRa p trace }
