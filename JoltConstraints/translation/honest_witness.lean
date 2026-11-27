import JoltConstraints.translation.honest_witness_helpers.ram_inc
import JoltConstraints.translation.honest_witness_helpers.ram_val
import JoltConstraints.translation.witness_helpers.branch
import JoltConstraints.translation.witness_helpers.bytecode_ra_chunk
import JoltConstraints.translation.witness_helpers.instruction_ra
import JoltConstraints.translation.witness_helpers.instruction_ra_chunk
import JoltConstraints.translation.witness_helpers.instruction_raf_flag
import JoltConstraints.translation.witness_helpers.left_lookup_operand
import JoltConstraints.translation.witness_helpers.lookup_output
import JoltConstraints.translation.witness_helpers.lookup_table_flag
import JoltConstraints.translation.witness_helpers.next_is_first_in_sequence
import JoltConstraints.translation.witness_helpers.next_is_noop
import JoltConstraints.translation.witness_helpers.next_is_virtual
import JoltConstraints.translation.witness_helpers.next_pc
import JoltConstraints.translation.witness_helpers.next_unexpanded_pc
import JoltConstraints.translation.witness_helpers.product
import JoltConstraints.translation.witness_helpers.ram_val_final
import JoltConstraints.translation.witness_helpers.rd_inc
import JoltConstraints.translation.witness_helpers.registers_val
import JoltConstraints.translation.witness_helpers.right_lookup_operand
import JoltConstraints.translation.witness_helpers.rs1_ra
import JoltConstraints.translation.witness_helpers.rs2_ra

open LeanRV64D

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
