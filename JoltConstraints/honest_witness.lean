import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Rust: [oracle_table](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/oracle.rs).
-- Each helper receives the same successful, linked trace and can access
-- its rows and program.initialState.
-- Helpers fill p.traceLength witness positions, padding beyond trace.rows.size.
-- ramFits certifies that every nonzero RAM access is representable in p.ramSize.
-- The prover-padded-length premise matches Rust's selected cycle domain and
-- ensures that no execution suffix is omitted and a padding row remains.
-- TODO: Eventually name it params and not p but its not a major issue for now
noncomputable def JoltProgram.honestWitness {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : p.RamFits trace)
    (_padded : p.ProverPaddedFor trace.rows.size) : WitnessType F p :=
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
    RamRa := HonestWitness.RamRa p trace ramFits
    RamVal := HonestWitness.RamVal p trace ramFits
    RamValFinal := HonestWitness.RamValFinal p trace
    InstructionRaChunk := HonestWitness.InstructionRaChunk p trace
    BytecodeRaChunk := HonestWitness.BytecodeRaChunk p trace
    RamRaChunk := HonestWitness.RamRaChunk p trace
    InstructionRa := HonestWitness.InstructionRa p trace }
