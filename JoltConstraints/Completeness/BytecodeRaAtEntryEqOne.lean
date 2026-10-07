import JoltConstraints.Constraints.BytecodeRaAtEntryEqOne
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.honest_witness
import JoltConstraints.ProgramLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
Trace linkage alone does not select the first instruction. startsAtEntry
connects the first executed row to the public entry slot. -/
theorem honestWitness_bytecodeRaAtEntryEqOne
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (entry : Fin (2 ^ params.logBytecodeK))
    (nonempty : 0 < trace.rows.size)
    (startsAtEntry : (getElem trace.rows 0 nonempty).rowIndex.val + 1 = entry.val)
    : bytecodeRaAtEntryEqOne entry
      (HonestTrace.honestWitness (F := F) params trace) := by
  unfold bytecodeRaAtEntryEqOne bytecodeRa
  apply Finset.prod_eq_one
  intro chunk _
  dsimp [HonestTrace.honestWitness, HonestWitness.BytecodeRaChunk,
    HonestWitness.addressChunkEntry, bytecodeAddressChunk,
    HonestWitness.addressChunk]
  simp [HonestWitness.bytecodePc, nonempty, startsAtEntry]

/-- Constraint (53) from the public entry address, rather than an assumed
equality with the first trace row's bytecode slot. Two rows that each start their
instruction at the same address are the same row (`expand_program_first_of_address`). The witness slot is one
greater than the trace index because preprocessing prepends the no-op.

Rust revision `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`:
`crates/jolt-trace/src/preprocess/bytecode.rs::entry_bytecode_index` calls
`BytecodePCMapper::get_first_pc(entry_address)` to select this row. -/
theorem honestWitness_bytecodeRaAtEntryEqOne_of_address
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (entry : Fin trace.bytecode.size)
    (entryIsStart : trace.bytecode[entry].starts_source = true)
    (entryAddress : trace.initialState.sail.regs.get? Register.PC =
      some trace.bytecode[entry].address)
    (nonempty : 0 < trace.rows.size) :
    bytecodeRaAtEntryEqOne
      ⟨entry.val + 1, by have := bytecodeDomain.rowsFit; omega⟩
      (HonestTrace.honestWitness (F := F) params trace) := by
  have first := trace.startsAtEntry nonempty
  have accepted := accepted_pc_map_ok joltInstance trace.bytecode trace.expands trace.accepted
  -- the first row and the entry row start their instructions at the same address
  have sameAddress : trace.bytecode[(getElem trace.rows 0 nonempty).rowIndex].address =
      trace.bytecode[entry].address :=
    Option.some.inj (first.2.symm.trans entryAddress)
  -- so each comes no later than the other
  have firstBefore := expand_program_first_of_address joltInstance.program trace.bytecode
    trace.expands accepted entry.val (getElem trace.rows 0 nonempty).rowIndex.val entry.isLt
    (getElem trace.rows 0 nonempty).rowIndex.isLt sameAddress.symm first.1
  have entryBefore := expand_program_first_of_address joltInstance.program trace.bytecode
    trace.expands accepted (getElem trace.rows 0 nonempty).rowIndex.val entry.val
    (getElem trace.rows 0 nonempty).rowIndex.isLt entry.isLt sameAddress entryIsStart
  apply honestWitness_bytecodeRaAtEntryEqOne params trace ramFits traceFits
    bytecodeDomain _ nonempty
  change (getElem trace.rows 0 nonempty).rowIndex.val + 1 = entry.val + 1
  omega

end JoltConstraints
