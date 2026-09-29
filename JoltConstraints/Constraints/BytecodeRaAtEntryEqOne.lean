import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.honest_witness
import JoltConstraints.ProgramLayout

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (53) in `constraints.md`:
At cycle zero, the full bytecode selector selects the supplied public entry slot.
The entry slot comes from preprocessing; it need not be slot 1.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L358-L378 -/
def bytecodeRaAtEntryEqOne {F : Type} [Field F] {params : WitnessParams}
    (entry : Fin (2 ^ params.logBytecodeK)) (witness : WitnessType F params) : Prop :=
  bytecodeRa witness entry ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1

/-- Completeness target for the honest witness.
Trace linkage alone does not select the first instruction. startsAtEntry
connects the first executed row to the public entry slot. -/
theorem honestWitness_bytecodeRaAtEntryEqOne
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (entry : Fin (2 ^ params.logBytecodeK))
    (nonempty : 0 < trace.rows.size)
    (startsAtEntry : (getElem trace.rows 0 nonempty).rowIndex.val + 1 = entry.val)
    : bytecodeRaAtEntryEqOne entry
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  unfold bytecodeRaAtEntryEqOne bytecodeRa
  apply Finset.prod_eq_one
  intro chunk _
  dsimp [JoltProgram.honestWitness, HonestWitness.BytecodeRaChunk,
    HonestWitness.addressChunkEntry, bytecodeAddressChunk,
    HonestWitness.addressChunk]
  simp [HonestWitness.bytecodePc, nonempty, startsAtEntry]

/-- Constraint (53) from the public entry address, rather than an assumed
equality with the first trace row's bytecode slot. An entry row at the initial
PC is unique by the program's address/count layout. The witness slot is one
greater than the program index because preprocessing prepends the no-op.

Rust revision `3cb4e24361ae2006e9713ae65d58a3fa51fd0518`:
`crates/jolt-program/src/preprocess/bytecode.rs::entry_bytecode_index` calls
`BytecodePCMapper::get_first_pc(entry_address)` to select this row. -/
theorem honestWitness_bytecodeRaAtEntryEqOne_of_address
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (entry : Fin program.expandedBytecode.size)
    (entryIsStart : program.expandedBytecode[entry].isEntry)
    (entryAddress : program.initialState.sail.regs.get? Register.PC =
      some program.expandedBytecode[entry].address)
    (nonempty : 0 < trace.rows.size) :
    bytecodeRaAtEntryEqOne
      ⟨entry.val + 1, by have := bytecodeDomain.rowsFit; omega⟩
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  have first := trace.startsAtEntry nonempty
  have same := trace.sequenceLayout.entry_address_unique
    (getElem trace.rows 0 nonempty).rowIndex entry first.1 entryIsStart
    (Option.some.inj (first.2.symm.trans entryAddress))
  apply honestWitness_bytecodeRaAtEntryEqOne params trace ramFits traceFits
    bytecodeDomain _ nonempty
  change (getElem trace.rows 0 nonempty).rowIndex.val + 1 = entry.val + 1
  rw [same]

end JoltConstraints
