import JoltConstraints.theorems.Soundness.Layer5.TapeTrace

open LeanRV64D

/-! Execution-prefix readiness and the address checks derived for selected memory rows.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::assert_effective_address`).
The selected-row proof derives these checks from the protected RAM constraints;
there is no universal tracer-address restriction. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- The prefix uses honest internal runtime advice, has not continued past a
halt, and is about to attempt `next` in `pre`. The row need not succeed.
The boundary cases follow the entry and linkage rules of UntrustedAnswerRun.
The stopping rule follows `Cpu::halt` at ff6fc6568. -/
structure UntrustedAnswerRun.NextStep
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) : Prop where
  honestRuntimeAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  noEarlierStop : ∀ (i : Nat) (current following : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some following →
    ¬ current.Halts
  ready :
    match run.rows.back? with
    | none =>
      run.bytecode[next].address = joltInstance.program.entry_address ∧
      run.bytecode[next].starts_source ∧
      pre = advance_pc joltInstance.program.entry_address
        (source_is_compressed run.bytecode next) run.initialState
    | some last =>
      if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0 then
        next.val = last.rowIndex.val + 1 ∧ pre = last.postState
      else
        ∃ address, last.postState.sail.regs.get? Register.nextPC = some address ∧
          ¬ last.Halts ∧
          run.bytecode[next].address = address ∧
          run.bytecode[next].starts_source ∧
          pre = advance_pc address (source_is_compressed run.bytecode next) last.postState

/-- The address assertions used by Mmu.load_doubleword and Mmu.store_doubleword.
RAM checks only the starting address; device memory checks each of eight bytes.
Checking all eight RAM bytes would strengthen Jolt's rule at an unaligned
heap or canary boundary. This predicate does not assume execution succeeds.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs`
(`Mmu::load_doubleword_raw`, `Mmu::store_doubleword_raw`). -/
def DoublewordAddressChecks (device : JoltDevice) (address : BitVec 64)
    (isWrite : Bool) : Prop :=
  if RAM_START_ADDRESS ≤ address.toNat then
    Mmu.effective_address_ok device address.toNat isWrite = true
  else
    ∀ offset < 8, Mmu.effective_address_ok device (address.toNat + offset) isWrite = true

end JoltConstraints.Soundness
