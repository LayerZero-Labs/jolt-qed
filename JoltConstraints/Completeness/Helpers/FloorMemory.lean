import JoltConstraints.Completeness.Helpers.JumpReturnProofHelpers
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions
open JoltISA

namespace JoltConstraints

/-- Successful retirement after an alignment guard supplies both its zero-bit
check and the continuation at the captured address; mask 1 checks halfwords.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`)
at `c6703570`. -/
private theorem floor_access_guard (base : Src) (imm mask : BitVec 64)
    (fault : ExceptionType) (next : BitVec 64 → JoltMonad ExecutionResult)
    (pre post : SailJoltState)
    (runs : (do
      let value ← readSrc base
      let ea := value + imm
      if ea &&& mask = 0 then next ea
      else pure (.Memory_Exception (virtaddr.Virtaddr ea, fault))) pre =
        .ok (.Retire_Success ()) post) :
    (sourceValue base pre + imm) &&& mask = 0 ∧
      next (sourceValue base pre + imm) pre = .ok (.Retire_Success ()) post := by
  have step := lookup_read_bind base _ _ _ _ runs
  split at step
  · exact ⟨by assumption, step⟩
  · cases step

/-- A floor load retires only after its natural-alignment check and the
containing doubleword load; for example H checks bit zero and reads `ea & ~7`.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`, `addresses`)
at `c6703570`. -/
theorem floor_load_access (instruction : Instr) (faultClass : LoadFaultClass)
    (dst : Dst) (base : Src) (imm mask : BitVec 64) (fault : ExceptionType)
    (selected : (instruction = .VirtualLoadB faultClass dst base imm fault ∧ mask = 0) ∨
      (instruction = .VirtualLoadH faultClass dst base imm fault ∧ mask = 1) ∨
      (instruction = .VirtualLoadW faultClass dst base imm fault ∧ mask = 3))
    (advice : instruction.RuntimeAdvice) (pre post : SailJoltState)
    (runs : execInstr (instruction.withRuntimeAdvice advice) pre = .ok (.Retire_Success ()) post) :
    (sourceValue base pre + imm) &&& mask = 0 ∧
      (do
        match ← Mmu.load_doubleword ((sourceValue base pre + imm) &&& ~~~7) with
        | .Ok word => writeDst dst word; pure RETIRE_SUCCESS
        | .Err error => pure error) pre = .ok (.Retire_Success ()) post := by
  apply floor_access_guard base imm mask fault
    (fun ea => do
      match ← Mmu.load_doubleword (ea &&& ~~~7) with
      | .Ok word => writeDst dst word; pure RETIRE_SUCCESS
      | .Err error => pure error) pre post
  rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simpa only [Instr.withRuntimeAdvice, execInstr, show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, ↓reduceIte] using runs

/-- A floor store checks alignment then writes its captured second source to
the containing doubleword; for example W checks bits zero and one.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`, `addresses`)
at `c6703570`. -/
theorem floor_store_access (instruction : Instr) (base value : Src)
    (imm mask : BitVec 64) (fault : ExceptionType)
    (selected : (instruction = .VirtualStoreB base value imm fault ∧ mask = 0) ∨
      (instruction = .VirtualStoreH base value imm fault ∧ mask = 1) ∨
      (instruction = .VirtualStoreW base value imm fault ∧ mask = 3))
    (advice : instruction.RuntimeAdvice) (pre post : SailJoltState)
    (runs : execInstr (instruction.withRuntimeAdvice advice) pre = .ok (.Retire_Success ()) post) :
    (sourceValue base pre + imm) &&& mask = 0 ∧
      (do
        match ← Mmu.store_doubleword ((sourceValue base pre + imm) &&& ~~~7)
            (sourceValue value pre) with
        | .Ok _ => pure RETIRE_SUCCESS
        | .Err error => pure error) pre = .ok (.Retire_Success ()) post := by
  have guarded := floor_access_guard base imm mask fault
    (fun ea => do
      let word ← readSrc value
      match ← Mmu.store_doubleword (ea &&& ~~~7) word with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err error => pure error) pre post
  have guardedRun := guarded (by
    rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simpa only [Instr.withRuntimeAdvice, execInstr, show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, ↓reduceIte] using runs)
  exact ⟨guardedRun.1, lookup_read_bind value _ _ _ _ guardedRun.2⟩

/-- The recorded floor address is the containing doubleword when the natural
alignment bits vanish; for example `ea = 10`, mask 1 and offset mask 6 give 8.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`addresses`)
at `c6703570`. -/
theorem floor_recorded_address (ea mask offset : BitVec 64)
    (partition : mask ||| offset = 7) (aligned : ea &&& mask = 0) :
    ea - (ea &&& offset) = ea &&& ~~~7 := by
  have low : ea &&& 7 = ea &&& offset := by
    rw [← partition, BitVec.and_or_distrib_left, aligned]
    exact BitVec.zero_or
  have parts := write_addr_split_aligned_offset ea
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at parts
  rw [← low]
  calc
    ea - (ea &&& 7) = (ea &&& (-8 : BitVec 64)) + (ea &&& 7) - (ea &&& 7) :=
      congrArg (fun value => value - (ea &&& 7)) parts.symm
    _ = ea &&& ~~~7 := BitVec.add_sub_cancel _ _

end JoltConstraints
