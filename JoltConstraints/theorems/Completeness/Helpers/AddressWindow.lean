import JoltConstraints.theorems.MemoryRowExecution
import JoltConstraints.theorems.MemoryExpansionFacts
import JoltConstraints.theorems.Completeness.Helpers.RamReadSelection
import JoltConstraints.theorems.Completeness.Helpers.RegistersValProofHelpers
import JoltConstraints.theorems.layout_facts
import JoltConstraints.theorems.trace_interface
import JoltConstraints.theorems.Completeness.Helpers.AddressSum
import JoltConstraints.translation.witness_helpers.lookup_output

/-!
Retired memory rows never wrap their effective address.
The tracer only accepts effective addresses in a window between `0x40000000` and
`2^63 + 2^31`, while every memory offset is a sign-extended 12-bit value. So the
integer sum `base + imm` of a retired load or store lies in `[0, 2^64)`, and the
64-bit sum equals the integer sum.
For example, `LD x1, -8(x2)` with `x2 = 4` would need the wrapped address
`2^64 - 4`, which lies above the window, so no honest trace retires it.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`assert_effective_address`) and
`crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow`).
-/

open LeanRV64D JoltISA
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D.Functions

set_option autoImplicit false

namespace JoltConstraints

open Soundness MemoryExpansionFacts

/-- The lowest address of a layout lies at or below both advice starts.
For example, with trusted advice at `0x7fff0000` and untrusted advice at
`0x7ffe0000`, the lowest address is `0x7ffe0000`. -/
theorem lowest_le_advice_starts (layout : MemoryLayout) :
    layout.get_lowest_address.toNat ≤ layout.trusted_advice_start.toNat ∧
      layout.get_lowest_address.toNat ≤ layout.untrusted_advice_start.toNat := by
  unfold MemoryLayout.get_lowest_address
  split <;> omega

/-- Every readable device address lies at or above the layout's lowest address.
For example, an input byte lies above the advice regions, which start at the
lowest address. -/
theorem JoltDevice.lowest_le_of_readable (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout) (address : Nat)
    (readable : device.readable address = true) :
    device.memory_layout.get_lowest_address.toNat ≤ address := by
  obtain ⟨inputAbove, outputAbove, outputEndAbove, ioEndEq, _⟩ :=
    new_io_ordered config device.memory_layout built
  have ioEnd := congrArg BitVec.toNat ioEndEq
  have starts := lowest_le_advice_starts device.memory_layout
  simp only [JoltDevice.readable, JoltDevice.is_input, JoltDevice.is_trusted_advice,
    JoltDevice.is_untrusted_advice, JoltDevice.is_output, JoltDevice.is_io_gap,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at readable
  omega

/-- A power of two whose eight-fold is below `2^64` has eight-fold at most `2^63`.
For example, `8 * 2^60 = 2^63`. -/
private theorem eight_pow_le (j : Nat) (fits : 8 * 2 ^ j < 18446744073709551616) :
    8 * 2 ^ j ≤ 9223372036854775808 := by
  rcases Nat.lt_or_ge j 61 with small | large
  · have bound : 2 ^ j ≤ 2 ^ 60 := Nat.pow_le_pow_right (by decide) (by omega)
    have sixty : (2 : Nat) ^ 60 = 1152921504606846976 := by norm_num
    omega
  · have bound : 2 ^ 61 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) large
    have sixtyOne : (2 : Nat) ^ 61 = 2305843009213693952 := by norm_num
    omega

/-- The arithmetic behind `ram_backing_end_le`.
For example, lowest `2^30` and eight-fold `2^63` give `2^31 + (2^30 + 2^63 - 2^31)`. -/
private theorem backing_arith (lowest ioEnd eightK : Nat) (lowestLe : lowest ≤ ioEnd)
    (ioEndBelow : ioEnd ≤ JoltISA.RAM_START_ADDRESS) (bound : eightK ≤ 9223372036854775808) :
    JoltISA.RAM_START_ADDRESS + (lowest + eightK - JoltISA.RAM_START_ADDRESS) ≤
      0x8000000080000000 := by
  simp only [JoltISA.RAM_START_ADDRESS] at ioEndBelow ⊢
  omega

/-- The RAM backing of a built layout ends at or below `2^63 + 2^31`.
The backing ends at the lowest address plus `8 * k` bytes, where `k` is a power of
two and the end fits in 64 bits, so `8 * k ≤ 2^63`; the lowest address lies below
RAM, which starts at `2^31`.
For example, a layout with `k = 2^20` words ends its backing near `2^31 + 2^23`.
Jolt at ff6fc6568: `common/src/jolt_device.rs` (`MemoryLayout::ram_size`). -/
theorem ram_backing_end_le (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout) :
    Mmu.ram_backing_end device ≤ 0x8000000080000000 := by
  obtain ⟨k, checked⟩ := Option.isSome_iff_exists.mp
    (new_max_ram_k config device.memory_layout built)
  obtain ⟨_, _, words, fits⟩ := max_ram_k_spec device.memory_layout k checked
  obtain ⟨inputAbove, outputAbove, outputEndAbove, ioEndEq, ioEndBelow⟩ :=
    new_io_ordered config device.memory_layout built
  have ioEnd := congrArg BitVec.toNat ioEndEq
  have lowestAbove := new_lowest_address_ge_half_ram config device.memory_layout built
  obtain ⟨j, power⟩ := Nat.isPowerOfTwo_nextPowerOfTwo
    ((device.memory_layout.heap_end.toNat - device.memory_layout.get_lowest_address.toNat) / 8)
  rw [← words] at power
  subst power
  have sixtyFour : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [sixtyFour] at fits
  have bound := eight_pow_le j (by omega)
  -- Rewrite step by step: closing these equations by `rfl` makes the kernel
  -- unfold `Nat.sub` against the literal RAM start.
  have mapped : (device.memory_layout.max_ram_k?.map fun words =>
      device.memory_layout.get_lowest_address.toNat + 8 * words - JoltISA.RAM_START_ADDRESS) =
      some (device.memory_layout.get_lowest_address.toNat + 8 * 2 ^ j -
        JoltISA.RAM_START_ADDRESS) := by
    rw [checked]
    rfl
  have size : device.memory_layout.ram_size =
      device.memory_layout.get_lowest_address.toNat + 8 * 2 ^ j - JoltISA.RAM_START_ADDRESS := by
    rw [MemoryLayout.ram_size, mapped, Option.getD_some]
  have backing : Mmu.ram_backing_end device =
      JoltISA.RAM_START_ADDRESS + device.memory_layout.ram_size := rfl
  rw [backing, size]
  exact backing_arith _ _ _ (by omega) ioEndBelow bound

/-- An effective address that passes the tracer's address check lies in the
window `[0x40000000, 2^63 + 2^31)`.
For example, an I/O-gap byte at `0x7ffffff8` and a heap byte at `0x80001000`
both pass and lie in the window.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`assert_effective_address`). -/
theorem Mmu.effective_address_window (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout) (ea : Nat) (isWrite : Bool)
    (ok : Mmu.effective_address_ok device ea isWrite = true) :
    0x40000000 ≤ ea ∧ ea < 0x8000000080000000 := by
  have lowestAbove := new_lowest_address_ge_half_ram config device.memory_layout built
  have backing := ram_backing_end_le device config built
  unfold Mmu.effective_address_ok at ok
  split at ok
  · rename_i below
    have lower := JoltDevice.lowest_le_of_readable device config built ea ok
    simp only [JoltISA.RAM_START_ADDRESS] at below
    omega
  · rename_i above
    simp only [decide_eq_true_eq] at ok
    simp only [JoltISA.RAM_START_ADDRESS] at above
    omega

/-- A doubleword load that returns passed the address check at its address.
For example, a load at an unmapped address below the advice regions fails.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`load_doubleword`). -/
theorem Mmu.load_doubleword_effective_ok (address : BitVec 64) (state middle : SailJoltState)
    (result : Result (BitVec 64) ExecutionResult)
    (loaded : Mmu.load_doubleword address state = .ok result middle) :
    Mmu.effective_address_ok state.jolt_device address.toNat false = true := by
  cases ok : Mmu.effective_address_ok state.jolt_device address.toNat false
  · exfalso
    unfold Mmu.load_doubleword at loaded
    dsimp only at loaded
    split at loaded
    · cases loaded
    · split at loaded
      · rw [ok] at loaded
        cases loaded
      · have firstByte : Mmu.load_raw? state address.toNat = none := by
          simp [Mmu.load_raw?, ok]
        simp [read_doubleword?, firstByte] at loaded
  · rfl

/-- A doubleword store that returns passed the address check at its address.
For example, a store above the RAM backing fails.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`store_doubleword`). -/
theorem Mmu.store_doubleword_effective_ok (address value : BitVec 64)
    (state post : SailJoltState) (result : Result Bool ExecutionResult)
    (stored : Mmu.store_doubleword address value state = .ok result post) :
    Mmu.effective_address_ok state.jolt_device address.toNat true = true := by
  cases ok : Mmu.effective_address_ok state.jolt_device address.toNat true
  · exfalso
    unfold Mmu.store_doubleword at stored
    dsimp only at stored
    split at stored
    · cases stored
    · split at stored
      · simp only [ok, Bool.false_and] at stored
        cases stored
      · have firstByte : Mmu.store_raw? state address.toNat (value.extractLsb' 0 8) = none := by
          simp [Mmu.store_raw?, ok]
        have range : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
        simp only [range, List.foldl_cons, List.foldl_nil, Option.bind_some, Nat.add_zero,
          Nat.mul_zero, firstByte, Option.bind_none] at stored
        cases stored
  · rfl

/-- The accessed doubleword of a row lies in the seven bytes below its effective
address. For example, a halfword row at `ea = 13` accesses 8.
Jolt at ff6fc6568: `tracer/src/instruction/floor_access.rs` (`load`, `store`). -/
theorem Soundness.MemoryWidth.accessed_bounds (width : MemoryWidth) (ea : BitVec 64) :
    (width.accessed ea).toNat ≤ ea.toNat ∧ ea.toNat ≤ (width.accessed ea).toNat + 7 := by
  cases width
  · simp [MemoryWidth.accessed]
  all_goals
    have same := MemoryWidth.recorded_eq_accessed .byte ea (by simp [MemoryWidth.alignMask])
    have value := MemoryWidth.recorded_toNat .byte ea
    rw [same] at value
    simp only [MemoryWidth.accessed, MemoryWidth.offsetMask] at value ⊢
    rw [show (7 : BitVec 64).toNat = 7 from rfl] at value
    have small : ea.toNat &&& 7 ≤ 7 := Nat.and_le_right
    have le : ea.toNat &&& 7 ≤ ea.toNat := Nat.and_le_left
    omega

/-- A small offset whose 64-bit sum lands within seven bytes above an address in
the window does not wrap: the integer sum lies in `[0, 2^64)`.
For example, base `2^64 - 4` with offset 8 wraps to 4, which lies below the window.
-/
theorem noWrap_of_window (base imm accessed : BitVec 64) (small : smallImm imm = true)
    (lower : accessed.toNat ≤ (base + imm).toNat) (upper : (base + imm).toNat ≤ accessed.toNat + 7)
    (window : 0x40000000 ≤ accessed.toNat ∧ accessed.toNat < 0x8000000080000000) :
    0 ≤ (base.toNat : Int) + imm.toInt ∧ (base.toNat : Int) + imm.toInt < 2 ^ 64 := by
  simp only [smallImm, Bool.and_eq_true, decide_eq_true_eq] at small
  rw [BitVec.toNat_add] at lower upper
  have baseLt := base.isLt
  have immLt := imm.isLt
  have cond := BitVec.toInt_eq_toNat_cond imm
  norm_num at lower upper baseLt immLt cond ⊢
  split at cond <;> rw [cond] at small ⊢ <;> omega

/-- Every memory operand pair of an access row is its `accessOperands?` result.
For example, `SD x2 x3 8` gives `(x2, 8)`. -/
theorem Soundness.AccessRow.accessOperands {instruction : Instr} {width : MemoryWidth} {base : Src}
    {imm : BitVec 64} (row : AccessRow instruction width base imm) :
    accessOperands? instruction = some (base, imm) := by
  rcases row with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases width <;> rfl

/-- A floor store's operands give an access row with that base and offset.
For example, `VirtualStoreW x2 v40 4 fault` is a word access row with base x2. -/
theorem access_of_floorStoreOperands {instruction : Instr} {base : Src} {imm : BitVec 64}
    (operands : floorStoreOperands? instruction = some (base, imm)) :
    ∃ width, AccessRow instruction width base imm := by
  cases instruction <;> simp only [floorStoreOperands?, reduceCtorEq] at operands
  all_goals
    simp only [Option.some.injEq, Prod.mk.injEq] at operands
    obtain ⟨rfl, rfl⟩ := operands
  · exact ⟨.byte, Or.inr ⟨_, _, rfl⟩⟩
  · exact ⟨.halfword, Or.inr ⟨_, _, rfl⟩⟩
  · exact ⟨.word, Or.inr ⟨_, _, rfl⟩⟩

/-- No retired memory row wraps its effective address: the integer sum of its
base value and signed offset lies in `[0, 2^64)`.
For example, an `LD x1, -8(x2)` row that retires has `x2 ≥ 8`.
Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`assert_effective_address`). -/
theorem _root_.HonestTrace.access_noWrap {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (inside : n < trace.rows.size) {width : MemoryWidth} {base : Src}
    {imm : BitVec 64}
    (access : AccessRow trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction
      width base imm) :
    0 ≤ ((sourceValue base (trace.rows[n]'inside).preState).toNat : Int) + imm.toInt ∧
      ((sourceValue base (trace.rows[n]'inside).preState).toNat : Int) + imm.toInt < 2 ^ 64 := by
  obtain ⟨config, built, _⟩ := trace.preState_layout n inside
  have small : smallImm imm = true := by
    have ok := expand_program_rowImmOk joltInstance.program trace.bytecode trace.expands
      trace.bytecode[(trace.rows[n]'inside).rowIndex] (by simp)
    simp only [rowImmOk, access.accessOperands, Bool.and_eq_true] at ok
    exact ok.1
  have bounds := width.accessed_bounds (sourceValue base (trace.rows[n]'inside).preState + imm)
  have runs := (trace.row n inside).executes
  have window : 0x40000000 ≤
      (width.accessed (sourceValue base (trace.rows[n]'inside).preState + imm)).toNat ∧
      (width.accessed (sourceValue base (trace.rows[n]'inside).preState + imm)).toNat <
        0x8000000080000000 := by
    rcases access with ⟨_, load⟩ | ⟨_, store⟩
    · obtain ⟨result, middle, loaded⟩ := load.load_of_run _ _ _ runs
      exact Mmu.effective_address_window _ config built _ _
        (Mmu.load_doubleword_effective_ok _ _ _ _ loaded)
    · have tapeRuns : execWithTapeAnswer
          (trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction.withRuntimeAdvice
            (trace.rows[n]'inside).runtimeAdvice) 0 (trace.rows[n]'inside).preState =
          .ok RETIRE_SUCCESS (trace.rows[n]'inside).postState := by
        rw [withRuntimeAdvice_eq_of_noAdvice _ (trace.rows[n]'inside).runtimeAdvice
            store.metadata.noAdvice,
          execWithTapeAnswer_of_ne _ 0 store.access.not_tape]
        rw [withRuntimeAdvice_eq_of_noAdvice _ (trace.rows[n]'inside).runtimeAdvice
          store.metadata.noAdvice] at runs
        exact runs
      obtain ⟨result, stored⟩ := store.store_of_run 0 _ _ _ tapeRuns
      exact Mmu.effective_address_window _ config built _ _
        (Mmu.store_doubleword_effective_ok _ _ _ _ _ stored)
  exact noWrap_of_window _ _ _ small bounds.1 bounds.2 window

/-- A row that is not a halt has a next row, since the trace ends at a halt.
For example, a ShiftData row is never the last row.
Jolt at ff6fc6568: `tracer/src/lib.rs` (`trace`). -/
theorem _root_.HonestTrace.next_exists {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (inside : n < trace.rows.size)
    (notHalt : trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction.haltKind?.isNone =
      true) :
    n + 1 < trace.rows.size := by
  by_contra last
  have isLast : n = trace.rows.size - 1 := by omega
  have back : trace.rows.back? = some (trace.rows[n]'inside) := by
    rw [Array.back?_eq_getElem?, ← isLast]
    exact Array.getElem?_eq_getElem inside
  have halts := trace.stops (trace.rows[n]'inside) back
  unfold TraceRow.Halts at halts
  rw [Option.isNone_iff_eq_none] at notHalt
  rw [notHalt] at halts
  cases halts

/-- A row that writes only a virtual register keeps every architectural register.
For example, `ADD v40 v40 v41` keeps x2.
Jolt at ff6fc6568: `tracer/src/instruction/mod.rs` (`RISCVInstruction::execute`). -/
theorem _root_.HonestTrace.xreg_kept {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (n : Nat) (inside : n < trace.rows.size) (register : regidx)
    (writes : writesVRegOnly trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction = true) :
    sourceValue (.xreg register) (trace.rows[n]'inside).postState =
      sourceValue (.xreg register) (trace.rows[n]'inside).preState := by
  apply register42_instruction_preserves_other
    (trace.bytecode[(trace.rows[n]'inside).rowIndex].instruction.withRuntimeAdvice
      (trace.rows[n]'inside).runtimeAdvice)
  · intro dst written
    rw [register42_destination_withRuntimeAdvice] at written
    simp only [writesVRegOnly, written, Bool.and_eq_true] at writes
    cases dst with
    | xreg _ => exact absurd writes.1 (by simp)
    | vreg _ => simp [register42_dstAsSrc]
  · exact (trace.rowAssumptions ⟨n, inside⟩).xRegReadable
  · exact (trace.row n inside).executes

/-- Every ShiftData row is followed, two rows later, by a floor store with the same
architectural base and offset, which reads the same base value.
For example, `ShiftDataW v41 x3 x2 4` at row `t` is followed by `ADD v40 v40 v41`
and `StoreW x2 v40 4`, and x2 is unchanged at row `t + 2`.
Jolt at ff6fc6568: `crates/jolt-program/src/expand/memory/shared.rs` (`expand_narrow_store`). -/
theorem _root_.HonestTrace.shiftData_store {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Nat) (inside : t < trace.rows.size) {address : Src} {imm : BitVec 64}
    (shift : shiftDataOperands? trace.bytecode[(trace.rows[t]'inside).rowIndex].instruction =
      some (address, imm)) :
    ∃ later : t + 2 < trace.rows.size, ∃ width,
      AccessRow trace.bytecode[(trace.rows[t + 2]'later).rowIndex].instruction width address imm ∧
      sourceValue address (trace.rows[t + 2]'later).preState =
        sourceValue address (trace.rows[t]'inside).preState := by
  let index := (trace.rows[t]'inside).rowIndex
  obtain ⟨next, related⟩ := expand_program_triples joltInstance.program trace.bytecode
    trace.expands index.val (by simp) (by
      simp only [Array.getElem_toList]
      change (shiftDataOperands? trace.bytecode[index].instruction).isSome = true
      simp only [index, shift, Option.isSome_some])
  simp only [Array.getElem_toList] at related
  obtain ⟨triple, firstContinues, secondContinues⟩ := related
  simp only [Array.length_toList] at next
  have firstIs : trace.bytecode[index.val] = trace.bytecode[index] := rfl
  cases third : floorStoreOperands? (trace.bytecode[index.val + 2]'(by simpa using next)).instruction with
  | none =>
    simp only [shiftDataTripleOk, firstIs, index, shift, third] at triple
    cases triple
  | some operands =>
    obtain ⟨base, offset⟩ := operands
    simp only [shiftDataTripleOk, firstIs, index, shift, third, Bool.and_eq_true,
      beq_iff_eq] at triple
    obtain ⟨⟨⟨sameBase, sameImm⟩, firstWrites⟩, secondWrites⟩ := triple
    obtain ⟨rfl, register, rfl⟩ := sameXReg_eq sameBase
    subst sameImm
    -- The second row runs bytecode row `index + 1`.
    have firstNotHalt : trace.bytecode[(trace.rows[t]'inside).rowIndex].instruction.haltKind?.isNone =
        true := by
      simp only [writesVRegOnly, Bool.and_eq_true] at firstWrites
      exact firstWrites.2
    have secondExists := trace.next_exists t inside firstNotHalt
    have firstCont : trace.bytecode[(trace.rows[t]'inside).rowIndex].continues = true :=
      firstContinues
    have secondIndex := trace.successor t inside secondExists
    rw [ite_eq_left firstCont] at secondIndex
    have secondPre := trace.linkedState t inside secondExists
    rw [ite_eq_left firstCont] at secondPre
    have secondRow : trace.bytecode[(trace.rows[t + 1]'secondExists).rowIndex] =
        trace.bytecode[index.val + 1]'(by omega) := by
      simp only [Fin.getElem_fin, secondIndex, index]
    -- The third row runs bytecode row `index + 2`.
    have secondNotHalt :
        trace.bytecode[(trace.rows[t + 1]'secondExists).rowIndex].instruction.haltKind?.isNone =
          true := by
      rw [secondRow]
      simp only [writesVRegOnly, Bool.and_eq_true] at secondWrites
      exact secondWrites.2
    have thirdExists := trace.next_exists (t + 1) secondExists secondNotHalt
    have secondCont : trace.bytecode[(trace.rows[t + 1]'secondExists).rowIndex].continues = true := by
      rw [secondRow]
      exact secondContinues
    have thirdIndex := trace.successor (t + 1) secondExists thirdExists
    rw [ite_eq_left secondCont] at thirdIndex
    have thirdPre := trace.linkedState (t + 1) secondExists thirdExists
    rw [ite_eq_left secondCont] at thirdPre
    have thirdRow : trace.bytecode[(trace.rows[t + 1 + 1]'thirdExists).rowIndex] =
        trace.bytecode[index.val + 2]'(by simpa using next) := by
      simp only [Fin.getElem_fin, thirdIndex, secondIndex, index]
    obtain ⟨width, access⟩ := access_of_floorStoreOperands third
    refine ⟨thirdExists, width, by rw [thirdRow]; exact access, ?_⟩
    have keptFirst := trace.xreg_kept t inside register firstWrites
    have keptSecond := trace.xreg_kept (t + 1) secondExists register (by rw [secondRow]; exact secondWrites)
    rw [thirdPre, keptSecond, secondPre, keptFirst]

/-- A 64-bit sum that does not wrap casts to the field sum of its unsigned base and
signed offset. For example, base 10 and offset -2 give 8 in both readings. -/
theorem add_toNat_cast_of_noWrap {F : Type} [Field F] (base imm : BitVec 64)
    (nonneg : 0 ≤ (base.toNat : Int) + imm.toInt) (below : (base.toNat : Int) + imm.toInt < 2 ^ 64) :
    ((base + imm).toNat : F) = (base.toNat : F) + (imm.toInt : F) := by
  have cast := encodedInt_cast (F := F) 64 _ nonneg below
  simpa only [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.ofInt_toInt, BitVec.setWidth_eq, Int.cast_add, Int.cast_natCast] using cast

/-- An access row's lookup output is its effective address masked by the width's
offset mask, which is zero for LD and SD.
For example, a halfword row at `ea = 10` outputs `10 &&& 6 = 2`.
Jolt at ff6fc6568: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
(`floor_access!`). -/
theorem Soundness.AccessRow.rowLookupOutput {bytecode : Array JoltInstructionRow}
    (row : TraceRow bytecode) {width : MemoryWidth} {base : Src} {imm : BitVec 64}
    (access : AccessRow bytecode[row.rowIndex].instruction width base imm) :
    TraceWitness.rowLookupOutput row =
      (sourceValue base row.preState + imm) &&& width.offsetMask := by
  simp only [Fin.getElem_fin] at access
  rcases access with ⟨_, _, _, same⟩ | ⟨_, _, same⟩ <;>
    cases width <;>
    simp [TraceWitness.rowLookupOutput, same, MemoryWidth.load, MemoryWidth.store,
      MemoryWidth.offsetMask]

end JoltConstraints
