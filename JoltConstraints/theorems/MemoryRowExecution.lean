import JoltConstraints.theorems.SharedMemoryExecution
import JoltConstraints.theorems.Completeness.Helpers.FloorMemory
import JoltConstraints.theorems.Completeness.Helpers.RegistersReadProofHelpers
import JoltConstraints.theorems.Soundness.Layer5.TapeSemantics
import JoltConstraints.theorems.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.theorems.expansion_temp_liveness

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- The width class of a memory row.
`double` is a native LD or SD, which accesses the eight bytes at its effective
address; `byte`, `halfword` and `word` are the floor rows VirtualLoadB/H/W and
VirtualStoreB/H/W, which access the containing doubleword.
For example, an LH source instruction expands to a `halfword` floor load. -/
inductive MemoryWidth where
  | double | byte | halfword | word

namespace MemoryWidth

/-- The doubleword accessed at effective address `ea`: `ea` itself for a native
row and `ea &&& ~~~7` for a floor row.
For example, a halfword row at `ea = 10` accesses 8, and SD at 16 accesses 16. -/
def accessed : MemoryWidth → BitVec 64 → BitVec 64
  | .double, ea => ea
  | .byte, ea | .halfword, ea | .word, ea => ea &&& ~~~7

/-- The low effective-address bits that must vanish for the row to execute:
7 for a native doubleword, and 0, 1 and 3 for floor byte, halfword and word rows.
For example, a word row at `ea = 12` passes, since `12 &&& 3 = 0`. -/
def alignMask : MemoryWidth → BitVec 64
  | .double => 7
  | .byte => 0
  | .halfword => 1
  | .word => 3

/-- The mask of the lookup offset that constraint (01) subtracts from `ea`:
zero for a native row (no lookup table), and 7, 6 and 4 for the AddressOffsetB,
AddressOffsetH and AddressOffsetW tables of floor rows.
For example, a halfword row at `ea = 10` subtracts `10 &&& 6 = 2`. -/
def offsetMask : MemoryWidth → BitVec 64
  | .double => 0
  | .byte => 7
  | .halfword => 6
  | .word => 4

/-- The RAM address recorded for a row of this width at `ea`:
`ea - (ea &&& offsetMask)`, as in `TraceWitness.ramAccessAddress`.
For example, a word row at `ea = 13` records 9, which no RAM word can select. -/
def recorded (width : MemoryWidth) (ea : BitVec 64) : BitVec 64 :=
  ea - (ea &&& width.offsetMask)

/-- The lookup table selected by a row of this width: none for native rows and
AddressOffsetB/H/W for floor rows.
For example, a byte floor store selects AddressOffsetB. -/
def table? : MemoryWidth → Option LookupTableKind
  | .double => none
  | .byte => some .AddressOffsetB
  | .halfword => some .AddressOffsetH
  | .word => some .AddressOffsetW

/-- If `sum = base + (sum &&& offset)` with `base` a multiple of 8 and `offset`
and `mask` disjoint masks below 8, then `sum &&& mask = 0`.
For example, `10 = 8 + (10 &&& 6)` gives `10 &&& 1 = 0`. -/
private theorem low_bits_zero (sum base offset mask : Nat)
    (split : sum = base + (sum &&& offset)) (aligned : base % 8 = 0)
    (offsetSmall : offset < 8) (maskSmall : mask < 8) (disjoint : offset &&& mask = 0) :
    sum &&& mask = 0 := by
  have small : sum &&& offset < 8 := lt_of_le_of_lt Nat.and_le_right offsetSmall
  have low : sum % 8 = sum &&& offset := by omega
  have maskLow : sum &&& mask = (sum % 8) &&& mask := by
    have reduced := Nat.and_mod_two_pow (a := sum) (b := mask) (n := 3)
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right (by simpa using maskSmall)),
      Nat.mod_eq_of_lt (show mask < 2 ^ 3 by simpa using maskSmall)] at reduced
    simpa using reduced
  rw [maskLow, low, Nat.land_assoc, disjoint, Nat.and_zero]

/-- The recorded address's value is `ea` minus its masked offset, with no wrap.
For example, a halfword row at `ea = 10` records value `10 - 2`. -/
theorem recorded_toNat (width : MemoryWidth) (ea : BitVec 64) :
    (width.recorded ea).toNat = ea.toNat - (ea.toNat &&& width.offsetMask.toNat) := by
  have le : ea &&& width.offsetMask ≤ ea := by
    rw [BitVec.le_def, BitVec.toNat_and]
    exact Nat.and_le_left
  rw [recorded, BitVec.toNat_sub_of_le le, BitVec.toNat_and]

/-- A recorded address that is a multiple of 8 forces the row's natural
alignment. For example, a word row at `ea = 13` records 9, so no such row with
an eight-byte-aligned RAM address has `ea = 13`. -/
theorem aligned_of_recorded (width : MemoryWidth) (ea : BitVec 64)
    (recordedAligned : (width.recorded ea).toNat % 8 = 0) :
    ea &&& width.alignMask = 0 := by
  have split : ea.toNat = (width.recorded ea).toNat + (ea.toNat &&& width.offsetMask.toNat) := by
    rw [recorded_toNat]
    have := Nat.and_le_left (n := ea.toNat) (m := width.offsetMask.toNat)
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and]
  cases width <;>
    exact low_bits_zero _ _ _ _ split recordedAligned (by decide) (by decide) (by decide)

/-- At a naturally aligned effective address, the recorded address is the
accessed doubleword. For example, a halfword row at `ea = 10` records and
accesses 8. -/
theorem recorded_eq_accessed (width : MemoryWidth) (ea : BitVec 64)
    (aligned : ea &&& width.alignMask = 0) :
    width.recorded ea = width.accessed ea := by
  cases width
  · simp [recorded, offsetMask, accessed]
  · exact floor_recorded_address ea 0 7 (by decide) aligned
  · exact floor_recorded_address ea 1 6 (by decide) aligned
  · exact floor_recorded_address ea 3 4 (by decide) aligned

/-- The load row of this width: LD for `double` and VirtualLoadB/H/W for the
floor widths, with load fault class `faultClass`, destination `destination`,
base `base`, offset `imm` and alignment exception `fault`.
LD has no `fault` field, so it ignores it.
For example, `halfword.load .normal dst base 2 fault` is
`.VirtualLoadH .normal dst base 2 fault`. -/
def load (width : MemoryWidth) (faultClass : LoadFaultClass) (destination : Dst)
    (base : Src) (imm : BitVec 64) (fault : ExceptionType) : Instr :=
  match width with
  | .double => .LD faultClass destination base imm
  | .byte => .VirtualLoadB faultClass destination base imm fault
  | .halfword => .VirtualLoadH faultClass destination base imm fault
  | .word => .VirtualLoadW faultClass destination base imm fault

/-- The store row of this width: SD for `double` and VirtualStoreB/H/W for the
floor widths, with base `base`, stored source `value`, offset `imm` and
alignment exception `fault`. SD has no `fault` field, so it ignores it.
For example, `byte.store base value 3 fault` is `.VirtualStoreB base value 3 fault`. -/
def store (width : MemoryWidth) (base value : Src) (imm : BitVec 64)
    (fault : ExceptionType) : Instr :=
  match width with
  | .double => .SD base value imm
  | .byte => .VirtualStoreB base value imm fault
  | .halfword => .VirtualStoreH base value imm fault
  | .word => .VirtualStoreW base value imm fault

end MemoryWidth

/-- `instruction` is a load of class `width` that writes `destination` with the
doubleword it accesses at effective address `base + imm`.
For example, `.VirtualLoadH faultClass dst base 2 fault` is a `halfword` load row
for every load fault class and exception. -/
def LoadRow (instruction : Instr) (width : MemoryWidth) (destination : Dst)
    (base : Src) (imm : BitVec 64) : Prop :=
  ∃ faultClass fault, instruction = width.load faultClass destination base imm fault

/-- `instruction` is a store of class `width` that writes the value of `value`
to the doubleword it accesses at effective address `base + imm`.
For example, `.SD base value 8` is a `double` store row, and
`.VirtualStoreB base value 3 fault` is a `byte` store row. -/
def StoreRow (instruction : Instr) (width : MemoryWidth) (base value : Src)
    (imm : BitVec 64) : Prop :=
  ∃ fault, instruction = width.store base value imm fault

/-- `instruction` is a load or store row of class `width` with base `base` and
offset `imm`. For example, both LD and SD are `double` access rows. -/
def AccessRow (instruction : Instr) (width : MemoryWidth) (base : Src) (imm : BitVec 64) : Prop :=
  (∃ destination, LoadRow instruction width destination base imm) ∨
    ∃ value, StoreRow instruction width base value imm

/-- A load row is an access row. For example, LD is a `double` access row. -/
theorem LoadRow.access {instruction : Instr} {width : MemoryWidth} {destination : Dst}
    {base : Src} {imm : BitVec 64} (row : LoadRow instruction width destination base imm) :
    AccessRow instruction width base imm :=
  Or.inl ⟨destination, row⟩

/-- A store row is an access row. For example, VirtualStoreB is a `byte` access row. -/
theorem StoreRow.access {instruction : Instr} {width : MemoryWidth} {base value : Src}
    {imm : BitVec 64} (row : StoreRow instruction width base value imm) :
    AccessRow instruction width base imm :=
  Or.inr ⟨value, row⟩

/-- Every load-flagged instruction is a load row.
For example, a `VirtualLoadW` is the `word` load row with its own operands.
See `JoltMetadata.opcodeFlag_load_cases`. -/
theorem loadRow_of_flag (instruction : Instr)
    (flag : JoltMetadata.opcodeFlag instruction .Load = true) :
    ∃ width destination base imm, LoadRow instruction width destination base imm := by
  obtain ⟨faultClass, destination, base, imm, same⟩ :=
    JoltMetadata.opcodeFlag_load_cases instruction flag
  rcases same with same | ⟨fault, same | same | same⟩
  · exact ⟨.double, destination, base, imm, faultClass, ExceptionType.E_Load_Addr_Align (), same⟩
  · exact ⟨.byte, destination, base, imm, faultClass, fault, same⟩
  · exact ⟨.halfword, destination, base, imm, faultClass, fault, same⟩
  · exact ⟨.word, destination, base, imm, faultClass, fault, same⟩

/-- Every store-flagged instruction is a store row.
For example, an SD is the `double` store row with its own operands.
See `JoltMetadata.opcodeFlag_store_cases`. -/
theorem storeRow_of_flag (instruction : Instr)
    (flag : JoltMetadata.opcodeFlag instruction .Store = true) :
    ∃ width base value imm, StoreRow instruction width base value imm := by
  obtain ⟨base, value, imm, same⟩ := JoltMetadata.opcodeFlag_store_cases instruction flag
  rcases same with same | ⟨fault, same | same | same⟩
  · exact ⟨.double, base, value, imm, ExceptionType.E_SAMO_Addr_Align (), same⟩
  · exact ⟨.byte, base, value, imm, fault, same⟩
  · exact ⟨.halfword, base, value, imm, fault, same⟩
  · exact ⟨.word, base, value, imm, fault, same⟩

/-- An instruction with a recorded RAM address is one of the eight memory rows.
For example, a floor store has a byte, halfword or word access class. -/
theorem accessRow_of_address (instruction : Instr) (pre : SailJoltState)
    (address : BitVec 64) (recorded : TraceWitness.ramAccessAddress instruction pre = some address) :
    ∃ width base imm, AccessRow instruction width base imm := by
  unfold TraceWitness.ramAccessAddress at recorded
  split at recorded
  · rename_i _ faultClass destination base imm
    exact ⟨.double, base, imm, Or.inl ⟨destination, faultClass, .E_Load_Addr_Align (), rfl⟩⟩
  · rename_i _ base value imm
    exact ⟨.double, base, imm, Or.inr ⟨value, .E_SAMO_Addr_Align (), rfl⟩⟩
  · rename_i _ faultClass destination base imm fault
    exact ⟨.byte, base, imm, Or.inl ⟨destination, faultClass, fault, rfl⟩⟩
  · rename_i _ base value imm fault
    exact ⟨.byte, base, imm, Or.inr ⟨value, fault, rfl⟩⟩
  · rename_i _ faultClass destination base imm fault
    exact ⟨.halfword, base, imm, Or.inl ⟨destination, faultClass, fault, rfl⟩⟩
  · rename_i _ base value imm fault
    exact ⟨.halfword, base, imm, Or.inr ⟨value, fault, rfl⟩⟩
  · rename_i _ faultClass destination base imm fault
    exact ⟨.word, base, imm, Or.inl ⟨destination, faultClass, fault, rfl⟩⟩
  · rename_i _ base value imm fault
    exact ⟨.word, base, imm, Or.inr ⟨value, fault, rfl⟩⟩
  · cases recorded

/-- The fixed metadata of a load row: the Load flag without Store, its signed
immediate, its base as first source and no second source, its destination, the
width's lookup table, no runtime advice, its base as only read source, and its
canonicality condition.
For example, LD has no table and VirtualLoadB selects AddressOffsetB. -/
structure LoadRowFacts (instruction : Instr) (width : MemoryWidth) (destination : Dst)
    (base : Src) (imm : BitVec 64) : Prop where
  load : JoltMetadata.opcodeFlag instruction .Load = true
  notStore : JoltMetadata.opcodeFlag instruction .Store = false
  immediate : JoltMetadata.immediate instruction = imm.toInt
  rs1Register : bytecodeRs1Register instruction = some (TraceWitness.sourceRegisterAddress base)
  rs2Register : bytecodeRs2Register instruction = none
  rs1Operand : rs1Operand? instruction = some base
  rs2Operand : rs2Operand? instruction = none
  destinationIs : instruction.destination? = some destination
  table : JoltMetadata.lookupTable instruction = width.table?
  noAdvice : instruction.adviceValue? = none
  readSources : ExpansionTempLiveness.readSources instruction = [base]
  canonical : JoltRegisterEncoding.instructionIsCanonical instruction =
    (JoltRegisterEncoding.destinationIsCanonical destination &&
      JoltRegisterEncoding.sourceIsCanonical base)

/-- The fixed metadata of a store row: the Store flag without Load, its signed
immediate, its base and value as first and second sources, no destination, the
width's lookup table, no runtime advice, its base and value as read sources, and
its canonicality condition.
For example, SD has no table and VirtualStoreH selects AddressOffsetH. -/
structure StoreRowFacts (instruction : Instr) (width : MemoryWidth) (base value : Src)
    (imm : BitVec 64) : Prop where
  notLoad : JoltMetadata.opcodeFlag instruction .Load = false
  store : JoltMetadata.opcodeFlag instruction .Store = true
  immediate : JoltMetadata.immediate instruction = imm.toInt
  rs1Register : bytecodeRs1Register instruction = some (TraceWitness.sourceRegisterAddress base)
  rs2Register : bytecodeRs2Register instruction = some (TraceWitness.sourceRegisterAddress value)
  rs1Operand : rs1Operand? instruction = some base
  rs2Operand : rs2Operand? instruction = some value
  noDestination : instruction.destination? = none
  table : JoltMetadata.lookupTable instruction = width.table?
  noAdvice : instruction.adviceValue? = none
  readSources : ExpansionTempLiveness.readSources instruction = [base, value]
  canonical : JoltRegisterEncoding.instructionIsCanonical instruction =
    (JoltRegisterEncoding.sourceIsCanonical base &&
      JoltRegisterEncoding.sourceIsCanonical value)

/-- Every load row has the fixed load metadata of its width.
For example, VirtualLoadW reads only its base and selects AddressOffsetW. -/
theorem LoadRow.metadata {instruction : Instr} {width : MemoryWidth} {destination : Dst}
    {base : Src} {imm : BitVec 64} (row : LoadRow instruction width destination base imm) :
    LoadRowFacts instruction width destination base imm := by
  obtain ⟨_, _, rfl⟩ := row
  cases width <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every store row has the fixed store metadata of its width.
For example, SD reads its base and value and selects no table. -/
theorem StoreRow.metadata {instruction : Instr} {width : MemoryWidth} {base value : Src}
    {imm : BitVec 64} (row : StoreRow instruction width base value imm) :
    StoreRowFacts instruction width base value imm := by
  obtain ⟨_, rfl⟩ := row
  cases width <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An access row's metadata shared by loads and stores: exactly one of the
Load and Store flags, the signed immediate, the base as first source and the
width's lookup table.
For example, both LD and SD have immediate `imm.toInt` and no table. -/
theorem AccessRow.metadata {instruction : Instr} {width : MemoryWidth} {base : Src}
    {imm : BitVec 64} (row : AccessRow instruction width base imm) :
    ((JoltMetadata.opcodeFlag instruction .Load = true ∧
        JoltMetadata.opcodeFlag instruction .Store = false) ∨
      (JoltMetadata.opcodeFlag instruction .Load = false ∧
        JoltMetadata.opcodeFlag instruction .Store = true)) ∧
    JoltMetadata.immediate instruction = imm.toInt ∧
    bytecodeRs1Register instruction = some (TraceWitness.sourceRegisterAddress base) ∧
    JoltMetadata.lookupTable instruction = width.table? := by
  rcases row with ⟨_, row⟩ | ⟨_, row⟩
  · have facts := LoadRow.metadata row
    exact ⟨Or.inl ⟨facts.load, facts.notStore⟩, facts.immediate, facts.rs1Register, facts.table⟩
  · have facts := StoreRow.metadata row
    exact ⟨Or.inr ⟨facts.notLoad, facts.store⟩, facts.immediate, facts.rs1Register, facts.table⟩

/-- A floor access row adds its operands: AddOperands is set, the left input is
the base register and the right input is the immediate.
For example, VirtualStoreW's lookup operand is `base + imm`. -/
theorem AccessRow.floor_inputs {instruction : Instr} {width : MemoryWidth} {base : Src}
    {imm : BitVec 64} (row : AccessRow instruction width base imm) (floor : width ≠ .double) :
    JoltMetadata.opcodeFlag instruction .AddOperands = true ∧
    (JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value,
      JoltMetadata.instructionFlag instruction .LeftOperandIsPC,
      JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value,
      JoltMetadata.instructionFlag instruction .RightOperandIsImm,
      JoltMetadata.instructionFlag instruction .RightOperandIsRdWriteValue) =
      (true, false, false, true, false) := by
  rcases row with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases width
  all_goals first
    | exact False.elim (floor rfl)
    | exact ⟨rfl, rfl⟩

/-- An access row is not a tape read. For example, LD is not VirtualAdviceLoad. -/
theorem AccessRow.not_tape {instruction : Instr} {width : MemoryWidth} {base : Src}
    {imm : BitVec 64} (row : AccessRow instruction width base imm)
    (destination : Dst) (count : BitVec 64) :
    instruction ≠ .VirtualAdviceLoad destination count := by
  rcases row with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases width <;> intro same <;> cases same

/-- A selected row's trace RAM address is its recorded address.
For example, VirtualLoadH records `ea - (ea &&& 6)`. -/
theorem AccessRow.ramAccessAddress {instruction : Instr} {width : MemoryWidth} {base : Src}
    {imm : BitVec 64} (row : AccessRow instruction width base imm) (state : SailJoltState) :
    TraceWitness.ramAccessAddress instruction state =
      some (width.recorded (sourceValue base state + imm)) := by
  rcases row with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> cases width <;>
    simp [MemoryWidth.load, MemoryWidth.store, TraceWitness.ramAccessAddress,
      MemoryWidth.recorded, MemoryWidth.offsetMask]

/-- A naturally aligned load row whose accessed doubleword loads `value` writes
`value` to its destination, ignoring the tape answer and runtime advice.
For example, VirtualLoadB at `ea = 11` writes the doubleword loaded from 8.
Jolt's tracer at c6703570: `tracer/src/instruction/floor_access.rs` (`load`)
and `tracer/src/instruction/ld.rs` (`LD::exec`). -/
theorem LoadRow.exec_rule {instruction : Instr} {width : MemoryWidth} {destination : Dst}
    {base : Src} {imm : BitVec 64} (row : LoadRow instruction width destination base imm)
    (pre : SailJoltState) (baseRead : readSrc base pre = .ok (sourceValue base pre) pre)
    (aligned : (sourceValue base pre + imm) &&& width.alignMask = 0) (value : BitVec 64)
    (loaded : Mmu.load_doubleword (width.accessed (sourceValue base pre + imm)) pre =
      .ok (.Ok value) pre)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice) :
    execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer pre =
      (do writeDst destination value; pure RETIRE_SUCCESS) pre := by
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice]
  obtain ⟨_, _, rfl⟩ := row
  cases width <;>
    simp only [MemoryWidth.alignMask, MemoryWidth.accessed] at aligned loaded <;>
    simp only [MemoryWidth.load, execWithTapeAnswer, execInstr, bind, EStateM.bind,
      baseRead, aligned, ↓reduceIte, loaded]

/-- A naturally aligned store row whose accessed doubleword store succeeds
retires with the store's post-state.
For example, SD at 16 storing 7 retires once `Mmu.store_doubleword 16 7` succeeds.
Jolt's tracer at c6703570: `tracer/src/instruction/floor_access.rs` (`store`)
and `tracer/src/instruction/sd.rs` (`SD::exec`). -/
theorem StoreRow.exec_rule {instruction : Instr} {width : MemoryWidth} {base value : Src}
    {imm : BitVec 64} (row : StoreRow instruction width base value imm)
    (pre post : SailJoltState) (baseRead : readSrc base pre = .ok (sourceValue base pre) pre)
    (valueRead : readSrc value pre = .ok (sourceValue value pre) pre)
    (aligned : (sourceValue base pre + imm) &&& width.alignMask = 0) (result : Bool)
    (stored : Mmu.store_doubleword (width.accessed (sourceValue base pre + imm))
      (sourceValue value pre) pre = .ok (.Ok result) post)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice) :
    execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post := by
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice]
  obtain ⟨_, rfl⟩ := row
  cases width <;>
    simp only [MemoryWidth.alignMask, MemoryWidth.accessed] at aligned stored <;>
    simp only [MemoryWidth.store, execWithTapeAnswer, execInstr, bind, EStateM.bind,
      baseRead, valueRead, aligned, ↓reduceIte, stored, pure, EStateM.pure]

/-- A retired load continuation writes the shared-memory doubleword.
For example, reading a mapped output word writes that word to its destination. -/
private theorem load_bind_word (address : BitVec 64) (destination : Dst)
    (pre post : SailJoltState)
    (runs : (do
        match ← Mmu.load_doubleword address with
        | .Ok word => writeDst destination word; pure RETIRE_SUCCESS
        | .Err error => pure error) pre = .ok RETIRE_SUCCESS post) :
    (do writeDst destination (Mmu.ram_doubleword pre.sail.mem address.toNat)
        pure RETIRE_SUCCESS) pre = .ok RETIRE_SUCCESS post := by
  cases loaded : Mmu.load_doubleword address pre with
  | error error middle => simp only [bind, EStateM.bind, loaded] at runs; cases runs
  | ok result middle =>
    obtain ⟨rfl, rfl⟩ := JoltConstraints.load_doubleword_shape pre middle address result loaded
    simpa only [bind, EStateM.bind, loaded] using runs

/-- A retired load row writes the doubleword at its accessed address.
For example, a floor load at effective address ten writes the whole word at eight.
The conclusion retains the full pre- and post-state of the destination write.
Jolt at `ff6fc6568`: `tracer/src/instruction/floor_access.rs` (`load`). -/
theorem LoadRow.write_of_run {instruction : Instr} {width : MemoryWidth} {destination : Dst}
    {base : Src} {imm : BitVec 64} (row : LoadRow instruction width destination base imm)
    (advice : instruction.RuntimeAdvice) (pre post : SailJoltState)
    (runs : execInstr (instruction.withRuntimeAdvice advice) pre = .ok RETIRE_SUCCESS post) :
    (do writeDst destination (Mmu.ram_doubleword pre.sail.mem
          (width.accessed (sourceValue base pre + imm)).toNat)
        pure RETIRE_SUCCESS) pre = .ok RETIRE_SUCCESS post := by
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice] at runs
  obtain ⟨faultClass, fault, rfl⟩ := row
  cases width <;> simp only [MemoryWidth.load, execInstr] at runs <;>
    have afterBase := lookup_read_bind base _ pre post _ runs
  · split at afterBase
    · exact load_bind_word _ destination pre post afterBase
    · cases afterBase
  · exact load_bind_word _ destination pre post afterBase
  all_goals
    split at afterBase
    · exact load_bind_word _ destination pre post afterBase
    · cases afterBase

/-- A retired load with a writable destination captures its shared-memory word.
For example, native `LD x0` expands to a temporary destination, which captures
its loaded word even though the architectural destination is discarded. -/
theorem LoadRow.capture_of_run {instruction : Instr} {width : MemoryWidth} {destination : Dst}
    {base : Src} {imm : BitVec 64} (row : LoadRow instruction width destination base imm)
    (writable : destination.NotX0) (advice : instruction.RuntimeAdvice)
    (pre post : SailJoltState)
    (runs : execInstr (instruction.withRuntimeAdvice advice) pre = .ok RETIRE_SUCCESS post) :
    TraceWitness.capturedDestinationValue destination post =
      Mmu.ram_doubleword pre.sail.mem
        (width.accessed (sourceValue base pre + imm)).toNat :=
  lookup_write_retire destination _ pre post writable (row.write_of_run advice pre post runs)

private theorem store_bind_result (address word : BitVec 64) (pre post : SailJoltState)
    (runs : (do
        match ← Mmu.store_doubleword address word with
        | .Ok _ => pure RETIRE_SUCCESS
        | .Err error => pure error) pre = .ok RETIRE_SUCCESS post) :
    ∃ result, Mmu.store_doubleword address word pre = .ok result post := by
  cases stored : Mmu.store_doubleword address word pre with
  | error err state => simp [bind, EStateM.bind, stored] at runs
  | ok result state =>
    simp only [bind, EStateM.bind, stored] at runs
    cases result <;> simp only [pure, EStateM.pure] at runs <;> cases runs <;> exact ⟨_, rfl⟩

/-- A store row that retires has run the doubleword store at its accessed
address with its stored value; an alignment fault would not retire.
For example, a retired VirtualStoreH at `ea = 10` stored to 8.
Jolt's tracer at c6703570: `tracer/src/instruction/floor_access.rs` (`store`). -/
theorem StoreRow.store_of_run {instruction : Instr} {width : MemoryWidth} {base value : Src}
    {imm : BitVec 64} (row : StoreRow instruction width base value imm)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice) (pre post : SailJoltState)
    (runs : execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post) :
    ∃ result, Mmu.store_doubleword (width.accessed (sourceValue base pre + imm))
      (sourceValue value pre) pre = .ok result post := by
  rw [withRuntimeAdvice_eq_of_noAdvice _ advice row.metadata.noAdvice] at runs
  obtain ⟨_, rfl⟩ := row
  cases width <;> simp only [MemoryWidth.store, execWithTapeAnswer, execInstr] at runs <;>
    have afterBase := lookup_read_bind base _ pre post _ runs
  · have afterValue := lookup_read_bind value _ pre post _ afterBase
    split at afterValue
    · exact store_bind_result _ _ pre post afterValue
    · cases afterValue
  · exact store_bind_result _ _ pre post (lookup_read_bind value _ pre post _ afterBase)
  all_goals
    split at afterBase
    · exact store_bind_result _ _ pre post (lookup_read_bind value _ pre post _ afterBase)
    · cases afterBase


/-- A retired store row changes only the eight bytes of its accessed word.
For example, a floor halfword row at effective address ten writes its captured
merged doubleword at eight, with the same map effect in I/O and RAM.
Jolt at `ff6fc6568`: `tracer/src/instruction/floor_access.rs` (`store`). -/
theorem StoreRow.memory_of_run {instruction : Instr} {width : MemoryWidth} {base value : Src}
    {imm : BitVec 64} (row : StoreRow instruction width base value imm)
    (answer : BitVec 64) (advice : instruction.RuntimeAdvice) (pre post : SailJoltState)
    (runs : execWithTapeAnswer (instruction.withRuntimeAdvice advice) answer pre =
      .ok RETIRE_SUCCESS post) :
    post.sail.mem = Mmu.write_ram_doubleword pre.sail.mem
      (width.accessed (sourceValue base pre + imm)).toNat (sourceValue value pre) := by
  obtain ⟨result, stored⟩ := row.store_of_run answer advice pre post runs
  exact congrArg (fun state => state.sail.mem)
    (JoltConstraints.store_doubleword_shape pre post _ _ result stored)

end JoltConstraints.Soundness
