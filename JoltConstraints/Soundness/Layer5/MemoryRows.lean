import JoltConstraints.Soundness.Layer5.RamAlignment
import JoltConstraints.Soundness.Layer5.LookupWrite
import JoltConstraints.Soundness.Layer5.PanicRestriction
import JoltConstraints.Soundness.Layer5.TerminationRestriction
import JoltConstraints.Soundness.Layer4.Identity
import JoltConstraints.Completeness.Helpers.FloorMemory
import JoltConstraints.Completeness.Helpers.RegistersReadProofHelpers
import JoltConstraints.expansion_temp_liveness

open LeanRV64D

/-! Native and floor-addressed memory rows, classified once by their width.
A memory row is a load (LD, VirtualLoadB/H/W) or a store (SD, VirtualStoreB/H/W).
Its effective address is `ea = base + imm`.
Native rows access the doubleword at `ea`; floor rows access the containing
doubleword `ea &&& ~~~7`.
For example, VirtualLoadH at `ea = 10` loads the doubleword at 8.
The facts below are proved once over the four widths and used by every memory step.
Jolt's tracer at c6703570: `tracer/src/instruction/floor_access.rs`
(`addresses`, `load`, `store`), `tracer/src/instruction/ld.rs` (`LD::exec`) and
`tracer/src/instruction/sd.rs` (`SD::exec`).
Jolt's verifier at c6703570 pins the accessed doubleword with constraint (01):
`crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_eq_constraint_rows`, row 0). -/

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

/-- The tracer's address checks for a ready load row, at its accessed doubleword.
For example, VirtualLoadH at `ea = 10` checks read permission at 8 through 15
below RAM. -/
theorem LoadRow.address_checks
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TracerAddressChecks)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (row : LoadRow run.bytecode[next].instruction width destination base imm) :
    DoublewordAddressChecks pre.jolt_device (width.accessed (sourceValue base pre + imm)) false := by
  have checked := restricted privateInputs run next pre ready
  obtain ⟨_, _, same⟩ := row
  rw [same] at checked
  cases width <;> exact checked

/-- The tracer's address checks for a ready store row, at its accessed doubleword.
For example, VirtualStoreB at `ea = 11` checks write permission at 8 through 15
below RAM. -/
theorem StoreRow.address_checks
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TracerAddressChecks)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (row : StoreRow run.bytecode[next].instruction width base value imm) :
    DoublewordAddressChecks pre.jolt_device (width.accessed (sourceValue base pre + imm)) true := by
  have checked := restricted privateInputs run next pre ready
  obtain ⟨_, same⟩ := row
  rw [same] at checked
  cases width <;> exact checked

/-- Under `PanicStoresOne`, a ready store row touching the panic region stores
the word 1. For example, the SDK's panic SB expansion ends with a VirtualStoreB
of the merged word 1. -/
theorem StoreRow.panic_value
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.PanicStoresOne)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    {width : MemoryWidth} {base value : Src} {imm : BitVec 64}
    (row : StoreRow run.bytecode[next].instruction width base value imm)
    (touch : TouchesPanic pre.jolt_device (width.accessed (sourceValue base pre + imm))) :
    sourceValue value pre = 1 := by
  have rule := restricted privateInputs run next pre ready
  obtain ⟨_, same⟩ := row
  rw [same] at rule
  cases width <;> exact rule touch

/-- Under `PanicStoresOne`, a ready load row cannot touch the panic region after
a completed panic store. For example, a VirtualLoadB of the panic word must come
before the store that sets the flag. -/
theorem LoadRow.panic_free
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.PanicStoresOne)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (row : LoadRow run.bytecode[next].instruction width destination base imm)
    (stored : ∃ i, run.StoresPanicAt i) :
    ¬ TouchesPanic pre.jolt_device (width.accessed (sourceValue base pre + imm)) := by
  have rule := restricted privateInputs run next pre ready
  obtain ⟨_, _, same⟩ := row
  rw [same] at rule
  cases width <;> exact rule stored

/-- Under `TerminationThenStall`, a ready load row cannot touch the termination
region after a completed termination store. For example, the SDK exit's
VirtualLoadB of the termination word comes before its store. -/
theorem LoadRow.termination_free
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (restricted : joltInstance.TerminationThenStall)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (row : LoadRow run.bytecode[next].instruction width destination base imm)
    (stored : ∃ i, run.StoresTerminationAt i) :
    ¬ TouchesTermination pre.jolt_device (width.accessed (sourceValue base pre + imm)) := by
  have rule := restricted privateInputs run next pre ready stored
  obtain ⟨_, _, same⟩ := row
  rw [same] at rule
  cases width <;> exact rule

/-- Row `row` of a trace over `bytecode` completed a store whose accessed
doubleword satisfies `touches`: an SD at `base + imm`, or a floor store at
`(base + imm) &&& ~~~7`. With `touches` set to `TouchesTermination` or
`TouchesPanic` this is the row form of `UntrustedAnswerRun.StoresTerminationAt`
or `UntrustedAnswerRun.StoresPanicAt`, with the same cases.
For example, the SDK exit's final VirtualStoreB touches termination. -/
def storeTouches (touches : JoltDevice → BitVec 64 → Prop)
    {bytecode : Array JoltInstructionRow} (row : TraceRow bytecode) : Prop :=
  match bytecode[row.rowIndex].instruction with
  | .SD base _ imm => touches row.preState.jolt_device (sourceValue base row.preState + imm)
  | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _ | .VirtualStoreW base _ imm _ =>
      touches row.preState.jolt_device ((sourceValue base row.preState + imm) &&& ~~~7)
  | _ => False

/-- A row's store satisfies `touches` exactly when the row is a store row whose
accessed doubleword satisfies it.
For example, a VirtualStoreH at `ea = termination + 2` touches termination. -/
theorem storeTouches_iff (touches : JoltDevice → BitVec 64 → Prop)
    {bytecode : Array JoltInstructionRow} (row : TraceRow bytecode) :
    storeTouches touches row ↔ ∃ width base value imm,
      StoreRow bytecode[row.rowIndex].instruction width base value imm ∧
      touches row.preState.jolt_device (width.accessed (sourceValue base row.preState + imm)) := by
  constructor
  · intro stored
    unfold storeTouches at stored
    split at stored
    · exact ⟨.double, _, _, _, ⟨ExceptionType.E_SAMO_Addr_Align (), by assumption⟩, stored⟩
    · exact ⟨.byte, _, _, _, ⟨_, by assumption⟩, stored⟩
    · exact ⟨.halfword, _, _, _, ⟨_, by assumption⟩, stored⟩
    · exact ⟨.word, _, _, _, ⟨_, by assumption⟩, stored⟩
    · exact False.elim stored
  · rintro ⟨width, base, value, imm, ⟨fault, same⟩, touch⟩
    unfold storeTouches
    rw [same]
    cases width <;> exact touch

/-- The termination-store history of a run is the row predicate at that row.
For example, both read the same SD and pre-state. -/
theorem storesTerminationAt_iff
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) (i : Fin run.rows.size) :
    run.StoresTerminationAt i ↔ storeTouches TouchesTermination run.rows[i] :=
  Iff.rfl

/-- The panic-store history of a run is the row predicate at that row.
For example, both read the same VirtualStoreB and pre-state. -/
theorem storesPanicAt_iff
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) (i : Fin run.rows.size) :
    run.StoresPanicAt i ↔ storeTouches TouchesPanic run.rows[i] :=
  Iff.rfl

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  {t : Fin params.traceLength} {slot : Fin (2 ^ params.logBytecodeK)}
  (selected : bytecodeRa witness slot t = 1)
  {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
  {width : MemoryWidth} {base : Src} {imm : BitVec 64}
  (access : AccessRow row.instruction width base imm)

include charAbove2pow128 context equations selected rowIs access

/-- The lookup output of a selected access row is a small offset: zero for a
native row, and the AddressOffset entry for a floor row.
Once `sum` is known to be the effective address's value, that offset is
`sum &&& offsetMask`. For example, a halfword row at `ea = 10` outputs 2.
Jolt's prover: `crates/jolt-lookup-tables/src/tables/address_offset.rs`
(`AddressOffsetTable::materialize_entry`) at `c6703570`. -/
private theorem AccessRow.lookup_offset (baseValue : BitVec 64)
    (source : witness.Rs1Value t = (baseValue.toNat : F)) :
    ∃ offset : Nat, offset ≤ 7 ∧ witness.LookupOutput t = (offset : F) ∧
      ∀ sum : Nat, sum < 2 ^ 64 →
        ((sum : Int) : F) = (((baseValue.toNat : Int) + imm.toInt : Int) : F) →
        offset = sum &&& width.offsetMask.toNat := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨-, immediate, -, tableIs⟩ := access.metadata
  obtain ⟨chosen, lookupSelected, _⟩ := instructionLookupRa_unique bound context equations t
  have output := lookupOutput_of_selected_bytecode bound context equations t slot selected
    chosen lookupSelected
  simp only [rowIs, Option.bind_some, tableIs] at output
  by_cases native : width = .double
  · subst native
    refine ⟨0, by decide, by simpa only [MemoryWidth.table?, Nat.cast_zero] using output, ?_⟩
    intro sum _ _
    simp [MemoryWidth.offsetMask]
  obtain ⟨addFlag, inputFlags⟩ := access.floor_inputs native
  simp only [Prod.mk.injEq] at inputFlags
  obtain ⟨rs1Flag, pcFlag, rs2Flag, immFlag, rdFlag⟩ := inputFlags
  have add : witness.OpFlags .AddOperands t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, addFlag] using
      opFlag_of_selected_bytecode bound context equations .AddOperands t slot selected
  have raf := instructionRafFlag_one_of_arithmetic bound context equations t (Or.inl add)
  have immediateIs : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode bound context equations t slot selected]
    simp only [bytecodeImmediate, rowIs, immediate]
  obtain ⟨left, right⟩ :=
    instructionInputs_of_selected_bytecode bound context equations t slot selected row rowIs
  simp only [rs1Flag, pcFlag, rs2Flag, immFlag, rdFlag, Bool.false_eq_true, ↓reduceIte,
    add_zero, zero_add, source, immediateIs] at left right
  have operand := rightLookupOperand_of_selected bound context equations t chosen lookupSelected
  rw [raf, sub_self, zero_mul, zero_add, one_mul] at operand
  have addition := equations.rightLookupAdd t
  rw [add, one_mul, operand, left, right, sub_sub, sub_eq_zero] at addition
  have entry (mask : Nat) (small : mask < 2 ^ 128) :
      ((BitVec.ofFin chosen &&& BitVec.ofNat 128 mask).toNat : F) = ((chosen.val &&& mask : Nat) : F) := by
    rw [BitVec.toNat_and, BitVec.toNat_ofFin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  refine ⟨chosen.val &&& width.offsetMask.toNat, ?_, ?_, ?_⟩
  · have offsetSmall : width.offsetMask.toNat ≤ 7 := by cases width <;> decide
    exact le_trans Nat.and_le_right offsetSmall
  · simp only [lookupTableEntry, addressOffsetTableEntry] at output
    cases width
    · exact False.elim (native rfl)
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 7 (by norm_num)] using output
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 6 (by norm_num)] using output
    · simpa only [MemoryWidth.table?, Nat.reduceSub, entry 4 (by norm_num)] using output
  · intro sum sumSmall sumIs
    have same : chosen.val = sum := natCast_injective_below_char
      (lt_trans chosen.isLt charAbove2pow128) (lt_trans sumSmall (two_pow_64_lt_char bound))
      (by
        rw [addition]
        push_cast at sumIs
        exact sumIs.symm)
    rw [same]

/-- A selected access row's RAM address is the doubleword it accesses, and its
effective address is naturally aligned for its width.
Constraint (01) subtracts the lookup offset from the integer sum of the base
and signed immediate, RAM selection makes the result zero or an in-domain word
address, and the layout bound rules out wrapping.
For example, VirtualStoreH with base 16 and immediate -6 has `ea = 10`, records
`10 - 2 = 8`, and accesses 8; with `ea = 11` it would record 9, which no RAM
selection allows.
Jolt's verifier at c6703570: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_eq_constraint_rows`, row 0). -/
theorem AccessRow.address_encoded (regionFits : joltInstance.RamRegionFits)
    (baseValue : BitVec 64) (source : witness.Rs1Value t = (baseValue.toNat : F)) :
    witness.RamAddress t = ((width.accessed (baseValue + imm)).toNat : F) ∧
      (baseValue + imm) &&& width.alignMask = 0 ∧
      width.recorded (baseValue + imm) = width.accessed (baseValue + imm) := by
  have bound := two_pow_127_lt_char charAbove2pow128
  obtain ⟨flags, immediate, -, -⟩ := access.metadata
  have active : witness.OpFlags .Load t + witness.OpFlags .Store t = 1 := by
    rw [opFlag_of_selected_bytecode bound context equations .Load t slot selected,
      opFlag_of_selected_bytecode bound context equations .Store t slot selected]
    rcases flags with ⟨load, store⟩ | ⟨load, store⟩ <;>
      simp [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, load, store]
  have immediateIs : witness.Imm t = (imm.toInt : F) := by
    rw [imm_of_selected_bytecode bound context equations t slot selected]
    simp only [bytecodeImmediate, rowIs, immediate]
  have sum := ramAddress_eq_sum equations.ramAddrEqRs1PlusImmMinusLookupIfLoadStore
    t active baseValue imm source immediateIs
  obtain ⟨offset, offsetSmall, output, offsetIs⟩ :=
    access.lookup_offset charAbove2pow128 context equations selected rowIs baseValue source
  obtain ⟨word, wordIs, wordFits⟩ : ∃ word : Nat,
      witness.RamAddress t = (word : F) ∧ word + 7 < 2 ^ 64 := by
    rcases ramRa_zero_or_unique bound context equations t with zero | ⟨chosen, one, _⟩
    · exact ⟨0, by simpa using (ramRa_zero_iff_address_zero bound context equations t).mp zero,
        by norm_num⟩
    · exact ⟨_, ramAddress_of_selected bound context equations t chosen one,
        ram_word_byte_lt_two_pow_64 context regionFits chosen ⟨7, by decide⟩⟩
  have fieldSum : (((baseValue.toNat : Int) + imm.toInt : Int) : F) = ((word + offset : Nat) : F) := by
    rw [Nat.cast_add, ← wordIs, sum, output]
    ring
  have intSum := addressSum_eq_of_field_eq bound baseValue imm (word + offset) (by omega) fieldSum
  have eaValue := address_toNat_eq_sum baseValue imm (by omega)
  have offsetEq := offsetIs (baseValue + imm).toNat (baseValue + imm).isLt (by rw [eaValue])
  have recordedValue : (width.recorded (baseValue + imm)).toNat = word := by
    rw [MemoryWidth.recorded_toNat, ← offsetEq]
    omega
  have recordedEncoded : witness.RamAddress t = ((width.recorded (baseValue + imm)).toNat : F) := by
    rw [recordedValue]
    exact wordIs
  have aligned := width.aligned_of_recorded _
    (ramAddress_aligned bound context equations t _ recordedEncoded)
  have same := width.recorded_eq_accessed _ aligned
  exact ⟨same ▸ recordedEncoded, aligned, same⟩

end JoltConstraints.Soundness
