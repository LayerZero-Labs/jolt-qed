import JoltConstraints.theorems.SharedMemoryInitialization
import JoltConstraints.theorems.WholeRun.Relation

/-!
The program image and the initialized shared byte map.
For example, a code byte at RAM start is retained through I/O initialization.
These facts require no decoded instruction or per-block simulation.
-/

open LeanRV64D JoltConstraints

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- The last byte `memory_init` writes at address `a`; later entries override earlier ones, as
`initialRam` folds them in order.
For example, `[(0x80000000, 1), (0x80000000, 2)]` gives 2 at `0x80000000`. -/
def lastByte : List (BitVec 64 × BitVec 8) → Nat → Option (BitVec 8)
  | [], _ => none
  | e :: t, a =>
    match lastByte t a with
    | some b => some b
    | none => if e.1.toNat = a then some e.2 else none

/-- The byte of the program image at address `a`: the byte Jolt loads there at initialization,
or none where the ELF has no byte. -/
def imageByte? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 8) :=
  lastByte program.memory_init a

/-- The 16-bit parcel of the image at `a`, low byte first.
For example, bytes `0x13` and `0x01` give `0x0113`. -/
def imageParcel? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 16) := do
  let lo ← imageByte? program a
  let hi ← imageByte? program (a + 1)
  pure (hi ++ lo)

/-- The 32-bit word of the image at `a`, low parcel first.
For example, parcels `0x0113` then `0x0000` give `0x00000113`. -/
def imageWord? (program : Rv64ProgramImage SourceInstruction) (a : Nat) : Option (BitVec 32) := do
  let lo ← imageParcel? program a
  let hi ← imageParcel? program (a + 2)
  pure (hi ++ lo)

/-- A recorded image byte comes from an image entry at that address.
For example, a byte at the entry address has a matching loaded byte entry. -/
theorem lastByte_some {l : List (BitVec 64 × BitVec 8)} {a : Nat} {b : BitVec 8}
    (h : lastByte l a = some b) : ∃ e ∈ l, e.1.toNat = a := by
  induction l generalizing b with
  | nil => simp [lastByte] at h
  | cons e t ih =>
    simp only [lastByte] at h
    split at h
    · rename_i hb
      obtain ⟨e', he', h'⟩ := ih hb
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · split at h
      · rename_i heq
        exact ⟨e, List.mem_cons_self .., heq⟩
      · cases h

/-- Every image byte lies in `[RAM_START_ADDRESS, program_end)`. -/
theorem imageByte?_bounds (program : Rv64ProgramImage SourceInstruction) {a : Nat}
    {b : BitVec 8} (h : imageByte? program a = some b) :
    JoltISA.RAM_START_ADDRESS ≤ a ∧ a < program.program_end.toNat := by
  obtain ⟨e, he, heq⟩ := lastByte_some h
  have := program.memory_init_in_program e he
  omega

/-- A parcel consists of its two consecutive image bytes in little-endian order.
For example, bytes 1 and 2 form the parcel `0x0201`. -/
theorem imageParcel?_eq_some {program : Rv64ProgramImage SourceInstruction} {a : Nat}
    {h : BitVec 16} : imageParcel? program a = some h ↔
      ∃ lo hi, imageByte? program a = some lo ∧ imageByte? program (a + 1) = some hi ∧
        h = hi ++ lo := by
  cases h1 : imageByte? program a <;> cases h2 : imageByte? program (a + 1) <;>
    simp [imageParcel?, h1, h2, eq_comm]

/-- A word consists of its two consecutive image parcels in little-endian order.
For example, parcels 1 and 2 form the word `0x00020001`. -/
theorem imageWord?_eq_some {program : Rv64ProgramImage SourceInstruction} {a : Nat}
    {w : BitVec 32} : imageWord? program a = some w ↔
      ∃ lo hi, imageParcel? program a = some lo ∧ imageParcel? program (a + 2) = some hi ∧
        w = hi ++ lo := by
  cases h1 : imageParcel? program a <;> cases h2 : imageParcel? program (a + 2) <;>
    simp [imageWord?, h1, h2, eq_comm]

/-- Folding `memory_init` into the zero array, as `initialRam` does: the byte at offset `o`
is the last image byte for `RAM_START_ADDRESS + o`, or the array's own byte if none. -/
theorem initialRam_fold_getElem? (l : List (BitVec 64 × BitVec 8)) (ram : Array (BitVec 8))
    (o : Nat) (ho : o < ram.size) :
    (l.foldl (fun ram (x : BitVec 64 × BitVec 8) =>
      if JoltISA.RAM_START_ADDRESS ≤ x.1.toNat then
        ram.setIfInBounds (x.1.toNat - JoltISA.RAM_START_ADDRESS) x.2 else ram) ram)[o]? =
      some ((lastByte l (JoltISA.RAM_START_ADDRESS + o)).getD ram[o]) := by
  induction l generalizing ram with
  | nil => simp [lastByte, ho]
  | cons e t ih =>
    rcases e with ⟨address, byte⟩
    rw [List.foldl_cons]
    dsimp only
    have hsz : (if JoltISA.RAM_START_ADDRESS ≤ address.toNat then
        ram.setIfInBounds (address.toNat - JoltISA.RAM_START_ADDRESS) byte else ram).size =
        ram.size := by
      split <;> simp
    rw [ih _ (by rw [hsz]; exact ho)]
    refine congrArg some ?_
    simp only [lastByte]
    cases hl : lastByte t (JoltISA.RAM_START_ADDRESS + o) with
    | some b => simp
    | none =>
      simp only [Option.getD_none]
      by_cases hr : JoltISA.RAM_START_ADDRESS ≤ address.toNat
      · simp only [hr, ite_true]
        by_cases hao : address.toNat - JoltISA.RAM_START_ADDRESS = o
        · have : address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
          simp [this, Array.getElem_setIfInBounds_self]
        · have : ¬ address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
          simp [this, Array.getElem_setIfInBounds_ne, hao, ho]
      · have : ¬ address.toNat = JoltISA.RAM_START_ADDRESS + o := by omega
        simp [hr, this]


/-- **Every image byte is in Sail's initial memory.** At `sailInit` of Jolt's initial state,
Sail's memory holds each byte of the program image at its address. -/
theorem sailInit_get?_image (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (jt : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some jt) (a : Nat) (b : BitVec 8)
    (h : imageByte? joltInstance.program a = some b) :
    (sailInit jt).mem.get? a = some b := by
  have layoutBuilt := (initial_state_device joltInstance privateInputs jt built).1
  unfold JoltInstance.memory_layout at layoutBuilt
  obtain ⟨above, inProgram⟩ := imageByte?_bounds joltInstance.program h
  have heap := initial_state_program_end_le_heap_end joltInstance privateInputs jt built
  have backing := heap_end_le_ram_backing_end jt.jolt_device _ layoutBuilt
  have size := initialRam_size_eq_ram_size jt.jolt_device.memory_layout
    joltInstance.program.memory_init _ layoutBuilt
  have inside : a - JoltISA.RAM_START_ADDRESS <
      (initialRam jt.jolt_device.memory_layout joltInstance.program.memory_init).size := by
    rw [size]
    unfold JoltISA.Mmu.ram_backing_end at backing
    omega
  have loaded := initial_state_ram_get? joltInstance privateInputs jt built
    (a - JoltISA.RAM_START_ADDRESS)
  rw [Nat.add_sub_cancel' above] at loaded
  change jt.sail.mem.get? a = some b
  rw [loaded]
  have allocated : a - JoltISA.RAM_START_ADDRESS < (Array.replicate
      (8 * ((jt.jolt_device.memory_layout.get_total_memory_size.toNat + 7) / 8))
      (0 : BitVec 8)).size := by
    rw [Array.size_replicate]
    rwa [initialRam_size] at inside
  have key := initialRam_fold_getElem? joltInstance.program.memory_init
    (Array.replicate (8 * ((jt.jolt_device.memory_layout.get_total_memory_size.toNat + 7) / 8)) 0)
    (a - JoltISA.RAM_START_ADDRESS) allocated
  rw [Nat.add_sub_cancel' above] at key
  change lastByte joltInstance.program.memory_init a = some b at h
  simpa only [initialRam, h, Option.getD_some] using key

end WholeRun
