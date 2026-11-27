import JoltConstraints.theorems.Completeness.Helpers.VerifierSizes

open LeanRV64D JoltISA

set_option autoImplicit false

namespace JoltConstraints

/-- Inserting `f a` at each address `a` of `[lo, lo + n)`. -/
theorem foldl_insert_range_get? (lo n : Nat) (f : Nat → BitVec 8)
    (base : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    ((List.range n).foldl (fun mem k => mem.insert (lo + k) (f (lo + k))) base).get? a =
      if lo ≤ a ∧ a < lo + n then some (f a) else base.get? a := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, ← Std.ExtHashMap.get?_eq_getElem?, ih]
    by_cases h : lo + n = a
    · subst h
      simp
    · simp only [beq_iff_eq, h, ↓reduceIte]
      by_cases hin : lo ≤ a ∧ a < lo + n
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- Jolt's memory map after inserting the bytes of an array from index `n`: the byte at
`start + o` is `l[o - n]` for `o` in range, else unchanged. -/
theorem zipIdx_fold_get? (start : Nat) (l : List (BitVec 8)) (n o : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    ((l.zipIdx n).foldl
      (fun mem (x : BitVec 8 × Nat) => mem.insert (start + x.2) x.1) mem).get?
        (start + o) =
      if n ≤ o ∧ o < n + l.length then l[o - n]? else mem.get? (start + o) := by
  induction l generalizing n mem with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    dsimp only
    rw [ih]
    by_cases h : n = o
    · subst h
      simp
    · simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      have : ¬ (start + n == start + o) = true := by
        simp only [beq_iff_eq]; omega
      simp only [this]
      simp only [List.length_cons]
      rcases Nat.lt_or_gt_of_ne h with hlt | hgt
      · obtain ⟨k, rfl⟩ : ∃ k, o = n + 1 + k := ⟨o - n - 1, by omega⟩
        by_cases hk : k < t.length
        · have h1 : n + 1 ≤ n + 1 + k ∧ n + 1 + k < n + 1 + t.length := by omega
          have h2 : n ≤ n + 1 + k ∧ n + 1 + k < n + (t.length + 1) := by omega
          simp only [h1, h2, and_self, ↓reduceIte]
          have : n + 1 + k - n = k + 1 := by omega
          have h3 : n + 1 + k - (n + 1) = k := by omega
          rw [this, h3]
          rfl
        · have h1 : ¬ (n + 1 ≤ n + 1 + k ∧ n + 1 + k < n + 1 + t.length) := by omega
          have h2 : ¬ (n ≤ n + 1 + k ∧ n + 1 + k < n + (t.length + 1)) := by omega
          rw [ite_eq_right h1, ite_eq_right h2]
          simp only [Bool.false_eq_true, ↓reduceIte]
      · have h1 : ¬ (n + 1 ≤ o ∧ o < n + 1 + t.length) := by omega
        have h2 : ¬ (n ≤ o ∧ o < n + (t.length + 1)) := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
        simp only [Bool.false_eq_true, ↓reduceIte]


/-- Jolt's initial RAM byte map holds the array's byte at each in-range offset. -/
theorem init_state_mem_get? (entry : BitVec 64) (ram : Array (BitVec 8)) (io : JoltDevice)
    (tape : JoltAdviceTape) (o : Nat) :
    (init_state entry ram io tape).sail.mem.get? (JoltISA.RAM_START_ADDRESS + o) = ram[o]? := by
  have h := zipIdx_fold_get? RAM_START_ADDRESS ram.toList 0 o {}
  rw [show (init_state entry ram io tape).sail.mem = (ram.toList.zipIdx.foldl
    (fun mem (x : BitVec 8 × Nat) => mem.insert (JoltISA.RAM_START_ADDRESS + x.2) x.1) {}) from rfl]
  by_cases ho : o < ram.size
  · simpa [ho] using h
  · have : ¬ (0 ≤ o ∧ o < 0 + ram.toList.length) := by simp; omega
    rw [ite_eq_right this] at h
    simpa [ho] using h

/-- Initialization retains all present base bytes and fills the complete I/O
window, even when an input or advice buffer is empty.
For example, an untouched output byte is present after initialization.
Adapted from Quang Dao's `initialMem_present` in PR #73. -/
theorem initial_ram_state_present (device : JoltDevice) (base : Std.ExtHashMap Nat (BitVec 8))
    (inputs trusted untrusted : Array (BitVec 8)) (a : Nat)
    (present : (base.get? a).isSome ∨
      device.memory_layout.get_lowest_address.toNat ≤ a ∧ a < RAM_START_ADDRESS) :
    ((device.initial_ram_state base inputs trusted untrusted).get? a).isSome := by
  have keep : ∀ (start : Nat) (bytes : Array (BitVec 8)) (m : Std.ExtHashMap Nat (BitVec 8)),
      (m.get? a).isSome = true →
      ((bytes.toList.zipIdx.foldl (fun m (x : BitVec 8 × Nat) => m.insert (start + x.2) x.1)
        m).get? a).isSome = true := fun start bytes m hm =>
    List.foldlRecOn (motive := fun m : Std.ExtHashMap Nat (BitVec 8) =>
      (m.get? a).isSome = true) _ _ hm
      (fun m hm byte _ => insert_preserves_present m _ a byte.1 hm)
  have zeroed : (((List.range
      (RAM_START_ADDRESS - device.memory_layout.get_lowest_address.toNat)).foldl
        (fun m k => m.insert (device.memory_layout.get_lowest_address.toNat + k) 0)
        base).get? a).isSome := by
    rcases present with present | ⟨low, high⟩
    · exact List.foldlRecOn (motive := fun m : Std.ExtHashMap Nat (BitVec 8) =>
          (m.get? a).isSome = true) _ _ present
        (fun m hm k _ => insert_preserves_present m _ a 0 hm)
    · rw [foldl_insert_range_get? _ _ (fun _ => 0) base a,
        ite_eq_left (by omega)]
      rfl
  exact keep _ _ _ (keep _ _ _ (keep _ _ _ zeroed))

/-- Installing a buffer keeps every byte at or after its endpoint unchanged.
For example, inserting advice cannot overwrite an input byte. -/
private theorem buffer_insert_get?_above (start : Nat) (bytes : Array (BitVec 8))
    (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (below : start + bytes.size ≤ a) :
    (bytes.toList.zipIdx.foldl (fun m byte => m.insert (start + byte.2) byte.1) mem).get? a =
      mem.get? a := by
  apply List.foldlRecOn (motive := fun m : Std.ExtHashMap Nat (BitVec 8) =>
    m.get? a = mem.get? a) _ _ rfl
  intro current same byte member
  have bound : byte.2 < bytes.size := by
    simpa using List.snd_lt_add_of_mem_zipIdx member
  have different : start + byte.2 ≠ a := by omega
  simpa [Std.ExtHashMap.getElem?_insert, different] using same

/-- Shared I/O initialization preserves every RAM byte of its base map.
For example, the program's first byte is unchanged by all three buffer overlays.
The layout is checked and each buffer fits its capacity, as `JoltDevice.try_with_io` checks.
Jolt at `504dd78a2`: `tracer/src/lib.rs` (`create_emulator`) and
`common/src/jolt_device.rs` (`JoltDevice::try_with_io`).
Adapted from Quang Dao's `initialMem_get?_above_ram` in PR #73. -/
theorem initial_ram_state_get?_above_ram (device : JoltDevice)
    (base : Std.ExtHashMap Nat (BitVec 8)) (inputs trusted untrusted : Array (BitVec 8))
    (config : MemoryConfig) (layoutBuilt : MemoryLayout.new config = some device.memory_layout)
    (trustedFits : trusted.size ≤ device.memory_layout.max_trusted_advice_size.toNat)
    (untrustedFits : untrusted.size ≤ device.memory_layout.max_untrusted_advice_size.toNat)
    (inputsFit : inputs.size ≤ device.memory_layout.max_input_size.toNat)
    (a : Nat) (above : RAM_START_ADDRESS ≤ a) :
    (device.initial_ram_state base inputs trusted untrusted).get? a = base.get? a := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config device.memory_layout layoutBuilt
  obtain ⟨outputStart, _⟩ := new_outputs_after_inputs config device.memory_layout layoutBuilt
  obtain ⟨lowestLeInput, inputLeOutput, outputLeEnd, endEq, ioEnd⟩ :=
    new_io_ordered config device.memory_layout layoutBuilt
  rw [endEq] at outputLeEnd
  unfold JoltDevice.initial_ram_state
  dsimp only
  rw [buffer_insert_get?_above _ _ _ a (by omega),
    buffer_insert_get?_above _ _ _ a (by omega),
    buffer_insert_get?_above _ _ _ a (by omega),
    foldl_insert_range_get? _ _ (fun _ => 0) base a, ite_eq_right (by omega)]

/-- Input-capacity bytes are the supplied input bytes followed by zero padding.
For example, with two supplied bytes, input byte three is initialized to zero.
Adapted from Quang Dao's `initialMem_input` in PR #73. -/
theorem initial_ram_state_input (device : JoltDevice)
    (base : Std.ExtHashMap Nat (BitVec 8)) (inputs trusted untrusted : Array (BitVec 8))
    (config : MemoryConfig) (layoutBuilt : MemoryLayout.new config = some device.memory_layout)
    (trustedFits : trusted.size ≤ device.memory_layout.max_trusted_advice_size.toNat)
    (untrustedFits : untrusted.size ≤ device.memory_layout.max_untrusted_advice_size.toNat)
    (a : Nat) (lower : device.memory_layout.input_start.toNat ≤ a)
    (upper : a < device.memory_layout.output_start.toNat) :
    (device.initial_ram_state base inputs trusted untrusted).get? a =
      some (inputs[a - device.memory_layout.input_start.toNat]?.getD 0) := by
  obtain ⟨_, _, _, _, trustedEnd, untrustedEnd, _, _, _, inputStart⟩ :=
    new_advice_regions config device.memory_layout layoutBuilt
  have trustedBelow : device.memory_layout.trusted_advice_start.toNat + trusted.size ≤
      device.memory_layout.input_start.toNat := by omega
  have untrustedBelow : device.memory_layout.untrusted_advice_start.toNat + untrusted.size ≤
      device.memory_layout.input_start.toNat := by omega
  obtain ⟨low, _, outputLeEnd, endEq, ioEnd⟩ := new_io_ordered config device.memory_layout layoutBuilt
  rw [endEq] at outputLeEnd
  have inputBelowRam : a < RAM_START_ADDRESS := by omega
  have lowBelow : device.memory_layout.get_lowest_address.toNat ≤ a := by omega
  unfold JoltDevice.initial_ram_state
  dsimp only
  let start := device.memory_layout.input_start.toNat
  let zeroed := (List.range (RAM_START_ADDRESS - device.memory_layout.get_lowest_address.toNat)).foldl
    (fun m k => m.insert (device.memory_layout.get_lowest_address.toNat + k) 0) base
  let advised := untrusted.toList.zipIdx.foldl
    (fun m (x : BitVec 8 × Nat) => m.insert (device.memory_layout.untrusted_advice_start.toNat + x.2) x.1)
    (trusted.toList.zipIdx.foldl
      (fun m (x : BitVec 8 × Nat) => m.insert (device.memory_layout.trusted_advice_start.toNat + x.2) x.1)
      zeroed)
  have inputRead := zipIdx_fold_get? start inputs.toList 0 (a - start) advised
  have addressEq : start + (a - start) = a := by dsimp only [start]; omega
  rw [addressEq] at inputRead
  change (inputs.toList.zipIdx.foldl
    (fun m (x : BitVec 8 × Nat) => m.insert (start + x.2) x.1) advised).get? a = _
  rw [inputRead]
  by_cases inInputs : a - start < inputs.size
  · rw [ite_eq_left (by simpa using inInputs)]
    change inputs.toList[a - start - 0]? = some (inputs[a - start]?.getD 0)
    simp only [Nat.sub_zero, Array.getElem?_toList, Array.getElem?_eq_getElem inInputs,
      Option.getD_some]
  · rw [ite_eq_right (by simpa using inInputs)]
    have none : inputs[a - start]? = none := Array.getElem?_eq_none (by omega)
    rw [none]
    dsimp only [advised]
    rw [buffer_insert_get?_above _ _ _ a (by omega), buffer_insert_get?_above _ _ _ a (by omega)]
    dsimp only [zeroed]
    rw [foldl_insert_range_get? _ _ (fun _ => 0) base a, ite_eq_left (by omega)]
    rfl

/-- Every byte of an initialized input-capacity region is its supplied byte or zero.
For example, missing input bytes are present zero bytes in shared memory. -/
theorem initial_state_input_get? {Source : Type} (inst : JoltInstance Source)
    (inputs : JoltPrivateInputs) (state : SailJoltState)
    (initialized : inst.initial_state inputs = some state) (a : Nat)
    (lower : state.jolt_device.memory_layout.input_start.toNat ≤ a)
    (upper : a < state.jolt_device.memory_layout.output_start.toNat) :
    state.sail.mem.get? a = some (inst.inputs[a - state.jolt_device.memory_layout.input_start.toNat]?.getD 0) := by
  obtain ⟨layout, layoutBuilt, trustedFits, untrustedFits, _, initialized⟩ :=
    initial_state_build inst inputs state initialized
  obtain ⟨_, _, shape⟩ := initialState_shape _ _ _ _ _ _ initialized
  unfold JoltInstance.memory_layout at layoutBuilt
  rw [shape] at lower upper ⊢
  exact initial_ram_state_input _ _ inst.inputs inst.trusted_advice inputs.untrusted_advice
    _ layoutBuilt trustedFits untrustedFits a lower upper

/-- An initialized program's RAM bytes are precisely its allocated initial array.
For example, an I/O overlay changes no byte at RAM offset zero. -/
theorem initial_state_ram_get? {Source : Type} (inst : JoltInstance Source)
    (inputs : JoltPrivateInputs) (state : SailJoltState)
    (initialized : inst.initial_state inputs = some state) (offset : Nat) :
    state.sail.mem.get? (RAM_START_ADDRESS + offset) =
      (initialRam state.jolt_device.memory_layout inst.program.memory_init)[offset]? := by
  obtain ⟨layout, layoutBuilt, trustedFits, untrustedFits, inputsFit, initialized⟩ :=
    initial_state_build inst inputs state initialized
  obtain ⟨_, _, shape⟩ := initialState_shape _ _ _ _ _ _ initialized
  unfold JoltInstance.memory_layout at layoutBuilt
  rw [shape]
  let ram := initialRam layout inst.program.memory_init
  let device : JoltDevice := { memory_layout := layout, panic := false }
  let tape : JoltAdviceTape := { bytes := inputs.advice_tape, readPosition := 0 }
  have same := initial_ram_state_get?_above_ram device
    (init_state inst.program.entry_address ram device tape).sail.mem
    inst.inputs inst.trusted_advice inputs.untrusted_advice _ layoutBuilt trustedFits
    untrustedFits inputsFit (RAM_START_ADDRESS + offset) (by omega)
  exact same.trans (init_state_mem_get? inst.program.entry_address ram device tape offset)

/-- Initialization allocates beyond the loaded program's endpoint.
For example, the stack canary and stack follow the program before the heap ends. -/
theorem initial_state_program_end_le_heap_end {Source : Type} (inst : JoltInstance Source)
    (inputs : JoltPrivateInputs) (state : SailJoltState)
    (initialized : inst.initial_state inputs = some state) :
    inst.program.program_end.toNat ≤ state.jolt_device.memory_layout.heap_end.toNat := by
  have layoutBuilt := (initial_state_device inst inputs state initialized).1
  unfold JoltInstance.memory_layout at layoutBuilt
  obtain ⟨size, sizeIs, bound⟩ := new_heap_end_ge _ _ layoutBuilt
  have sizeEq : size = inst.program.program_size := by simpa using sizeIs.symm
  subst size
  have programSize : inst.program.program_size.toNat =
      inst.program.program_end.toNat - RAM_START_ADDRESS := by
    unfold Rv64ProgramImage.program_size
    rw [BitVec.toNat_sub_of_le (by
      simpa [RAM_START_ADDRESS, BitVec.le_def] using inst.program.program_end_ge_ram_start)]
    simp [RAM_START_ADDRESS]
  have above := inst.program.program_end_ge_ram_start
  omega

end JoltConstraints
