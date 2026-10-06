import JoltConstraints.Constraints.RamReadData

/-!
Rust's `MemoryLayout::new`, restricted to the advice and input regions, and a
proof that every device it lays out satisfies `JoltDevice.AdviceBelowInput`.

Rust: https://github.com/a16z/jolt/blob/754fc88214936801a7d8a2260d9fc73478be4cbd/common/src/jolt_device.rs#L346-L438

Arithmetic is on `Nat`. Each Rust `checked_*` call followed by `expect` becomes
a guard that returns `none` where Rust panics. Everything after `input_start`
in `new`, and its two power-of-two assertions on the advice sizes, only add
further panics and leave these fields unchanged; they are omitted, so
`adviceInputLayout` succeeds on at least every configuration Rust accepts.
-/

set_option autoImplicit false

namespace JoltConstraints.RustMemoryLayout

/-- The `MemoryConfig` fields that determine the advice and input regions. -/
structure MemoryConfig where
  maxTrustedAdviceSize : Nat
  maxUntrustedAdviceSize : Nat
  maxInputSize : Nat
  maxOutputSize : Nat

/-- Advice and input placement computed by `MemoryLayout::new`. -/
structure AdviceInputLayout where
  trustedAdviceStart : Nat
  trustedAdviceEnd : Nat
  untrustedAdviceStart : Nat
  untrustedAdviceEnd : Nat
  inputStart : Nat

/-- Rust `u64::checked_add`. -/
def checkedAdd (a b : Nat) : Option Nat :=
  if a + b < 2 ^ 64 then some (a + b) else none

/-- Rust `align_up(val, 8)`, which panics on overflow. -/
def alignUp8 (val : Nat) : Option Nat :=
  if val % 8 = 0 then some val else checkedAdd val (8 - val % 8)

/-- `MemoryLayout::new` up to `input_start`. The larger (or equal) advice region
goes first, at `RAM_START_ADDRESS - io_bytes`; the other starts where it ends;
`input_start` is the larger end. -/
def adviceInputLayout (config : MemoryConfig) : Option AdviceInputLayout := do
  let trusted ← alignUp8 config.maxTrustedAdviceSize
  let untrusted ← alignUp8 config.maxUntrustedAdviceSize
  let input ← alignUp8 config.maxInputSize
  let output ← alignUp8 config.maxOutputSize
  let ioRegionBytes ← (checkedAdd input trusted).bind fun s =>
    (checkedAdd s untrusted).bind fun s => (checkedAdd s output).bind fun s => checkedAdd s 16
  let ioBytes := (ioRegionBytes / 8).nextPowerOfTwo * 8
  if 2 ^ 64 ≤ ioBytes ∨ JoltISA.RAM_START_ADDRESS < ioBytes then none else
  let first := JoltISA.RAM_START_ADDRESS - ioBytes
  if untrusted ≤ trusted then
    let trustedEnd ← checkedAdd first trusted
    let untrustedEnd ← checkedAdd trustedEnd untrusted
    pure { trustedAdviceStart := first, trustedAdviceEnd := trustedEnd,
           untrustedAdviceStart := trustedEnd, untrustedAdviceEnd := untrustedEnd,
           inputStart := max untrustedEnd trustedEnd }
  else
    let untrustedEnd ← checkedAdd first untrusted
    let trustedEnd ← checkedAdd untrustedEnd trusted
    pure { trustedAdviceStart := untrustedEnd, trustedAdviceEnd := trustedEnd,
           untrustedAdviceStart := first, untrustedAdviceEnd := untrustedEnd,
           inputStart := max untrustedEnd trustedEnd }

theorem checkedAdd_eq_some {a b c : Nat} (h : checkedAdd a b = some c) : c = a + b := by
  unfold checkedAdd at h
  split at h <;> simp_all

theorem alignUp8_eq_some {val aligned : Nat} (h : alignUp8 val = some aligned) :
    val ≤ aligned ∧ aligned % 8 = 0 := by
  unfold alignUp8 at h
  split at h
  · simp_all
  · have := checkedAdd_eq_some h
    omega

/-- The arithmetic facts about a successful layout: each advice region has its
aligned size, the two regions are adjacent, and `input_start` is the larger end. -/
theorem adviceInputLayout_spec {config : MemoryConfig} {layout : AdviceInputLayout}
    (h : adviceInputLayout config = some layout) :
    ∃ trusted untrusted,
      config.maxTrustedAdviceSize ≤ trusted ∧ trusted % 8 = 0 ∧
      config.maxUntrustedAdviceSize ≤ untrusted ∧ untrusted % 8 = 0 ∧
      layout.trustedAdviceEnd = layout.trustedAdviceStart + trusted ∧
      layout.untrustedAdviceEnd = layout.untrustedAdviceStart + untrusted ∧
      (layout.untrustedAdviceStart = layout.trustedAdviceEnd ∨
        layout.trustedAdviceStart = layout.untrustedAdviceEnd) ∧
      layout.inputStart = max layout.untrustedAdviceEnd layout.trustedAdviceEnd := by
  unfold adviceInputLayout at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨trusted, htrusted, untrusted, huntrusted, _, _, _, _, _, _, h⟩ := h
  obtain ⟨hT, hT8⟩ := alignUp8_eq_some htrusted
  obtain ⟨hU, hU8⟩ := alignUp8_eq_some huntrusted
  refine ⟨trusted, untrusted, hT, hT8, hU, hU8, ?_⟩
  split at h
  · simp at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨trustedEnd, htEnd, untrustedEnd, huEnd, rfl⟩ := h
    have := checkedAdd_eq_some htEnd
    have := checkedAdd_eq_some huEnd
    simp only
    simp only [true_or, and_true]
    omega
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨untrustedEnd, huEnd, trustedEnd, htEnd, rfl⟩ := h
    have := checkedAdd_eq_some htEnd
    have := checkedAdd_eq_some huEnd
    simp only
    simp only [or_true, and_true]
    omega

end JoltConstraints.RustMemoryLayout

open JoltConstraints JoltConstraints.RustMemoryLayout in
/-- Every device Rust builds satisfies `AdviceBelowInput`: its layout comes from
`MemoryLayout::new`, and `create_emulator` rejects advice longer than the
configured maximum before execution starts.
Rust: https://github.com/a16z/jolt/blob/754fc88214936801a7d8a2260d9fc73478be4cbd/tracer/src/lib.rs#L382-L393 -/
theorem JoltDevice.AdviceBelowInput.of_memoryLayout
    (io : JoltDevice) (config : MemoryConfig) (layout : AdviceInputLayout)
    (built : adviceInputLayout config = some layout)
    (trustedStart : io.memory_layout.trusted_advice_start.toNat = layout.trustedAdviceStart)
    (untrustedStart : io.memory_layout.untrusted_advice_start.toNat = layout.untrustedAdviceStart)
    (inputStart : io.memory_layout.input_start.toNat = layout.inputStart)
    (trustedLength : io.trusted_advice.size ≤ config.maxTrustedAdviceSize)
    (untrustedLength : io.untrusted_advice.size ≤ config.maxUntrustedAdviceSize) :
    io.AdviceBelowInput := by
  obtain ⟨trusted, untrusted, hT, hT8, hU, hU8, htEnd, huEnd, hadj, hinput⟩ :=
    adviceInputLayout_spec built
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ramLowestAddress, trustedStart, untrustedStart, inputStart] <;> omega
