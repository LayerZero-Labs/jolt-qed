import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Soundness.Layer5.RuntimeAdvice
import JoltConstraints.advice_inputs

open LeanRV64D

/-!
# Inline advice on the proof side

`honestTracerAdviceAtStepN` gives an inline's VirtualAdvice step the next word of the
private input `inline_advice`, and every other advice step the value Jolt's tracer
computes (`builtinAdviceAtStepN`). Soundness reconstructs a run from a witness without
knowing the words in advance, so the reconstruction tracks only the built-in steps
(`BuiltinAdviceHonest`). At the end, `collectInlineAdvice` reads the words off the run's
inline advice steps, and `honest_of_builtin` shows the run is honest for private inputs
with those words. `UntrustedAnswerRun.withInlineAdvice` moves a run to such inputs: the
initial state does not read `inline_advice`.

For example, a run with one SECP256K1_MULQ call whose VirtualAdvice rows write
w0, w1, ... is honest for `inline_advice = #[w0, w1, ...]`.
-/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

section
variable {bytecode : Array JoltInstructionRow}

/-- The advice the honest tracer gives step `n` when step `n`'s expansion is not a
registered inline: the `n`-th step's share of `honestTracerAdvice`, computed from the
state before the expansion began. For example, a DIV's VirtualAdvice step gets the
quotient. On an inline's VirtualAdvice step it gives the bytecode placeholder, which
`honestTracerAdviceAtStepN` never uses (`honestTracerAdviceAtStepN_eq`).
See jolt/tracer/src/instruction/mod.rs:207-233 (`trace_inline_sequence_with_advice`). -/
def builtinAdviceAtStepN (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat) : Option (BitVec 64) := do
  let row ← rows[n]?
  let bytecodeValue ← bytecode[row.rowIndex].instruction.adviceValue?
  let first ← rows[startOfExpansionContainingStepN rows n]?
  let instruction ← program.instructionAt bytecode[first.rowIndex].address
  let values := instruction.honestTracerAdvice first.preState
  pure (values[adviceStepsBeforeStepN rows n]?.getD bytecodeValue)

/-- The honest advice at step `n` is the next inline advice word on an inline's advice
step and the built-in advice everywhere else. For example, on a DIV's advice step both
sides are the quotient, whatever `inline_advice` holds. -/
theorem honestTracerAdviceAtStepN_eq (program : Rv64ProgramImage SourceInstruction)
    (privateInputs : JoltPrivateInputs) (rows : Array (TraceRow bytecode)) (n : Nat) :
    honestTracerAdviceAtStepN program privateInputs rows n =
      if stepNOfTraceIsInlineAdvice program rows n then
        some (privateInputs.inline_advice[inlineAdviceStepsBeforeStepN program rows n]?.getD 0)
      else builtinAdviceAtStepN program rows n := by
  unfold honestTracerAdviceAtStepN builtinAdviceAtStepN stepNOfTraceIsInlineAdvice
    stepNOfTraceIsAdvice
  cases rowAt : rows[n]? with
  | none => simp
  | some row =>
    cases value : bytecode[(row.rowIndex : Nat)].instruction.adviceValue? with
    | none => simp [value]
    | some bytecodeValue =>
      cases firstAt : rows[startOfExpansionContainingStepN rows n]? with
      | none => simp [value]
      | some first =>
        cases source : program.instructionAt bytecode[(first.rowIndex : Nat)].address with
        | none => simp [value, source]
        | some instruction => cases instruction <;> simp [value, source]

/-- A row without VirtualAdvice records no advice and has no built-in advice.
For example, an ADD row has neither. -/
theorem runtimeAdvice_agrees_of_noAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Fin rows.size)
    (absent : bytecode[rows[n].rowIndex].instruction.adviceValue? = none) :
    rows[n].someTracerAdvice? = builtinAdviceAtStepN program rows n := by
  change (bytecode[rows[n].rowIndex].instruction.withRuntimeAdvice
    rows[n].runtimeAdvice).adviceValue? = _
  rw [withRuntimeAdvice_eq_of_noAdvice _ rows[n].runtimeAdvice absent, absent]
  simp only [builtinAdviceAtStepN, Array.getElem?_eq_getElem n.isLt, bind, Option.bind_some]
  change none = bytecode[rows[n].rowIndex].instruction.adviceValue?.bind _
  rw [absent]
  rfl

/-- Runtime advice keeps a row a VirtualAdvice row. For example, a VirtualAdvice row
patched with 5 records 5. -/
theorem adviceValue?_withRuntimeAdvice_isSome (instruction : Instr)
    (advice : instruction.RuntimeAdvice) :
    (instruction.withRuntimeAdvice advice).adviceValue?.isSome =
      instruction.adviceValue?.isSome := by
  cases instruction <;> rfl

/-- The steps up to `n` of a trace, read in the trace or in its first `m > n` steps,
agree. For example, row 1 is unchanged by a cut after row 3. -/
theorem extract_getElem?_before {α : Type} (rows : Array α)
    (m k : Nat) (within : m ≤ rows.size) (before : k < m) :
    (rows.extract 0 m)[k]? = rows[k]? := by
  simp only [Array.getElem?_extract, Nat.min_eq_left within, Nat.sub_zero,
    Nat.zero_add, ite_eq_left before]

/-- The flag that step `k` starts an expansion is unchanged by a later cut.
For example, an ECALL expansion start at row 2 remains a start after a cut at row 3. -/
theorem stepNOfTraceIsStartOfNewExpansion_extract (rows : Array (TraceRow bytecode))
    (m k : Nat) (within : m ≤ rows.size) (before : k < m) :
    stepNOfTraceIsStartOfNewExpansion (rows.extract 0 m) k =
      stepNOfTraceIsStartOfNewExpansion rows k := by
  simp only [stepNOfTraceIsStartOfNewExpansion, extract_getElem?_before rows m k within before]

/-- The expansion containing step `k` begins at the same step after a later cut.
For example, a DIV expansion starting at row 2 still starts there after a cut at row 4. -/
theorem startOfExpansionContainingStepN_extract (rows : Array (TraceRow bytecode))
    (m k : Nat) (within : m ≤ rows.size) (before : k < m) :
    startOfExpansionContainingStepN (rows.extract 0 m) k =
      startOfExpansionContainingStepN rows k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [startOfExpansionContainingStepN,
        stepNOfTraceIsStartOfNewExpansion_extract rows m (k + 1) within before]
      by_cases h : stepNOfTraceIsStartOfNewExpansion rows (k + 1)
      · simp [h]
      · simp [h, ih (by omega)]

/-- An expansion starts no later than any of its steps. For example, the expansion
containing step 7 starts at step 7 or earlier. -/
theorem startOfExpansionContainingStepN_le (rows : Array (TraceRow bytecode)) (k : Nat) :
    startOfExpansionContainingStepN rows k ≤ k := by
  induction k with
  | zero => simp [startOfExpansionContainingStepN]
  | succ k ih =>
      simp only [startOfExpansionContainingStepN]
      split <;> omega

/-- The VirtualAdvice flag of step `k` is unchanged by a later cut.
For example, row 2 remains an advice row after a cut at row 3. -/
theorem stepNOfTraceIsAdvice_extract (rows : Array (TraceRow bytecode))
    (m k : Nat) (within : m ≤ rows.size) (before : k < m) :
    stepNOfTraceIsAdvice (rows.extract 0 m) k = stepNOfTraceIsAdvice rows k := by
  simp only [stepNOfTraceIsAdvice, extract_getElem?_before rows m k within before]

/-- The number of earlier advice steps in step `i`'s expansion is unchanged by a later
cut. For example, a DIV's advice step still sees no earlier advice step. -/
theorem adviceStepsBeforeStepN_extract (rows : Array (TraceRow bytecode))
    (m i : Nat) (within : m ≤ rows.size) (earlier : i < m) :
    adviceStepsBeforeStepN (rows.extract 0 m) i = adviceStepsBeforeStepN rows i := by
  simp only [adviceStepsBeforeStepN, startOfExpansionContainingStepN_extract rows m i within earlier]
  congr 1
  apply List.filter_congr
  intro k member
  have below : k < i := by
    rw [List.mem_range'] at member
    obtain ⟨j, _, rfl⟩ := member
    omega
  exact stepNOfTraceIsAdvice_extract rows m k within (by omega)

/-- The built-in advice at step `i` depends only on steps up to `i`. For example,
cutting a five-row DIV trace after row 3 keeps row 2's advice. -/
theorem builtinAdviceAtStepN_extract (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (m i : Nat) (within : m ≤ rows.size) (earlier : i < m) :
    builtinAdviceAtStepN program (rows.extract 0 m) i = builtinAdviceAtStepN program rows i := by
  have start := startOfExpansionContainingStepN_le rows i
  simp only [builtinAdviceAtStepN, extract_getElem?_before rows m i within earlier,
    startOfExpansionContainingStepN_extract rows m i within earlier,
    adviceStepsBeforeStepN_extract rows m i within earlier,
    extract_getElem?_before rows m (startOfExpansionContainingStepN rows i) within (by omega)]

/-- Whether step `k` is an inline advice step is unchanged by a later cut. For example,
an advice step of a SECP256K1_MULQ call stays one after a cut later in the call. -/
theorem stepNOfTraceIsInlineAdvice_extract (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (m k : Nat) (within : m ≤ rows.size) (before : k < m) :
    stepNOfTraceIsInlineAdvice program (rows.extract 0 m) k =
      stepNOfTraceIsInlineAdvice program rows k := by
  have start := startOfExpansionContainingStepN_le rows k
  simp only [stepNOfTraceIsInlineAdvice, stepNOfTraceIsAdvice_extract rows m k within before,
    startOfExpansionContainingStepN_extract rows m k within before,
    extract_getElem?_before rows m (startOfExpansionContainingStepN rows k) within (by omega)]

/-- Every step that is not an inline advice step records its built-in advice. Inline
advice steps may record any word. For example, a run whose DIV records the honest
quotient and whose SECP256K1_MULQ call records arbitrary words satisfies this. -/
def BuiltinAdviceHonest (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) : Prop :=
  ∀ n : Fin rows.size, stepNOfTraceIsInlineAdvice program rows n = false →
    rows[n].someTracerAdvice? = builtinAdviceAtStepN program rows n

/-- `BuiltinAdviceHonest` holds for a prefix of a trace that satisfies it.
For example, the first three rows of an honest run satisfy it. -/
theorem BuiltinAdviceHonest.of_extract (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (m : Nat) (within : m ≤ rows.size)
    (honest : BuiltinAdviceHonest program rows) :
    BuiltinAdviceHonest program (rows.extract 0 m) := by
  intro n notInline
  have size : (rows.extract 0 m).size = m := by simp [Nat.min_eq_left within]
  have below : n.val < m := by have := n.isLt; omega
  rw [stepNOfTraceIsInlineAdvice_extract program rows m n within below] at notInline
  rw [builtinAdviceAtStepN_extract program rows m n within below]
  have same : (rows.extract 0 m)[n] = rows[n.val] := by
    simp only [Fin.getElem_fin, Array.getElem_extract, Nat.zero_add]
  rw [same]
  exact honest ⟨n.val, by omega⟩ notInline

/-- Appending a step keeps `BuiltinAdviceHonest` when the new step records its built-in
advice or is an inline advice step. For example, appending an ADD after a DIV keeps the
DIV's quotient honest. -/
theorem BuiltinAdviceHonest.push (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (step : TraceRow bytecode)
    (honest : BuiltinAdviceHonest program rows)
    (new : stepNOfTraceIsInlineAdvice program (rows.push step) rows.size = false →
      step.someTracerAdvice? = builtinAdviceAtStepN program (rows.push step) rows.size) :
    BuiltinAdviceHonest program (rows.push step) := by
  intro n notInline
  by_cases old : n.val < rows.size
  · have prefixRows : (rows.push step).extract 0 rows.size = rows := by
      rw [Array.extract_push_of_le (Nat.le_refl _), Array.extract_size]
    have within : rows.size ≤ (rows.push step).size := by simp
    have flag := stepNOfTraceIsInlineAdvice_extract program (rows.push step) rows.size n within old
    have value := builtinAdviceAtStepN_extract program (rows.push step) rows.size n within old
    rw [prefixRows] at flag value
    rw [← flag] at notInline
    rw [← value, show (rows.push step)[n] = rows[n.val] from Array.getElem_push_lt old]
    exact honest ⟨n.val, old⟩ notInline
  · have last : n.val = rows.size := by
      have inside := n.isLt
      simp only [Array.size_push] at inside
      omega
    have atLast : (rows.push step)[n] = step := by
      simp only [Fin.getElem_fin, last, Array.getElem_push_eq]
    rw [atLast]
    rw [last] at notInline ⊢
    exact new notInline

/-- Appending a row without VirtualAdvice keeps `BuiltinAdviceHonest`. For example,
appending an AND after a DIV does not change the DIV's quotient. -/
theorem BuiltinAdviceHonest.push_noAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (step : TraceRow bytecode)
    (honest : BuiltinAdviceHonest program rows)
    (absent : bytecode[step.rowIndex].instruction.adviceValue? = none) :
    BuiltinAdviceHonest program (rows.push step) := by
  apply BuiltinAdviceHonest.push program rows step honest
  intro _
  have agrees := runtimeAdvice_agrees_of_noAdvice program (rows.push step)
    ⟨rows.size, by simp⟩ (by simpa only [Fin.getElem_fin, Array.getElem_push_eq] using absent)
  simpa only [Fin.getElem_fin, Array.getElem_push_eq] using agrees

/-- The words a trace's inline advice steps record, in trace order. For example, a
trace with one SECP256K1_MULQ call whose advice rows record w0, w1, ... gives
`#[w0, w1, ...]`. -/
def collectInlineAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) : Array (BitVec 64) :=
  ((List.range rows.size).filterMap fun n =>
    if stepNOfTraceIsInlineAdvice program rows n then rows[n]?.bind (·.someTracerAdvice?)
    else none).toArray

/-- An inline advice step records a word. For example, a SECP256K1_MULQ advice row
records its runtime advice. -/
theorem someTracerAdvice?_isSome_of_inline (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat)
    (inline : stepNOfTraceIsInlineAdvice program rows n = true) :
    (rows[n]?.bind (·.someTracerAdvice?)).isSome = true := by
  simp only [stepNOfTraceIsInlineAdvice, stepNOfTraceIsAdvice, Bool.and_eq_true] at inline
  cases rowAt : rows[n]? with
  | none => simp [rowAt] at inline
  | some row =>
    simp only [rowAt, Option.bind_some] at inline ⊢
    rw [TraceRow.someTracerAdvice?, adviceValue?_withRuntimeAdvice_isSome]
    exact inline.1

private theorem length_filterMap_of_isSome {α β : Type} (f : α → Option β) (p : α → Bool)
    (l : List α) (same : ∀ x ∈ l, (f x).isSome = p x) :
    (l.filterMap f).length = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    have head := same x List.mem_cons_self
    have tail := ih (fun y member => same y (List.mem_cons_of_mem _ member))
    cases fx : f x with
    | none =>
      rw [fx, Option.isSome_none] at head
      simp [fx, ← head, tail]
    | some value =>
      rw [fx, Option.isSome_some] at head
      simp [fx, ← head, tail]

/-- The word an inline advice step records is the collected word at its index.
For example, the first advice step of a trace's second SECP256K1_MULQ call reads the
word after the first call's words. -/
theorem collectInlineAdvice_getElem? (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat) (inside : n < rows.size)
    (inline : stepNOfTraceIsInlineAdvice program rows n = true) :
    (collectInlineAdvice program rows)[inlineAdviceStepsBeforeStepN program rows n]? =
      rows[n]?.bind (·.someTracerAdvice?) := by
  let f := fun k => if stepNOfTraceIsInlineAdvice program rows k then
    rows[k]?.bind (·.someTracerAdvice?) else none
  have split : List.range rows.size =
      List.range n ++ (List.range (rows.size - n)).map (n + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  have before : ((List.range n).filterMap f).length = inlineAdviceStepsBeforeStepN program rows n := by
    apply length_filterMap_of_isSome
    intro k member
    have below := List.mem_range.mp member
    by_cases flag : stepNOfTraceIsInlineAdvice program rows k
    · simp only [f, flag, ite_true]
      exact someTracerAdvice?_isSome_of_inline program rows k flag
    · simp [f, flag]
  have rest : (List.range (rows.size - n)).map (n + ·) =
      n :: (List.range (rows.size - n - 1)).map (n + 1 + ·) := by
    obtain ⟨r, hr⟩ : ∃ r, rows.size - n = r + 1 := ⟨rows.size - n - 1, by omega⟩
    rw [hr, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map, Nat.add_sub_cancel]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    omega
  have atN : f n = rows[n]?.bind (·.someTracerAdvice?) := by simp [f, inline]
  obtain ⟨word, hword⟩ := Option.isSome_iff_exists.mp
    (someTracerAdvice?_isSome_of_inline program rows n inline)
  unfold collectInlineAdvice
  change (((List.range rows.size).filterMap f).toArray)[_]? = _
  rw [split, List.filterMap_append, rest, List.filterMap_cons, atN, hword, List.getElem?_toArray,
    ← before, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- A trace that records its built-in advice is honest for private inputs whose inline
advice words are the ones it records. For example, a run with one DIV and one
SECP256K1_MULQ call is honest for `inline_advice` set to the call's recorded words. -/
theorem honest_of_builtin (program : Rv64ProgramImage SourceInstruction)
    (privateInputs : JoltPrivateInputs) (rows : Array (TraceRow bytecode))
    (builtin : BuiltinAdviceHonest program rows) :
    ∀ n : Fin rows.size, rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN program
        { privateInputs with inline_advice := collectInlineAdvice program rows } rows n := by
  intro n
  rw [honestTracerAdviceAtStepN_eq]
  split
  · rename_i inline
    rw [collectInlineAdvice_getElem? program rows n n.isLt inline]
    obtain ⟨word, hword⟩ := Option.isSome_iff_exists.mp
      (someTracerAdvice?_isSome_of_inline program rows n inline)
    rw [hword]
    simp only [Array.getElem?_eq_getElem n.isLt, Option.bind_some] at hword
    simpa only [Fin.getElem_fin, Option.getD_some] using hword
  · rename_i notInline
    exact builtin n (by simpa using notInline)

end

/-- The same run, for private inputs with other inline advice words. The run's rows,
states and tape answers are unchanged, because initialization does not read
`inline_advice`. For example, a run for `inline_advice = #[]` is also a run for `#[5]`. -/
def UntrustedAnswerRun.withInlineAdvice {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (run : UntrustedAnswerRun joltInstance privateInputs)
    (words : Array (BitVec 64)) :
    UntrustedAnswerRun joltInstance { privateInputs with inline_advice := words } :=
  { run with initialized := run.initialized }

end JoltConstraints.Soundness
