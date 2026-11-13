import JoltConstraints.WholeRun.InlineContract
import JoltConstraints.Completeness.completeness
import JoltConstraints.Soundness.Layer5.InlineAdvice

/-!
# Completeness with Jolt's inline advice (R4)

`JoltInstance.completeness` takes an honest trace, whose `inline_advice` may hold any words
that pass the inlines' own checks. Jolt's prover fills `inline_advice` with the words its
host computes: `InlineOp::build_runtime_advice` in `jolt-inlines/sdk/src/host.rs` calls the
`build_advice` methods in `jolt-inlines/secp256k1/src/sequence_builder.rs`, and the tracer
patches those words into the call's rows (`INLINE::trace_sequence` in
`tracer/src/instruction/inline.rs`). This file shows that completeness holds for those words.

* `InlineKey.joltWords` gives Jolt's words for one call, from the state before the call
  (`joltAdvice` with the operands read from memory). Hash inlines take no words.
* `joltInlineAdvice` gives Jolt's words for a whole trace, in trace order: each inline advice
  step takes the word that Jolt's words, patched into the call's rows, give that step.
* `InlineKey.JoltOutput` is what a call must store for its words to be Jolt's: a canonical
  result (`FieldMulCanonical`, `GlvrAdvCanonical`). For DIV it adds a dividend below `q` and
  a divisor nonzero modulo `q`; Jolt's prover panics on a zero divisor, and for a dividend at
  least `q` its quotient does not satisfy the rows' relation.
* `InlineKey.jolt_words_of_output`: a run of a call's rows that stores such an output used
  Jolt's words. The rows check `a·b = w·q + c` (or `c·b = w·q + a`) but not `c < q`, and a
  canonical `c` fixes `w` (`mulRows_advice_of_canonical`, `divRows_advice_of_canonical`).
  `GLVR_ADV` stores its six words unchanged (`glvrAdv_advice_of_canonical`).
* `JoltInstance.completeness_jolt_inline_advice`: if every call of an honest trace stores
  such an output, the trace with `inline_advice` replaced by `joltInlineAdvice` is an honest
  trace with the same rows, the same outputs and the same prover configuration, and its
  honest witness satisfies `AllConstraints`.

Termination, the prover configuration and the outputs are properties of the guest's run, so
the theorem takes an honest trace and keeps them, as `JoltInstance.completeness` does.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltISA JoltISA.Inlines JoltISA.Inlines.Secp256k1

set_option autoImplicit false

noncomputable section

/-! ## Jolt's words for one call -/

namespace JoltISA.Inlines.InlineKey

/-- Jolt's advice words for the call `key rd, rs1, rs2` from state `s`, in the order the
call's VirtualAdvice rows take them, or `none` where Jolt's host panics or a load fails.
The secp256k1 inlines read `a` at `rs1` and `b` at `rs2` (SQUARE reads `a` twice, and
`GLVR_ADV` reads the scalar at `rs1`) and pass them to `joltAdvice`
(`InlineOp::build_runtime_advice`, `jolt-inlines/sdk/src/host.rs`). The hash inlines take
no words.
Example: for `SECP256K1_MULQ` with `a = 2` at `rs1` and `b = (p+1)/2` at `rs2`, the words
are `[1, 0, 0, 0]`. -/
def joltWords : InlineKey → regidx → regidx → SailJoltState → Option (List (BitVec 64))
  | .secp256k1Mulq, rs1, rs2, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a =>
      (readLimbs? s (sourceValue (.xreg rs2) s)).bind fun b => joltAdvice .mulq a b
  | .secp256k1Mulr, rs1, rs2, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a =>
      (readLimbs? s (sourceValue (.xreg rs2) s)).bind fun b => joltAdvice .mulr a b
  | .secp256k1Squareq, rs1, _, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a => joltAdvice .squareq a a
  | .secp256k1Squarer, rs1, _, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a => joltAdvice .squarer a a
  | .secp256k1Divq, rs1, rs2, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a =>
      (readLimbs? s (sourceValue (.xreg rs2) s)).bind fun b => joltAdvice .divq a b
  | .secp256k1Divr, rs1, rs2, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun a =>
      (readLimbs? s (sourceValue (.xreg rs2) s)).bind fun b => joltAdvice .divr a b
  | .secp256k1GlvrAdv, rs1, _, s =>
    (readLimbs? s (sourceValue (.xreg rs1) s)).bind fun k => joltAdvice .glvrAdv k k
  | .sha256, _, _, _ | .sha256Init, _, _, _ | .keccak256, _, _, _
  | .keccak256AbsorbPermute, _, _, _ | .blake2, _, _, _ => some []

/-- The DIV operands for which Jolt's advice matches the rows: the dividend `a` at `rs1` is
below `q`, and the divisor `b` at `rs2` is nonzero modulo `q`. Jolt's prover panics when
`b ≡ 0 (mod q)`; for `a ≥ q` its quotient `⌊b·c / q⌋` satisfies `c·b = w·q + (a mod q)`,
not the rows' `c·b = w·q + a`.
Example: `a = 1`, `b = 2` meet it for `q = p`; `a = p`, `b = 1` do not. -/
def DivOperands (q : Nat) (rs1 rs2 : regidx) (s : SailJoltState) : Prop :=
  ∃ a b : Limbs, readLimbs? s (sourceValue (.xreg rs1) s) = some a ∧
    readLimbs? s (sourceValue (.xreg rs2) s) = some b ∧
    limbsToNat a < q ∧ limbsToNat b % q ≠ 0

/-- What the call `key rd, rs1, rs2` from state `s` to state `s'` must store for its advice
to be Jolt's. A secp256k1 call has its output buffer in RAM and stores Jolt's result: a
result below the modulus for MUL, SQUARE and DIV (with `DivOperands` for DIV), and Jolt's
split of the scalar at `rs1` for `GLVR_ADV`. A hash call takes no advice and needs nothing.
Example: a `SECP256K1_MULQ` call with `a·b = p + 1` must store `1`, not `p + 1`. -/
def JoltOutput : InlineKey → regidx → regidx → regidx → SailJoltState → SailJoltState → Prop
  | .secp256k1Mulq, _, _, rd, s, s' => FieldMulBuffer rd s ∧ FieldMulCanonical p rd s s'
  | .secp256k1Mulr, _, _, rd, s, s' => FieldMulBuffer rd s ∧ FieldMulCanonical n rd s s'
  | .secp256k1Squareq, _, _, rd, s, s' => FieldMulBuffer rd s ∧ FieldMulCanonical p rd s s'
  | .secp256k1Squarer, _, _, rd, s, s' => FieldMulBuffer rd s ∧ FieldMulCanonical n rd s s'
  | .secp256k1Divq, rs1, rs2, rd, s, s' =>
    FieldMulBuffer rd s ∧ FieldMulCanonical p rd s s' ∧ DivOperands p rs1 rs2 s
  | .secp256k1Divr, rs1, rs2, rd, s, s' =>
    FieldMulBuffer rd s ∧ FieldMulCanonical n rd s s' ∧ DivOperands n rs1 rs2 s
  | .secp256k1GlvrAdv, rs1, _, rd, s, s' =>
    GlvrAdvBuffer rd s ∧
      ∃ k, readLimbs? s (sourceValue (.xreg rs1) s) = some k ∧ GlvrAdvCanonical k rd s s'
  | .sha256, _, _, _, _, _ | .sha256Init, _, _, _, _, _ | .keccak256, _, _, _, _, _
  | .keccak256AbsorbPermute, _, _, _, _, _ | .blake2, _, _, _, _, _ => True

end JoltISA.Inlines.InlineKey

namespace WholeRun

/-- A MUL or SQUARE run that stores a canonical result used Jolt's quotient words. -/
private theorem mul_words {op : FieldOp} {scalar : Bool} {L : MulRegs} (hop : op ≠ .div)
    (hv : L.Valid op scalar) {rs1 rs2 rs3 : regidx} (values : List (BitVec 64))
    {s s' : SailJoltState} (buf : FieldMulBuffer rs3 s)
    (run : (Program.seq (patchAdvice values (mulRows op scalar L rs1 rs2 rs3 fun _ => 0))).Run
      s s')
    (canonical : FieldMulCanonical (if scalar then n else p) rs3 s s') :
    ∃ a b : Limbs, readLimbs? s (sourceValue (.xreg rs1) s) = some a ∧
      (op = .square → b = a) ∧
      (op ≠ .square → readLimbs? s (sourceValue (.xreg rs2) s) = some b) ∧
      ∃ w, mulqQuotientAdvice (if scalar then n else p) a b = some w ∧
        patchAdvice values (mulRows op scalar L rs1 rs2 rs3 fun _ => 0) =
          patchAdvice (quotientWords w) (mulRows op scalar L rs1 rs2 rs3 fun _ => 0) := by
  rw [mulRows_patch] at run
  obtain ⟨a, b, ha, hsq, hb, hw⟩ := mulRows_advice_of_canonical hop hv buf run canonical
  refine ⟨a, b, ha, hsq, hb, _, hw, ?_⟩
  rw [mulRows_patch, mulRows_patch]
  refine mulRows_congr _ _ _ _ _ _ fun i hi => ?_
  have four : i < 4 := by cases op <;> first | exact absurd rfl hop | exact hi
  interval_cases i <;> rfl

/-- A DIV run that stores a canonical result, with operands that meet `DivOperands`, used
Jolt's division words. -/
private theorem div_words {scalar : Bool} {L : MulRegs} (hv : L.Valid .div scalar)
    {rs1 rs2 rs3 : regidx} (values : List (BitVec 64)) {s s' : SailJoltState}
    (buf : FieldMulBuffer rs3 s)
    (run : (Program.seq (patchAdvice values (mulRows .div scalar L rs1 rs2 rs3 fun _ => 0))).Run
      s s')
    (canonical : FieldMulCanonical (if scalar then n else p) rs3 s s')
    (operands : InlineKey.DivOperands (if scalar then n else p) rs1 rs2 s) :
    ∃ a b : Limbs, readLimbs? s (sourceValue (.xreg rs1) s) = some a ∧
      readLimbs? s (sourceValue (.xreg rs2) s) = some b ∧
      ∃ cw, mulqDivisionAdvice (if scalar then n else p) a b = some cw ∧
        patchAdvice values (mulRows .div scalar L rs1 rs2 rs3 fun _ => 0) =
          patchAdvice (divisionWords cw.1 cw.2) (mulRows .div scalar L rs1 rs2 rs3 fun _ => 0) := by
  obtain ⟨a, b, ha, hb, hca, hb0⟩ := operands
  rw [mulRows_patch] at run
  have hcw := divRows_advice_of_canonical hv buf run canonical ha hb hca hb0
  refine ⟨a, b, ha, hb, _, hcw, ?_⟩
  rw [mulRows_patch, mulRows_patch]
  refine mulRows_congr _ _ _ _ _ _ fun i hi => ?_
  have eight : i < 8 := hi
  interval_cases i <;> rfl

/-- A `GLVR_ADV` run that leaves Jolt's split of `k` in the buffer used Jolt's words. -/
private theorem glvr_words {rs1 rs2 rs3 : regidx} (values : List (BitVec 64))
    {s s' : SailJoltState} (buf : GlvrAdvBuffer rs3 s)
    (run : (Program.seq (patchAdvice values
      (Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 fun _ => 0))).Run s s')
    {k : Limbs} (canonical : GlvrAdvCanonical k rs3 s s') :
    patchAdvice values (Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 fun _ => 0) =
      patchAdvice (glvrAdvice k).toList
        (Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 fun _ => 0) := by
  rw [glvrAdvRows_patch] at run
  have words := glvrAdv_advice_of_canonical buf run canonical
  rw [glvrAdvRows_patch, glvrAdvRows_patch]
  refine glvrAdvRows_congr _ _ _ fun i hi => (words i hi).trans ?_
  have inside : i < (glvrAdvice k).toList.length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some,
    Vector.getElem_toList]

end WholeRun

namespace JoltISA.Inlines.InlineKey

open WholeRun

/-- **A call that stores Jolt's output used Jolt's words.** Let the call `key rd, rs1, rs2`
be one that `SourceInstruction.expand` accepts. If a run of its rows, with words `values`
patched in, goes from `s` to a state `s'` that meets `JoltOutput`, then Jolt's words exist
and patching them in gives the same rows.
Example: a run of the `SECP256K1_MULQ` rows with `a = 2`, `b = (p+1)/2` that stores `1` had
`values` starting `1, 0, 0, 0`, which are Jolt's words. -/
theorem jolt_words_of_output (key : InlineKey) (rs1 rs2 rd : regidx)
    (accepted : key.readsRd = true → isX0 rd = false) (values : List (BitVec 64))
    {s s' : SailJoltState}
    (run : (Program.seq (patchAdvice values (key.expandRows rs1 rs2 rd))).Run s s')
    (output : key.JoltOutput rs1 rs2 rd s s') :
    ∃ ws, key.joltWords rs1 rs2 s = some ws ∧
      patchAdvice values (key.expandRows rs1 rs2 rd) = patchAdvice ws (key.expandRows rs1 rs2 rd) := by
  cases reads : key.readsRd
  · refine ⟨[], ?_, by rw [hash_patchAdvice key reads, hash_patchAdvice key reads]⟩
    cases key <;> first | rfl | exact absurd reads (by decide)
  have rdOk := accepted reads
  cases key <;> simp only [readsRd, Bool.false_eq_true] at reads <;>
    simp only [expandRows, rows, rdOk, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case secp256k1Mulq =>
    obtain ⟨buf, canonical⟩ := output
    rw [secp256k1MulqRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, -, hb, w, hw, patched⟩ :=
      mul_words (by decide) mulqRegs_valid values buf run canonical
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, hb (by decide), Option.bind_some, joltAdvice,
      Secp256k1Inline.modulus]
    rw [show mulqQuotientAdvice p a b = some w from hw]
    rfl
  case secp256k1Mulr =>
    obtain ⟨buf, canonical⟩ := output
    rw [secp256k1MulrRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, -, hb, w, hw, patched⟩ :=
      mul_words (by decide) mulrRegs_valid values buf run canonical
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, hb (by decide), Option.bind_some, joltAdvice,
      Secp256k1Inline.modulus]
    rw [show mulqQuotientAdvice n a b = some w from hw]
    rfl
  case secp256k1Squareq =>
    obtain ⟨buf, canonical⟩ := output
    rw [secp256k1SquareqRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, hsq, -, w, hw, patched⟩ :=
      mul_words (by decide) squareqRegs_valid values buf run canonical
    obtain rfl := hsq rfl
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, Option.bind_some, joltAdvice, Secp256k1Inline.modulus]
    rw [show mulqQuotientAdvice p b b = some w from hw]
    rfl
  case secp256k1Squarer =>
    obtain ⟨buf, canonical⟩ := output
    rw [secp256k1SquarerRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, hsq, -, w, hw, patched⟩ :=
      mul_words (by decide) squarerRegs_valid values buf run canonical
    obtain rfl := hsq rfl
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, Option.bind_some, joltAdvice, Secp256k1Inline.modulus]
    rw [show mulqQuotientAdvice n b b = some w from hw]
    rfl
  case secp256k1Divq =>
    obtain ⟨buf, canonical, operands⟩ := output
    rw [secp256k1DivqRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, hb, cw, hcw, patched⟩ :=
      div_words divqRegs_valid values buf run canonical operands
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, hb, Option.bind_some, joltAdvice, Secp256k1Inline.modulus]
    rw [show mulqDivisionAdvice p a b = some cw from hcw]
    rfl
  case secp256k1Divr =>
    obtain ⟨buf, canonical, operands⟩ := output
    rw [secp256k1DivrRowsAutoList_eq] at run ⊢
    obtain ⟨a, b, ha, hb, cw, hcw, patched⟩ :=
      div_words divrRegs_valid values buf run canonical operands
    refine ⟨_, ?_, patched⟩
    simp only [joltWords, ha, hb, Option.bind_some, joltAdvice, Secp256k1Inline.modulus]
    rw [show mulqDivisionAdvice n a b = some cw from hcw]
    rfl
  case secp256k1GlvrAdv =>
    obtain ⟨buf, k, hk, canonical⟩ := output
    refine ⟨_, ?_, glvr_words values buf run canonical⟩
    simp only [joltWords, hk, Option.bind_some, joltAdvice]

end JoltISA.Inlines.InlineKey

/-! ## Jolt's words for a whole trace -/

namespace WholeRun

open JoltConstraints.Soundness

section
variable {bytecode : Array JoltInstructionRow}

/-- Jolt's inline advice word for step `n`: if step `n`'s expansion is an inline call, the
advice of row `n - base` of the call's rows with Jolt's words patched in, where `base` is the
call's first step. This is the word Jolt's tracer records at step `n`
(`INLINE::trace_sequence`, `tracer/src/instruction/inline.rs`).
Example: for a SECP256K1_MULQ call at step 100 whose first VirtualAdvice row is row 17, step
117 gets the first quotient word. -/
def joltInlineWordAtStep (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) (n : Nat) : Option (BitVec 64) :=
  (rows[startOfExpansionContainingStepN rows n]?).bind fun first =>
    match program.instructionAt bytecode[first.rowIndex].address with
    | some (.inline key rs1 rs2 rd) =>
      (key.joltWords rs1 rs2 first.preState).bind fun ws =>
        ((patchAdvice ws (key.expandRows rs1 rs2 rd))[n - startOfExpansionContainingStepN rows n]?).bind
          (·.adviceValue?)
    | _ => none

/-- Jolt's inline advice for a trace: the words of `joltInlineWordAtStep` at the trace's
inline advice steps, in trace order. This is the `inline_advice` Jolt's prover builds.
Example: a trace with one SECP256K1_MULQ call with `a = 2`, `b = (p+1)/2` gives
`#[1, 0, 0, 0]`. -/
def joltInlineAdvice (program : Rv64ProgramImage SourceInstruction)
    (rows : Array (TraceRow bytecode)) : Array (BitVec 64) :=
  ((List.range rows.size).filterMap fun n =>
    if stepNOfTraceIsInlineAdvice program rows n then joltInlineWordAtStep program rows n
    else none).toArray

/-- The step where step `n`'s expansion starts is step `0` or a marked start. -/
private theorem start_marked (rows : Array (TraceRow bytecode)) (n : Nat) :
    startOfExpansionContainingStepN rows n = 0 ∨
      stepNOfTraceIsStartOfNewExpansion rows (startOfExpansionContainingStepN rows n) = true := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [startOfExpansionContainingStepN]
    split
    · next marked => exact Or.inr marked
    · exact ih

/-- A marked start at or before step `n` is at or before the start of step `n`'s
expansion. -/
private theorem le_start (rows : Array (TraceRow bytecode)) (j n : Nat) (before : j ≤ n)
    (marked : stepNOfTraceIsStartOfNewExpansion rows j = true) :
    j ≤ startOfExpansionContainingStepN rows n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [startOfExpansionContainingStepN]
    split
    · omega
    · next notMarked =>
      rcases Nat.lt_or_eq_of_le before with earlier | same
      · exact ih (by omega)
      · subst same
        exact absurd marked notMarked

end

/-- **Each inline advice step records Jolt's word.** In an honest trace whose inline calls all
store Jolt's output, the word an inline advice step records is `joltInlineWordAtStep`.
Example: the first VirtualAdvice step of a SECP256K1_MULQ call that stores `a·b mod p`
records the low limb of `⌊a·b / p⌋`. -/
private theorem inline_step_word {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (outputs : ∀ base key rs1 rs2 rd (call : InlineCallAt trace base key rs1 rs2 rd)
      (lastBound : base + key.rowCount - 1 < trace.rows.size),
      key.JoltOutput rs1 rs2 rd (trace.rows[base]'call.bound).preState
        (trace.rows[base + key.rowCount - 1]'lastBound).postState)
    (n : Nat) (hn : n < trace.rows.size)
    (inline : stepNOfTraceIsInlineAdvice joltInstance.program trace.rows n = true) :
    trace.rows[n]?.bind (·.someTracerAdvice?) =
      joltInlineWordAtStep joltInstance.program trace.rows n := by
  have flag := inline
  simp only [stepNOfTraceIsInlineAdvice, Bool.and_eq_true] at flag
  obtain ⟨-, flag⟩ := flag
  obtain ⟨key, rs1, rs2, rd, call⟩ : ∃ key rs1 rs2 rd,
      (trace.rows[startOfExpansionContainingStepN trace.rows n]?).bind
        (fun first => joltInstance.program.instructionAt trace.bytecode[first.rowIndex].address) =
        some (.inline key rs1 rs2 rd) := by
    split at flag
    · next key rs1 rs2 rd found => exact ⟨key, rs1, rs2, rd, found⟩
    · exact absurd flag (by simp)
  unfold joltInlineWordAtStep
  generalize hb : startOfExpansionContainingStepN trace.rows n = base at call ⊢
  have hbase : base < trace.rows.size := by
    by_contra outside
    rw [Array.getElem?_eq_none (by omega)] at call
    cases call
  rw [Array.getElem?_eq_getElem hbase, Option.bind_some] at call ⊢
  -- The call's first step starts a source expansion.
  have starts : trace.bytecode[(trace.rows[base]'hbase).rowIndex].starts_source = true := by
    rcases start_marked trace.rows n with zero | marked
    · rw [hb] at zero
      subst zero
      exact (trace.starts _ (Array.getElem?_eq_getElem hbase)).2.1
    · rw [hb] at marked
      simpa only [stepNOfTraceIsStartOfNewExpansion, Array.getElem?_eq_getElem hbase,
        Option.map_some, Option.getD_some] using marked
  obtain ⟨source, segment, atSource, emits, address, lastBound, -, next, exec⟩ :=
    HonestTrace.inline_call_exec trace base hbase starts
  have isInline : source.instruction = .inline key rs1 rs2 rd := by
    rw [address, show joltInstance.program.instructionAt source.address =
      (rowAt joltInstance.program source.address).map (·.instruction) from rfl, atSource] at call
    exact Option.some.inj call
  obtain ⟨accepted, rowsEq⟩ := inline_expand_rows emits isInline
  obtain ⟨ran, recorded⟩ := exec key rs1 rs2 rd isInline
  rw [rowsEq] at ran recorded
  -- Step `n` lies inside the call.
  have le : base ≤ n := hb ▸ startOfExpansionContainingStepN_le trace.rows n
  have lt : n < base + segment.length := by
    by_contra after
    have marked := next (by omega)
    have := le_start trace.rows (base + segment.length) n (by omega) marked
    have := List.length_pos_iff.mpr (expand_instruction_nonempty source segment emits)
    omega
  -- The call stores Jolt's output, so its words are Jolt's.
  have hlen : segment.length = key.rowCount := by
    have := congrArg List.length rowsEq
    rwa [List.length_map, InlineKey.expandRows_length] at this
  have lastBound' : base + key.rowCount - 1 < trace.rows.size := hlen ▸ lastBound
  have output := outputs base key rs1 rs2 rd ⟨hbase, starts, call⟩ lastBound'
  have same : trace.rows[base + segment.length - 1]'lastBound =
      trace.rows[base + key.rowCount - 1]'lastBound' := by
    simp only [hlen]
  rw [same] at ran
  obtain ⟨ws, hws, patchEq⟩ := InlineKey.jolt_words_of_output key rs1 rs2 rd accepted _ ran output
  obtain ⟨k, rfl⟩ : ∃ k, n = base + k := ⟨n - base, by omega⟩
  rw [Array.getElem?_eq_getElem hn, Option.bind_some, recorded k (by omega)]
  simp only [call, hws, Option.bind_some, Nat.add_sub_cancel_left, patchEq]

/-- **The recorded words are Jolt's.** In an honest trace whose inline calls all store Jolt's
output, the words the inline advice steps record are `joltInlineAdvice`.
Example: a trace whose one SECP256K1_MULQ call with `a = 2`, `b = (p+1)/2` stores `1`
records `#[1, 0, 0, 0]`. -/
theorem collectInlineAdvice_eq_joltInlineAdvice {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (outputs : ∀ base key rs1 rs2 rd (call : InlineCallAt trace base key rs1 rs2 rd)
      (lastBound : base + key.rowCount - 1 < trace.rows.size),
      key.JoltOutput rs1 rs2 rd (trace.rows[base]'call.bound).preState
        (trace.rows[base + key.rowCount - 1]'lastBound).postState) :
    collectInlineAdvice joltInstance.program trace.rows =
      joltInlineAdvice joltInstance.program trace.rows := by
  unfold collectInlineAdvice joltInlineAdvice
  congr 1
  refine List.filterMap_congr fun n member => ?_
  by_cases inline : stepNOfTraceIsInlineAdvice joltInstance.program trace.rows n = true
  · simp only [inline, ↓reduceIte]
    exact inline_step_word trace outputs n (List.mem_range.mp member) inline
  · simp only [inline, Bool.false_eq_true, ↓reduceIte]

/-! ## The honest trace with Jolt's words -/

/-- An honest trace records the honest tracer's advice at every step that is not an inline
advice step.
Example: the VirtualAdvice step of a DIV records the quotient. -/
theorem HonestTrace.builtinAdviceHonest {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs) :
    BuiltinAdviceHonest joltInstance.program trace.rows := by
  intro n notInline
  rw [trace.advice_from_honest_tracer n, honestTracerAdviceAtStepN_eq]
  simp only [notInline, Bool.false_eq_true, ↓reduceIte]

/-- An honest trace stays honest, with the same rows, when `inline_advice` is replaced by
the words its inline advice steps record. Initialization does not read `inline_advice`.
Example: a trace with one SECP256K1_MULQ call that records `[1, 0, 0, 0]` is honest for
`inline_advice = #[1, 0, 0, 0]`. -/
def HonestTrace.withInlineAdvice {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (words : Array (BitVec 64))
    (recorded : collectInlineAdvice joltInstance.program trace.rows = words) :
    HonestTrace joltInstance { inputs with inline_advice := words } :=
  { trace.toValidRun with
    initialized := trace.initialized
    accepted := trace.accepted
    valid_inputs := trace.valid_inputs
    advice_from_honest_tracer := by
      rw [← recorded]
      exact honest_of_builtin joltInstance.program inputs trace.rows
        (HonestTrace.builtinAdviceHonest trace)
    stops := trace.stops
    runs_until_stop := trace.runs_until_stop
    nonempty := trace.nonempty }

end WholeRun

open WholeRun in
/-- **Completeness with Jolt's inline advice.** Let an honest trace put the instance in
Jolt's language, and let every inline call in it store Jolt's output (`InlineKey.JoltOutput`):
a canonical result for MUL, SQUARE and DIV, with a dividend below the modulus and a divisor
nonzero modulo it for DIV, and Jolt's split of the scalar for `GLVR_ADV`. Then the trace
with `inline_advice` set to Jolt's words (`joltInlineAdvice`) is an honest trace with the
same rows, outputs and prover configuration, and the witness Jolt's prover builds from it
satisfies every modeled constraint.
Example: a guest that calls `SECP256K1_MULQ` on `a = 2`, `b = (p+1)/2` and stores `1` is
proved with `inline_advice = #[1, 0, 0, 0]`. -/
theorem JoltInstance.completeness_jolt_inline_advice {F : Type} [Field F]
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.CompletenessAssumptions)
    (privateInputs : JoltPrivateInputs)
    (trace : HonestTrace joltInstance privateInputs)
    (claimsRunOutputs : trace.matches_outputs joltInstance)
    (spoilAssertsPass : trace.SpoilAssertsPass)
    (config : ProverConfig)
    (proverAccepts : trace.prover_config joltInstance = some config)
    (joltOutputs : ∀ base key rs1 rs2 rd (call : InlineCallAt trace base key rs1 rs2 rd)
      (lastBound : base + key.rowCount - 1 < trace.rows.size),
      key.JoltOutput rs1 rs2 rd (trace.rows[base]'call.bound).preState
        (trace.rows[base + key.rowCount - 1]'lastBound).postState) :
    ∃ (jolt : HonestTrace joltInstance
        { privateInputs with inline_advice := joltInlineAdvice joltInstance.program trace.rows })
      (accepts : jolt.prover_config joltInstance = some config),
      jolt.toTrace = trace.toTrace ∧ jolt.matches_outputs joltInstance ∧ jolt.SpoilAssertsPass ∧
      JoltConstraints.AllConstraints joltInstance
        (JoltConstraints.adviceBlockWords jolt.initialState.jolt_device.memory_layout
          (TraceWitness.initialRamWord jolt))
        (HonestTrace.honestWitness (F := F) (jolt.witness_params config accepts) jolt) := by
  let jolt := HonestTrace.withInlineAdvice trace _
    (collectInlineAdvice_eq_joltInlineAdvice trace joltOutputs)
  exact ⟨jolt, proverAccepts, rfl, claimsRunOutputs, spoilAssertsPass,
    JoltInstance.completeness joltInstance assumptions _ jolt claimsRunOutputs
      spoilAssertsPass config proverAccepts⟩
