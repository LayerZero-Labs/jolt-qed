import JoltConstraints.WholeRun.Blocks
import JoltConstraints.expansion_facts
import JoltBytecode.Inlines.Secp256k1.FieldDiv
import JoltBytecode.Inlines.Secp256k1.GlvrAdv

/-!
# Inline calls with Jolt's advice, in an honest trace

The per-call completeness lemmas of the secp256k1 inlines
(`secp256k1Mulq_rows_jolt_advice_complete` and its siblings in
`JoltBytecode/Inlines/Secp256k1/`) say that a call's rows run with the advice
words Jolt's host computes (`joltAdvice`, after `InlineOp::build_runtime_advice`
in `jolt-inlines/sdk/src/host.rs`, which calls the `build_advice` methods in
`jolt-inlines/secp256k1/src/sequence_builder.rs`). This file lifts them to a
call inside an honest trace: when the private input `inline_advice` holds those
words at the call's position, the trace's state after the call's last step
satisfies the inline's specification, and the stored result is canonical.

The lift has three parts.

* `patchAdvice` of the placeholder rows (`InlineKey.rows`, advice `fun _ => 0`)
  is the generated rows with the patched words as advice (`mulRows_patch`,
  `glvrAdvRows_patch`).
* The rows read only the first 4, 8 or 6 advice words (`mulRows_congr`,
  `glvrAdvRows_congr`).
* `HonestTrace.inline_call_exec` runs the patched rows from the state before the
  call to the state after its last step, and `Program.Run` is deterministic
  (`HonestTrace.inline_call_result`).

These theorems do not restrict the language: `JoltInstance.completeness` holds
for every passing inline advice, and these results say that Jolt's own advice
is one of them (design note `docs/inline-precompiles.md`, section 5.3).
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions
open JoltISA.Inlines JoltISA.Inlines.Secp256k1
open JoltISA (sourceValue)

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-! ## Patching advice into rows -/

/-- `patchAdvice` gives a VirtualAdvice row the first value, and passes the rest on.
Example: `patchAdvice [7, 9] [VirtualAdvice vr48 0 0, …]` starts with
`VirtualAdvice vr48 7 0` and patches the remaining rows with `[9]`. -/
theorem patchAdvice_virtualAdvice (values : List (BitVec 64)) (dst : JoltISA.Dst)
    (placeholder imm : BitVec 64) (rest : List JoltISA.Instr) :
    patchAdvice values (.VirtualAdvice dst placeholder imm :: rest) =
      .VirtualAdvice dst (values.getD 0 placeholder) imm :: patchAdvice values.tail rest := by
  cases values <;> rfl

/-- `patchAdvice` keeps a row that is not a VirtualAdvice.
Example: `patchAdvice [7] (LD vr48, 0(x10) :: rest)` is `LD vr48, 0(x10)` followed by
`patchAdvice [7] rest`. -/
theorem patchAdvice_of_none (values : List (BitVec 64)) (instruction : JoltISA.Instr)
    (rest : List JoltISA.Instr) (none : instruction.adviceValue? = none) :
    patchAdvice values (instruction :: rest) = instruction :: patchAdvice values rest := by
  cases instruction <;> first | rfl | cases none

/-- `patchAdvice` keeps a list without VirtualAdvice rows.
Example: `patchAdvice [7] (resetRows [vr48]) = resetRows [vr48]`. -/
theorem patchAdvice_of_forall_none (values : List (BitVec 64)) (instructions : List JoltISA.Instr)
    (none : ∀ instruction ∈ instructions, instruction.adviceValue? = none) :
    patchAdvice values instructions = instructions := by
  induction instructions with
  | nil => cases values <;> rfl
  | cons instruction rest ih =>
    rw [patchAdvice_of_none _ _ _ (none instruction List.mem_cons_self),
      ih fun other mem => none other (List.mem_cons_of_mem _ mem)]

/-- Patching a list whose tail has no VirtualAdvice rows patches only its front.
Example: `patchAdvice ws (prologueRows … ++ tail) = patchAdvice ws (prologueRows …) ++ tail`
when `tail` has no VirtualAdvice rows. -/
theorem patchAdvice_append_of_none (values : List (BitVec 64)) (front back : List JoltISA.Instr)
    (none : ∀ instruction ∈ back, instruction.adviceValue? = none) :
    patchAdvice values (front ++ back) = patchAdvice values front ++ back := by
  induction front generalizing values with
  | nil =>
    rw [List.nil_append, patchAdvice_of_forall_none values back none]
    cases values <;> rfl
  | cons instruction rest ih =>
    rw [List.cons_append]
    cases advice : instruction.adviceValue? with
    | none => rw [patchAdvice_of_none _ _ _ advice, patchAdvice_of_none _ _ _ advice, ih,
        List.cons_append]
    | some word =>
      obtain ⟨dst, placeholder, imm, rfl⟩ :
          ∃ dst placeholder imm, instruction = .VirtualAdvice dst placeholder imm := by
        cases instruction <;> first | exact ⟨_, _, _, rfl⟩ | cases advice
      rw [patchAdvice_virtualAdvice, patchAdvice_virtualAdvice, ih, List.cons_append]

private theorem getD_tail (values : List (BitVec 64)) (i : Nat) :
    values.tail.getD i 0 = values.getD (i + 1) 0 := by
  cases values <;> simp

/-! ## The field inlines -/

/-- How many advice words the rows of a field operation read: four quotient limbs for
MUL and SQUARE, and four result limbs interleaved with four quotient limbs for DIV
(`quotientWords` and `divisionWords`).
Example: `FieldOp.adviceCount .div = 8`. -/
def _root_.JoltISA.Inlines.Secp256k1.FieldOp.adviceCount : FieldOp → Nat
  | .mul | .square => 4
  | .div => 8

/-- The rows of a field inline after its operand loads and advice rows.
Example: for `SECP256K1_MULQ` they start with `LUI vr60 0x1000003d1`. -/
private def mulTail (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) :
    List JoltISA.Instr :=
  constRows scalar L ++ (col0Rows op L rs1 rs3 ++
    (((List.range' 1 6).flatMap fun k => colKRows op scalar L rs1 rs3 k) ++ (finalRows L ++
      ((if op = .div then storeRows L rs3 else []) ++
        resetRows ((List.range L.count).map fun i => vr (48 + i))))))

private theorem mulRows_split (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (advice : Nat → BitVec 64) :
    mulRows op scalar L rs1 rs2 rs3 advice =
      prologueRows op L rs1 rs2 advice ++ mulTail op scalar L rs1 rs3 := by
  simp only [mulRows, mulTail, List.append_assoc]

private theorem macRows_none (R : MacRegs) (first : Bool) (m : Mac) :
    ∀ instruction ∈ m.rows R first, instruction.adviceValue? = none := by
  cases m <;> cases first <;>
    simp [Mac.rows, Mac.addFirst, Mac.addCarry, JoltISA.Instr.adviceValue?]

private theorem colRows_none (R : MacRegs) :
    ∀ (first : Bool) (terms : List Mac),
      ∀ instruction ∈ colRows R first terms, instruction.adviceValue? = none
  | _, [] => by simp [colRows]
  | first, m :: terms => by
    intro instruction mem
    rcases List.mem_append.1 mem with mem | mem
    · exact macRows_none R first m instruction mem
    · exact colRows_none R false terms instruction mem

private theorem outRows_none (op : FieldOp) (L : MulRegs) (rs1 rs3 : regidx) (k : Nat) :
    ∀ instruction ∈ outRows op L rs1 rs3 k, instruction.adviceValue? = none := by
  unfold outRows
  split <;> (try cases op) <;> simp [ldRow, sdRow, JoltISA.Instr.adviceValue?]

private theorem mulTail_none (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs3 : regidx) :
    ∀ instruction ∈ mulTail op scalar L rs1 rs3, instruction.adviceValue? = none := by
  simp only [mulTail, List.forall_mem_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases scalar <;> simp [constRows, JoltISA.Instr.adviceValue?]
  · intro instruction mem
    rcases List.mem_cons.1 mem with rfl | mem
    · rfl
    rcases List.mem_append.1 mem with mem | mem
    · exact colRows_none _ true _ instruction mem
    · exact outRows_none op L rs1 rs3 0 instruction mem
  · intro instruction mem
    obtain ⟨k, -, mem⟩ := List.mem_flatMap.1 mem
    rcases List.mem_append.1 mem with mem | mem
    · exact colRows_none _ true _ instruction mem
    · exact outRows_none op L rs1 rs3 k instruction mem
  · simp [finalRows, JoltISA.Instr.adviceValue?]
  · split <;> simp [storeRows, sdRow, JoltISA.Instr.adviceValue?]
  · simp [resetRows, JoltISA.Instr.adviceValue?]

private theorem prologueRows_patch (op : FieldOp) (L : MulRegs) (rs1 rs2 : regidx)
    (values : List (BitVec 64)) :
    patchAdvice values (prologueRows op L rs1 rs2 fun _ => 0) =
      prologueRows op L rs1 rs2 fun i => values.getD i 0 := by
  cases op <;>
    simp only [prologueRows, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, ldRow, patchAdvice_virtualAdvice, getD_tail,
      patchAdvice_of_none _ (JoltISA.Instr.LD _ _ _ _) _ rfl] <;> rfl

/-- Patching words into a field inline's placeholder rows gives its rows with those
words as advice; a missing word is `0`.
Example: patching `[1, 0, 0, 0]` into the placeholder rows of `SECP256K1_MULQ` gives
its rows with quotient advice `w = 1`. -/
theorem mulRows_patch (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    (values : List (BitVec 64)) :
    patchAdvice values (mulRows op scalar L rs1 rs2 rs3 fun _ => 0) =
      mulRows op scalar L rs1 rs2 rs3 fun i => values.getD i 0 := by
  rw [mulRows_split, mulRows_split, patchAdvice_append_of_none _ _ _ (mulTail_none op scalar L rs1 rs3),
    prologueRows_patch]

/-- A field inline's rows read only the first `op.adviceCount` advice words.
Example: the rows of `SECP256K1_MULQ` are the same for any two advice functions that
agree on `0`, `1`, `2` and `3`. -/
theorem mulRows_congr (op : FieldOp) (scalar : Bool) (L : MulRegs) (rs1 rs2 rs3 : regidx)
    {advice advice' : Nat → BitVec 64} (agree : ∀ i < op.adviceCount, advice i = advice' i) :
    mulRows op scalar L rs1 rs2 rs3 advice = mulRows op scalar L rs1 rs2 rs3 advice' := by
  rw [mulRows_split, mulRows_split]
  congr 1
  cases op
  · simp only [prologueRows, List.flatMap_cons, List.flatMap_nil, agree 0 (by decide),
      agree 1 (by decide), agree 2 (by decide), agree 3 (by decide)]
  · simp only [prologueRows, List.flatMap_cons, List.flatMap_nil, agree 0 (by decide),
      agree 1 (by decide), agree 2 (by decide), agree 3 (by decide)]
  · simp only [prologueRows, List.flatMap_cons, List.flatMap_nil, agree 0 (by decide),
      agree 1 (by decide), agree 2 (by decide), agree 3 (by decide), agree 4 (by decide),
      agree 5 (by decide), agree 6 (by decide), agree 7 (by decide)]

/-! ## GLVR_ADV -/

/-- Patching words into the placeholder rows of `SECP256K1_GLVR_ADV` gives its rows with
those words as advice; a missing word is `0`.
Example: patching `[0, 1, 0, 0, 0, 0]` gives the rows that store `k₁ = 1`, `k₂ = 0`. -/
theorem glvrAdvRows_patch (rs1 rs2 rs3 : regidx) (values : List (BitVec 64)) :
    patchAdvice values (Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 fun _ => 0) =
      Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 fun i => values.getD i 0 := by
  rw [glvrAdvRowsAutoList_eq, glvrAdvRowsAutoList_eq,
    patchAdvice_append_of_none _ _ _ (by simp [JoltISA.Instr.adviceValue?])]
  simp only [glvrWords, adviceStoreRows, patchAdvice_virtualAdvice, getD_tail,
    patchAdvice_of_none _ (JoltISA.Instr.SD _ _ _) _ rfl]
  rfl

/-- The rows of `SECP256K1_GLVR_ADV` read only the first six advice words.
Example: `glvrAdvAdvice k` and `fun i => (glvrAdvice k).toList.getD i 0` give the same
rows. -/
theorem glvrAdvRows_congr (rs1 rs2 rs3 : regidx) {advice advice' : Nat → BitVec 64}
    (agree : ∀ i < 6, advice i = advice' i) :
    Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 advice =
      Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3 advice' := by
  rw [glvrAdvRowsAutoList_eq, glvrAdvRowsAutoList_eq]
  simp only [glvrWords, agree 0 (by decide), agree 1 (by decide), agree 2 (by decide),
    agree 3 (by decide), agree 4 (by decide), agree 5 (by decide)]

/-! ## The lift -/

/-- **An inline call with given advice, in an honest trace.** Let a source expansion start
at step `base` with the inline call `key rd=rs3, rs1, rs2`, for a key that reads `rs3`.
Since `SourceInstruction.expand` rejects `rs3 = x0` for such a key (decision D7), the call
runs the key's `rd ≠ x0` rows. Suppose the key's
rows are `rowsOf (fun _ => 0)` for a family `rowsOf` that reads only its first `count`
advice words, and that patching words into the placeholder rows gives `rowsOf` of those
words. If `inline_advice` holds `advice 0, …, advice (count - 1)` at the call's position,
then every run of `rowsOf advice` from the state before step `base` ends in the state
after the call's last step, `base + key.rowCount - 1`.
Example: for a SECP256K1_MULQ call at step 100 whose four quotient words sit in
`inline_advice`, any run of the rows with those words ends in the state after step 285. -/
theorem HonestTrace.inline_call_result {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs)
    (base : Nat) (hbase : base < trace.rows.size)
    (starts : trace.bytecode[(trace.rows[base]'hbase).rowIndex].starts_source = true)
    {key : InlineKey} {rs1 rs2 rs3 : regidx}
    (call : joltInstance.program.instructionAt
      trace.bytecode[(trace.rows[base]'hbase).rowIndex].address =
        some (.inline key rs1 rs2 rs3))
    (reads : key.readsRd = true)
    (rowsOf : (Nat → BitVec 64) → List JoltISA.Instr)
    (rowsEq : key.rows rs1 rs2 rs3 = rowsOf fun _ => 0)
    (patch : ∀ values, patchAdvice values (rowsOf fun _ => 0) = rowsOf fun i => values.getD i 0)
    (count : Nat) (short : count ≤ key.rowCount)
    (congr : ∀ advice advice' : Nat → BitVec 64, (∀ i < count, advice i = advice' i) →
      rowsOf advice = rowsOf advice')
    (advice : Nat → BitVec 64)
    (words : ∀ i < count, (inputs.inline_advice[inlineAdviceStepsBeforeStepN
      joltInstance.program trace.rows base + i]?).getD 0 = advice i)
    {s' : SailJoltState}
    (run : (JoltISA.Program.seq (rowsOf advice)).Run (trace.rows[base]'hbase).preState s') :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + key.rowCount - 1 ∧
      (trace.rows[last]'lastBound).postState = s' := by
  obtain ⟨source, rows, atSource, emits, address, lastBound, exec⟩ :=
    HonestTrace.inline_call_exec trace base hbase starts
  have isInline : source.instruction = .inline key rs1 rs2 rs3 := by
    rw [address, show joltInstance.program.instructionAt source.address =
      (rowAt joltInstance.program source.address).map (·.instruction) from rfl, atSource] at call
    exact Option.some.inj call
  have checks := ExpansionFacts.expand_instruction_checks source rows emits
  rw [isInline] at checks
  have rd : JoltISA.isX0 rs3 = false := by
    cases zero : JoltISA.isX0 rs3
    · rfl
    · have rejected : (SourceInstruction.inline key rs1 rs2 rs3).expand = none := by
        simp only [SourceInstruction.expand, zero, reads, Bool.and_self, ↓reduceIte]
      rw [rejected] at checks
      exact False.elim checks
  have registered : (SourceInstruction.inline key rs1 rs2 rs3).expand =
      some (.sequence (key.expandRows rs1 rs2 rs3)) := by
    simp only [SourceInstruction.expand, rd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [registered] at checks
  have expanded : rows.map (·.instruction) = key.expandRows rs1 rs2 rs3 := checks.1
  have mapped : rows.map (·.instruction) = rowsOf fun _ => 0 := by
    rw [expanded, InlineKey.expandRows, rd, ite_eq_right Bool.false_ne_true, rowsEq]
  have length : rows.length = key.rowCount := by
    have := congrArg List.length expanded
    rwa [List.length_map, InlineKey.expandRows_length] at this
  have patched : patchAdvice (inlineCallAdvice joltInstance.program inputs trace.rows base
      rows.length) (rows.map (·.instruction)) = rowsOf advice := by
    rw [mapped, patch]
    refine congr _ _ fun i hi => ?_
    have inside : i < rows.length := by omega
    rw [← words i hi]
    simp [inlineCallAdvice, List.getD_eq_getElem?_getD, List.getElem?_range inside]
  have done := exec key rs1 rs2 rs3 isInline
  rw [patched] at done
  refine ⟨base + rows.length - 1, lastBound, by rw [length], ?_⟩
  have both : JoltISA.execProgram (JoltISA.Program.seq (rowsOf advice))
      (trace.rows[base]'hbase).preState = .ok RETIRE_SUCCESS s' := run
  rw [done] at both
  cases both
  rfl

/-- The trace hypotheses shared by the secp256k1 lifts: a source expansion starts at step
`base` with the inline call `key rd=rs3, rs1, rs2`.
Example: a SECP256K1_MULQ call with `rd = x12` whose first row is step 100. -/
structure InlineCallAt {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs) (base : Nat)
    (key : InlineKey) (rs1 rs2 rs3 : regidx) : Prop where
  bound : base < trace.rows.size
  starts : trace.bytecode[(trace.rows[base]'bound).rowIndex].starts_source = true
  call : joltInstance.program.instructionAt
    trace.bytecode[(trace.rows[base]'bound).rowIndex].address = some (.inline key rs1 rs2 rs3)

/-- The private input `inline_advice` holds the words `ws` for the call at step `base`:
word `i` sits at index `i` past the inline advice steps before `base`.
Example: for the first SECP256K1_MULQ call of a trace, `inline_advice[0..3]` holds the
quotient `w`. -/
def HonestTrace.InlineWordsAt {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} (trace : HonestTrace joltInstance inputs) (base : Nat)
    (ws : List (BitVec 64)) : Prop :=
  ∀ i < ws.length, inputs.inline_advice[inlineAdviceStepsBeforeStepN
    joltInstance.program trace.rows base + i]? = ws[i]?

private theorem words_of_jolt {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} {trace : HonestTrace joltInstance inputs} {base : Nat}
    {ws : List (BitVec 64)} (jolt : HonestTrace.InlineWordsAt trace base ws) :
    ∀ i < ws.length, (inputs.inline_advice[inlineAdviceStepsBeforeStepN
      joltInstance.program trace.rows base + i]?).getD 0 = ws.getD i 0 := by
  intro i hi
  rw [jolt i hi, List.getD_eq_getElem?_getD]

private theorem quotient_length {advice : Option Limbs} {ws : List (BitVec 64)}
    (h : quotientWords <$> advice = some ws) : ws.length = 4 := by
  cases advice with
  | none => exact absurd h (by simp)
  | some w =>
    obtain rfl : quotientWords w = ws := Option.some.inj h
    simp [quotientWords]

private theorem division_length {advice : Option (Limbs × Limbs)} {ws : List (BitVec 64)}
    (h : (fun cw => divisionWords cw.1 cw.2) <$> advice = some ws) : ws.length = 8 := by
  cases advice with
  | none => exact absurd h (by simp)
  | some cw =>
    obtain rfl : divisionWords cw.1 cw.2 = ws := Option.some.inj h
    rfl

/-- A field inline call in an honest trace, run with words `ws` that `inline_advice` holds
at the call's position, ends in the state after the call's last step. -/
private theorem field_call_result {joltInstance : JoltInstance SourceInstruction}
    {inputs : JoltPrivateInputs} {trace : HonestTrace joltInstance inputs} {base : Nat}
    {key : InlineKey} {rs1 rs2 rs3 : regidx} (at_ : InlineCallAt trace base key rs1 rs2 rs3)
    (reads : key.readsRd = true) (op : FieldOp) (scalar : Bool) (L : MulRegs)
    (rowsOf : (Nat → BitVec 64) → List JoltISA.Instr)
    (keyRows : key.rows rs1 rs2 rs3 = rowsOf fun _ => 0)
    (rowsOf_eq : ∀ advice, rowsOf advice = mulRows op scalar L rs1 rs2 rs3 advice)
    (short : op.adviceCount ≤ key.rowCount)
    {ws : List (BitVec 64)} (len : ws.length = op.adviceCount) (jolt : HonestTrace.InlineWordsAt trace base ws)
    {s' : SailJoltState}
    (run : (JoltISA.Program.seq (rowsOf fun i => ws.getD i 0)).Run
      (trace.rows[base]'at_.bound).preState s') :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + key.rowCount - 1 ∧
      (trace.rows[last]'lastBound).postState = s' :=
  HonestTrace.inline_call_result trace base at_.bound at_.starts at_.call reads rowsOf keyRows
    (fun values => by rw [rowsOf_eq, rowsOf_eq]; exact mulRows_patch ..)
    op.adviceCount short
    (fun advice advice' agree => by
      rw [rowsOf_eq, rowsOf_eq]; exact mulRows_congr _ _ _ _ _ _ agree)
    (fun i => ws.getD i 0) (fun i hi => words_of_jolt jolt i (by omega)) run

/-! ## The seven secp256k1 inlines -/

/-- **SECP256K1_MULQ with Jolt's advice, in an honest trace.** Let the call
`SECP256K1_MULQ rd=rs3, rs1, rs2` start at step `base`, and let the state `s` before that
step meet the call's obligations, with operands `a` and `b` below `p` at `rs1` and `rs2`.
If `inline_advice` holds Jolt's quotient words for `a·b` at the call's position, then the
state after the call's last step meets `FieldMulSpec` and stores a canonical result.
Example: with `a = 2`, `b = (p+1)/2` and `inline_advice` holding `[1, 0, 0, 0]` at the
call's position, the state after the call's 186th step holds `1` at the address in `rs3`. -/
theorem HonestTrace.secp256k1Mulq_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Mulq rs1 rs2 rs3)
    (pre : FieldMulPre .mul rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a b : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hb : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs2) (trace.rows[base]'at_.bound).preState) = some b)
    (hca : limbsToNat a < p) (hcb : limbsToNat b < p)
    (jolt : ∀ ws, joltAdvice .mulq a b = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Mulq.rowCount - 1 ∧
      FieldMulSpec p .mul rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical p rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Mulq_rows_jolt_advice_complete pre ha hb hca hcb
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .mul false mulqRegs
    (Generated.secp256k1MulqRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1MulqRowsAutoList_eq rs1 rs2 rs3) (by decide) (quotient_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_MULR with Jolt's advice, in an honest trace.** As
`HonestTrace.secp256k1Mulq_jolt_advice_complete`, modulo `n`.
Example: with `a = 2`, `b = (n+1)/2` and `inline_advice` holding `[1, 0, 0, 0]` at the
call's position, the state after the call's 232nd step holds `1` at the address in `rs3`. -/
theorem HonestTrace.secp256k1Mulr_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Mulr rs1 rs2 rs3)
    (pre : FieldMulPre .mul rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a b : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hb : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs2) (trace.rows[base]'at_.bound).preState) = some b)
    (hca : limbsToNat a < n) (hcb : limbsToNat b < n)
    (jolt : ∀ ws, joltAdvice .mulr a b = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Mulr.rowCount - 1 ∧
      FieldMulSpec n .mul rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical n rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Mulr_rows_jolt_advice_complete pre ha hb hca hcb
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .mul true mulrRegs
    (Generated.secp256k1MulrRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1MulrRowsAutoList_eq rs1 rs2 rs3) (by decide) (quotient_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_SQUAREQ with Jolt's advice, in an honest trace.** As
`HonestTrace.secp256k1Mulq_jolt_advice_complete`, for the square of the operand `a` at
`rs1`.
Example: with `a = 2` and `inline_advice` holding `[0, 0, 0, 0]` at the call's position,
the state after the call's 167th step holds `4` at the address in `rs3`. -/
theorem HonestTrace.secp256k1Squareq_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Squareq rs1 rs2 rs3)
    (pre : FieldMulPre .square rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hca : limbsToNat a < p)
    (jolt : ∀ ws, joltAdvice .squareq a a = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Squareq.rowCount - 1 ∧
      FieldMulSpec p .square rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical p rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Squareq_rows_jolt_advice_complete pre ha hca
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .square false squareqRegs
    (Generated.secp256k1SquareqRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1SquareqRowsAutoList_eq rs1 rs2 rs3) (by decide) (quotient_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_SQUARER with Jolt's advice, in an honest trace.** As
`HonestTrace.secp256k1Squareq_jolt_advice_complete`, modulo `n`.
Example: with `a = 2` and `inline_advice` holding `[0, 0, 0, 0]` at the call's position,
the state after the call's 213th step holds `4` at the address in `rs3`. -/
theorem HonestTrace.secp256k1Squarer_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Squarer rs1 rs2 rs3)
    (pre : FieldMulPre .square rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hca : limbsToNat a < n)
    (jolt : ∀ ws, joltAdvice .squarer a a = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Squarer.rowCount - 1 ∧
      FieldMulSpec n .square rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical n rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Squarer_rows_jolt_advice_complete pre ha hca
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .square true squarerRegs
    (Generated.secp256k1SquarerRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1SquarerRowsAutoList_eq rs1 rs2 rs3) (by decide) (quotient_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_DIVQ with Jolt's advice, in an honest trace.** Let the call
`SECP256K1_DIVQ rd=rs3, rs1, rs2` start at step `base`, and let the state `s` before that
step meet the call's obligations, with a dividend `a` below `p` at `rs1` and a divisor `b`
nonzero modulo `p` at `rs2`. If `inline_advice` holds Jolt's eight words for `a / b` at the
call's position, then the state after the call's last step meets `FieldDivSpec` and stores
a canonical result.
Example: with `a = 1`, `b = 2` and `inline_advice` holding Jolt's words for
`c = (p+1)/2`, `w = 1`, the state after the call's 194th step holds `(p+1)/2` at the address
in `rs3`. -/
theorem HonestTrace.secp256k1Divq_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Divq rs1 rs2 rs3)
    (pre : FieldMulPre .div rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a b : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hb : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs2) (trace.rows[base]'at_.bound).preState) = some b)
    (hca : limbsToNat a < p) (hb0 : limbsToNat b % p ≠ 0)
    (jolt : ∀ ws, joltAdvice .divq a b = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Divq.rowCount - 1 ∧
      FieldDivSpec p rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical p rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Divq_rows_jolt_advice_complete pre ha hb hca hb0
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .div false mulqRegs
    (Generated.secp256k1DivqRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1DivqRowsAutoList_eq rs1 rs2 rs3) (by decide) (division_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_DIVR with Jolt's advice, in an honest trace.** As
`HonestTrace.secp256k1Divq_jolt_advice_complete`, modulo `n`.
Example: with `a = 1`, `b = 2` and `inline_advice` holding Jolt's words for
`c = (n+1)/2`, `w = 1`, the state after the call's 240th step holds `(n+1)/2` at the address
in `rs3`. -/
theorem HonestTrace.secp256k1Divr_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1Divr rs1 rs2 rs3)
    (pre : FieldMulPre .div rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState) {a b : Limbs}
    (ha : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some a)
    (hb : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs2) (trace.rows[base]'at_.bound).preState) = some b)
    (hca : limbsToNat a < n) (hb0 : limbsToNat b % n ≠ 0)
    (jolt : ∀ ws, joltAdvice .divr a b = some ws → HonestTrace.InlineWordsAt trace base ws) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1Divr.rowCount - 1 ∧
      FieldDivSpec n rs1 rs2 rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      FieldMulCanonical n rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨ws, hws, s', run, spec, canonical⟩ :=
    secp256k1Divr_rows_jolt_advice_complete pre ha hb hca hb0
  obtain ⟨last, lastBound, lastEq, post⟩ := field_call_result at_ rfl .div true mulrRegs
    (Generated.secp256k1DivrRowsAutoList rs1 rs2 rs3) rfl
    (secp256k1DivrRowsAutoList_eq rs1 rs2 rs3) (by decide) (division_length hws)
    (jolt ws hws) run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

/-- **SECP256K1_GLVR_ADV with Jolt's advice, in an honest trace.** Let the call
`SECP256K1_GLVR_ADV rd=rs3, rs1, rs2` start at step `base`, and let the state `s` before
that step meet the call's obligations, with the scalar `k` at `rs1`. If `inline_advice`
holds the six words of `glvrAdvice k` at the call's position, then the state after the
call's last step meets `GlvrAdvSpec` and its buffer holds `glvrAdvice k`.
Example: for `k = 1` and `inline_advice` holding `[0, 1, 0, 0, 0, 0]` at the call's
position, the buffer at `rs3` reads `[0, 1, 0, 0, 0, 0]` after the call's 13th step. -/
theorem HonestTrace.secp256k1GlvrAdv_jolt_advice_complete
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {trace : HonestTrace joltInstance inputs} {base : Nat} {rs1 rs2 rs3 : regidx}
    (at_ : InlineCallAt trace base .secp256k1GlvrAdv rs1 rs2 rs3)
    (pre : GlvrAdvPre rs3 (trace.rows[base]'at_.bound).preState) {k : Limbs}
    (hk : readLimbs? (trace.rows[base]'at_.bound).preState
      (sourceValue (.xreg rs1) (trace.rows[base]'at_.bound).preState) = some k)
    (jolt : HonestTrace.InlineWordsAt trace base (glvrAdvice k).toList) :
    ∃ last, ∃ lastBound : last < trace.rows.size, last = base + InlineKey.secp256k1GlvrAdv.rowCount - 1 ∧
      GlvrAdvSpec rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState ∧
      GlvrAdvCanonical k rs3 (trace.rows[base]'at_.bound).preState
        (trace.rows[last]'lastBound).postState := by
  obtain ⟨s', run, spec, canonical⟩ := glvrAdv_rows_jolt_advice_complete pre hk
  have words : ∀ i < 6, (inputs.inline_advice[inlineAdviceStepsBeforeStepN
      joltInstance.program trace.rows base + i]?).getD 0 = glvrAdvAdvice k i := by
    intro i hi
    rw [words_of_jolt jolt i (by simpa using hi), glvrAdvAdvice, dite_eq_left hi]
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨last, lastBound, lastEq, post⟩ := HonestTrace.inline_call_result trace base at_.bound at_.starts
    at_.call rfl (Generated.secp256k1GlvrAdvRowsAutoList rs1 rs2 rs3) rfl
    (glvrAdvRows_patch rs1 rs2 rs3) 6 (by decide)
    (fun _ _ agree => glvrAdvRows_congr rs1 rs2 rs3 agree) _ words run
  exact ⟨last, lastBound, lastEq, post ▸ spec, post ▸ canonical⟩

end WholeRun
