import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer7.LastJump
import JoltConstraints.prover_config_facts
import JoltConstraints.Soundness.Layer3.Address
import JoltConstraints.Soundness.Layer3.State

set_option autoImplicit false

namespace JoltInstance

/-- From the last represented stable branch onward, every witness cycle has
nonzero next unexpanded PC: the branch replays and cannot enter padding.
For example, a taken `BEQ x1, x1, 0` keeps its source address through every
remaining real cycle, contradicting the final zero shift.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`NextUnexpandedPc::extract`)
and jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs
(`rv64_eq_constraint_rows`) at 5def437f. -/
theorem represented_branch_stall_replays
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (stable : last.StableStall)
    (branch : JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true) :
    ∀ cycle : Fin params.traceLength, run.rows.size - 1 ≤ cycle.val →
      witness.NextUnexpandedPC cycle ≠ 0 := by
  obtain ⟨before, beforeEq, real, atBefore⟩ :=
    represented_last_branch_invariant joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last atEnd branch
  have replay (n : Nat) (lower : before.val ≤ n) (bound : n < params.traceLength) :
      witness.InstructionFlags .IsNoop ⟨n, bound⟩ ≠ 1 ∧
        StallSuffixInvariant witness run.bytecode last ⟨n, bound⟩ := by
    induction n, lower using Nat.le_induction with
    | base => exact ⟨by simpa only [real] using (zero_ne_one : (0 : F) ≠ 1), atBefore⟩
    | succ n lower ih =>
        have previousBound : n < params.traceLength := by omega
        let previous : Fin params.traceLength := ⟨n, previousBound⟩
        obtain ⟨notPadding, invariant⟩ := ih previousBound
        obtain ⟨targetNonzero, nextInvariant⟩ := stall_branch_replay joltField
          joltInstance privateInputs witness context equations run bytecodeEq last
          atEnd stable branch previous notPadding invariant
        refine ⟨?_, nextInvariant bound⟩
        intro padding
        have nextZero := unexpanded_zero_of_padding joltField joltInstance privateInputs
          witness context equations ⟨n + 1, bound⟩ padding
        apply targetNonzero
        have shifted := equations.nextUnexpandedPCEqShift previous
        simpa only [previous, dif_pos bound, nextZero] using shifted
  intro cycle afterLast
  obtain ⟨notPadding, invariant⟩ := replay cycle.val (by omega) cycle.isLt
  exact (stall_branch_replay joltField joltInstance privateInputs witness context
    equations run bytecodeEq last atEnd stable branch cycle notPadding invariant).1

/-- A represented completed relaxed execution passes the prover's last-row
check: it is empty or its final instruction is JAL or JALR.
The trace supplies execution and stopping certificates, while representation
identifies its row observations with the constrained witness.
For example, a taken BEQ with offset zero is a stable stall, but cannot end
such a represented trace because its nonzero target cannot reach witness padding
or the final zero PC shift.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`) at 5def437f. -/
theorem represented_trace_ends_in_jump
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : RepresentsRows witness trace.toUntrustedAnswerRun.toTrace) :
    trace.rows.size = 0 ∨ trace.execution_dimensions.ends_in_jump = true := by
  have lastIn : trace.rows.size - 1 < trace.rows.size := by
    have nonempty := trace.nonempty
    omega
  let last := trace.rows[trace.rows.size - 1]
  have back : trace.rows.back? = some last := by
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem lastIn]
  have atEnd : last ∈ trace.rows.back? := by simp only [back, Option.mem_some_iff]
  have stable := trace.stops last atEnd
  right
  rcases stable_stall_control_flow joltInstance privateInputs
      trace.toUntrustedAnswerRun last atEnd stable with
    ⟨dst, imm, jump⟩ | ⟨dst, base, imm, jump⟩ | branch
  · simp only [Trace.execution_dimensions, back, Option.any_some, jump, JoltISA.Instr.is_jump]
  · simp only [Trace.execution_dimensions, back, Option.any_some, jump, JoltISA.Instr.is_jump]
  · have positive : 0 < params.traceLength := lt_of_lt_of_le trace.nonempty represented.rowsBound
    let finalCycle : Fin params.traceLength := ⟨params.traceLength - 1, by omega⟩
    have nonzero := represented_branch_stall_replays joltField joltInstance privateInputs
      witness context equations trace.toUntrustedAnswerRun bytecodeEq represented
      last atEnd stable branch finalCycle (by
        have rowsBound := represented.rowsBound
        dsimp [finalCycle]
        omega)
    have noNext : ¬ finalCycle.val + 1 < params.traceLength := by
      dsimp [finalCycle]
      omega
    exact False.elim (nonzero (by
      simpa only [dif_neg noNext] using equations.nextUnexpandedPCEqShift finalCycle))

/-- Checked padding adds a no-op, rounds up to a power of two and enforces the
256-cycle floor, within a 64-bit public maximum.
The row count fits a power-of-two witness domain within that maximum and differs
from the largest admissible power of two; the caller obtains this last condition
from `NoMaxLengthTrace`.
For example, 256 rows under maximum 1024 pad to 512, while 1024 rows are excluded.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`) and jolt/crates/jolt-verifier/src/config.rs
(`MIN_PADDED_TRACE_LENGTH`, base/Dory) at 5def437f. -/
theorem checked_trace_length_fits
    (rows logT : Nat) (maximum : BitVec 64)
    (rowsBound : rows ≤ 2 ^ logT)
    (witnessBound : 2 ^ logT ≤ maximum.toNat)
    (floor : 256 ≤ maximum.toNat)
    (notMax : rows ≠ 2 ^ Nat.log2 maximum.toNat) :
    ∃ padded, ProverConfig.checkedTraceLength rows = some padded ∧
      padded ≤ maximum.toNat := by
  let maxPower := 2 ^ Nat.log2 maximum.toNat
  have maximumPositive : maximum.toNat ≠ 0 := by omega
  have maxPowerBound : maxPower ≤ maximum.toNat := by
    dsimp [maxPower]
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 maximumPositive
  have exponentBound : logT ≤ Nat.log2 maximum.toNat := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by decide : 1 < 2) witnessBound
  have rowsBound' : rows ≤ maxPower :=
    rowsBound.trans (Nat.pow_le_pow_right (by decide) exponentBound)
  have withNoopBound : rows + 1 ≤ maxPower := by
    have different : rows ≠ maxPower := notMax
    omega
  have roundedExponentBound : Nat.clog 2 (rows + 1) ≤ Nat.log2 maximum.toNat :=
    Nat.clog_le_of_le_pow withNoopBound
  have roundedBound : 2 ^ Nat.clog 2 (rows + 1) ≤ maxPower :=
    Nat.pow_le_pow_right (by decide) roundedExponentBound
  have withNoopFits : rows + 1 < 2 ^ 64 :=
    lt_of_le_of_lt (withNoopBound.trans maxPowerBound) maximum.isLt
  have roundedFits : 2 ^ Nat.clog 2 (rows + 1) < 2 ^ 64 :=
    lt_of_le_of_lt (roundedBound.trans maxPowerBound) maximum.isLt
  have added : MemoryLayout.checkedAdd rows 1 = some (rows + 1) := by
    simp only [MemoryLayout.checkedAdd, if_pos withNoopFits]
  have rounded : JoltConstraints.VerifierSizes.checkedNextPowerOfTwo (rows + 1) =
      some (2 ^ Nat.clog 2 (rows + 1)) := by
    simp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo, if_pos roundedFits]
  refine ⟨max (2 ^ Nat.clog 2 (rows + 1)) 256, ?_, ?_⟩
  · simp [ProverConfig.checkedTraceLength, added, rounded]
  · exact max_le (roundedBound.trans maxPowerBound) floor

/-- Represented row addresses fit in 64 bits and, unless zero, lie at or above
the constraint layout's lowest address.
For example, a selected RAM index 3 records an address 24 bytes above that base.
See jolt/crates/jolt-prover/src/config.rs (`checked_remap_address`) at 5def437f. -/
theorem represented_ram_addresses_bounded
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : Trace) (rowsBound : trace.rows.size ≤ params.traceLength)
    (ramAddress : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
      witness.RamAddress t = TraceWitness.RamAddress params trace t) :
    ∀ address ∈ trace.rows.toList.filterMap (·.ram_address),
      address < 2 ^ 64 ∧
        (address = 0 ∨ JoltConstraints.ramLowestAddress context.io.memory_layout ≤ address) := by
  intro address member
  obtain ⟨row, rowMem, touches⟩ := List.mem_filterMap.mp member
  refine ⟨row.ram_address_lt address touches, ?_⟩
  by_cases zero : address = 0
  · exact Or.inl zero
  right
  obtain ⟨index, inRun, rowAt⟩ := Array.mem_iff_getElem.mp (by simpa using rowMem)
  let cycle : Fin params.traceLength := ⟨index, lt_of_lt_of_le inRun rowsBound⟩
  rw [TraceRow.ram_address_eq] at touches
  obtain ⟨raw, access, rawEq⟩ := Option.map_eq_some_iff.mp touches
  have encoded : witness.RamAddress cycle = (raw.toNat : F) := by
    simp only [Fin.getElem_fin] at access
    rw [ramAddress cycle inRun]
    simp only [TraceWitness.RamAddress, cycle, dif_pos inRun, rowAt, access]
  have charBound := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  have nonzero : witness.RamAddress cycle ≠ 0 := by
    intro vanishes
    have rawZero : raw = (0 : BitVec 64) :=
      JoltConstraints.Soundness.word_eq_of_field_eq charBound
        (by simpa using encoded.symm.trans vanishes)
    exact zero (by simpa only [rawZero, BitVec.toNat_zero] using rawEq.symm)
  obtain ⟨chosen, selected, _⟩ := JoltConstraints.Soundness.ramRa_unique_of_address_ne_zero
    charBound context equations cycle nonzero
  have addressEq := JoltConstraints.Soundness.ramAddress_eq_of_selected
    charBound context equations cycle chosen selected raw encoded
  omega

/-- Folding bounded addresses makes checked remapping succeed, with the largest
touched word index below `2 ^ 61`.
Zero is ignored; for example, `[0, lowest + 24]` yields word index 3.
See jolt/crates/jolt-program/src/execution/trace.rs (`RamAddressBounds::observe`)
and jolt/crates/jolt-prover/src/config.rs (`checked_remap_address`) at 5def437f. -/
theorem checked_touched_of_address_bounds (addresses : List Nat) (layout : MemoryLayout)
    (bounded : ∀ address ∈ addresses, address < 2 ^ 64 ∧
      (address = 0 ∨ layout.get_lowest_address.toNat ≤ address)) :
    ∃ touched, ProverConfig.checkedTouched
        (addresses.foldl ExecutionDimensions.observe none) layout = some touched ∧
      touched < 2 ^ 61 := by
  have valid := ExecutionDimensions.boundsFor_fold addresses
  cases bounds : addresses.foldl ExecutionDimensions.observe none with
  | none => exact ⟨0, rfl, by norm_num⟩
  | some pair =>
      rcases pair with ⟨lo, hi⟩
      rw [bounds] at valid
      obtain ⟨loMem, hiMem, loNonzero, hiNonzero, _⟩ := valid
      obtain ⟨_, loAbove⟩ := bounded lo loMem
      obtain ⟨hiFits, hiAbove⟩ := bounded hi hiMem
      have loBound := loAbove.resolve_left loNonzero
      have hiBound := hiAbove.resolve_left hiNonzero
      refine ⟨(hi - layout.get_lowest_address.toNat) / 8, ?_, by omega⟩
      simp [ProverConfig.checkedTouched, MemoryLayout.checkedSub, loBound, hiBound]

/-- Successful ordered verifier RAM sizes bound the program image's exclusive
word end by `2 ^ 61` and certify its remapping and checked addition.
For example, an image starting at word 3 with two words has exclusive end 5;
the prover will subsequently add its extra sentinel word.
See jolt/crates/jolt-program/src/preprocess/ram.rs
(`compute_min_ram_k`, `compute_max_ram_k`) at 5def437f. -/
theorem verifier_ram_image_end_bounded {Source : Type}
    (program : Rv64ProgramImage Source) (layout : MemoryLayout) (minimum maximum : Nat)
    (minimumComputed : JoltConstraints.VerifierSizes.minRamSize program layout = some minimum)
    (maximumComputed : JoltConstraints.VerifierSizes.maxRamSize layout = some maximum)
    (ordered : minimum ≤ maximum) :
    ∃ start finish,
      JoltConstraints.VerifierSizes.remapWordAddress layout
        (min_bytecode_address program.memory_init) = some start ∧
      MemoryLayout.checkedAdd (start.getD 0) (program_image_len_words program.memory_init) =
        some finish ∧ finish ≤ 2 ^ 61 := by
  unfold JoltConstraints.VerifierSizes.maxRamSize at maximumComputed
  obtain ⟨totalBytes, subtracted, rounded⟩ := Option.bind_eq_some_iff.mp maximumComputed
  obtain ⟨rfl, _⟩ := checkedSub_some subtracted
  have wordsBound : (layout.heap_end.toNat - layout.get_lowest_address.toNat) / 8 ≤ 2 ^ 61 := by
    have fits := layout.heap_end.isLt
    omega
  have maximumBound : maximum ≤ 2 ^ 61 := by
    rw [(ProverConfig.checkedRound_some _ _ rounded).1]
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow wordsBound)
  unfold JoltConstraints.VerifierSizes.minRamSize at minimumComputed
  obtain ⟨start, remapped, minimumComputed⟩ := Option.bind_eq_some_iff.mp minimumComputed
  obtain ⟨finish, added, minimumComputed⟩ := Option.bind_eq_some_iff.mp minimumComputed
  obtain ⟨ioEnd, _, minimumComputed⟩ := Option.bind_eq_some_iff.mp minimumComputed
  cases ioEnd with
  | none => simp at minimumComputed
  | some ioEnd =>
      have minimumEq := (ProverConfig.checkedRound_some _ _ minimumComputed).1
      have imageBound : finish ≤ minimum := by
        rw [minimumEq]
        exact (Nat.le_max_left _ _).trans (Nat.le_pow_clog (by decide) _)
      exact ⟨start, finish, remapped, added, imageBound.trans (ordered.trans maximumBound)⟩

/-- Represented RAM addresses and the verifier's RAM bounds make checked prover
RAM sizing succeed for a trace with the instance's initial state.
Only the row-count bound and RAM-address observations are needed from row
representation; no execution or final-memory agreement is assumed here.
Every nonzero address is the layout base plus eight times a selected RAM index;
for example, selected index 3 gives a byte address 24 above that base.
The verifier bounds the image end, and 64-bit addresses bound the touched slots,
so adding the image sentinel and rounding cannot overflow the 64-bit host size.
See jolt/crates/jolt-prover/src/config.rs
(`ProverConfig::derive_from_dimensions`, `checked_remap_address`) and
jolt/crates/jolt-program/src/preprocess/ram.rs
(`compute_min_ram_k`, `compute_max_ram_k`) at 5def437f. -/
theorem represented_ram_size_computes
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : Trace)
    (initialized : joltInstance.initial_state privateInputs = some trace.initialState)
    (rowsBound : trace.rows.size ≤ params.traceLength)
    (ramAddress : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
      witness.RamAddress t = TraceWitness.RamAddress params trace t) :
    ∃ ramK, ProverConfig.checkedRamSize trace.execution_dimensions
      trace.initialState.jolt_device.memory_layout
      (min_bytecode_address joltInstance.program.memory_init)
      (program_image_len_words joltInstance.program.memory_init) = some ramK := by
  let layout := trace.initialState.jolt_device.memory_layout
  have layoutBuilt := (initial_state_device joltInstance privateInputs trace.initialState initialized).1
  have sameLayout := JoltConstraints.Soundness.initial_state_memory_layout context initialized
  have addressesBound := represented_ram_addresses_bounded joltField joltInstance privateInputs
    witness context equations trace rowsBound ramAddress
  obtain ⟨touched, touchedComputed, touchedBound⟩ := checked_touched_of_address_bounds
    (trace.rows.toList.filterMap (·.ram_address)) layout (by
      simpa only [layout, sameLayout, MemoryLayout.get_lowest_address_toNat,
        JoltConstraints.ramLowestAddress] using addressesBound)
  have sizes := context.ramSizeBounds
  unfold ram_size_in_bounds at sizes
  cases bounds : joltInstance.verifier_ram_bounds with
  | none => simp [bounds] at sizes
  | some pair =>
      rcases pair with ⟨minimum, maximum⟩
      have ordered : minimum ≤ maximum := by
        have limits : minimum ≤ params.ramSize ∧ params.ramSize ≤ maximum := by
          simpa only [bounds, decide_eq_true_eq] using sizes
        exact limits.1.trans limits.2
      unfold verifier_ram_bounds at bounds
      rw [layoutBuilt] at bounds
      simp only [bind_some_iff, Option.some.injEq] at bounds
      obtain ⟨_, rfl, minSize, minimumComputed, maxSize, maximumComputed, result⟩ := bounds
      have pairEq : (minSize, maxSize) = (minimum, maximum) := Option.some.inj result
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
      obtain ⟨start, finish, remapped, added, finishBound⟩ :=
        verifier_ram_image_end_bounded joltInstance.program layout minSize maxSize
          minimumComputed maximumComputed ordered
      have sentinelFits : finish + 1 < 2 ^ 64 := by omega
      have totalBound : max touched (finish + 1) ≤ 2 ^ 62 := by omega
      have roundedBound : 2 ^ Nat.clog 2 (max touched (finish + 1)) ≤ 2 ^ 62 :=
        Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow totalBound)
      have roundedFits : 2 ^ Nat.clog 2 (max touched (finish + 1)) < 2 ^ 64 := by omega
      refine ⟨2 ^ Nat.clog 2 (max touched (finish + 1)), ?_⟩
      simp only [ProverConfig.checkedRamSize, bind_some_iff]
      refine ⟨touched, touchedComputed, start, remapped, finish, added, finish + 1, ?_, ?_⟩
      · simp only [MemoryLayout.checkedAdd, if_pos sentinelFits]
      · simp only [JoltConstraints.VerifierSizes.checkedNextPowerOfTwo, if_pos roundedFits]

end JoltInstance
