import JoltConstraints.Constraints.RegistersValProofHelpers
import Batteries.Data.Fin.Fold

set_option autoImplicit false

open scoped BigOperators

namespace JoltConstraints

private theorem register42_prefix_sum_succ
    {F : Type} [Field F] {N : Nat} (f : Fin N → F)
    (n : Nat) (hn : n < N) :
    (∑ i : Fin N, if i.val < n + 1 then f i else 0) =
      (∑ i : Fin N, if i.val < n then f i else 0) + f ⟨n, hn⟩ := by
  classical
  conv_lhs =>
    arg 2
    ext i
    rw [show (if i.val < n + 1 then f i else 0) =
      (if i.val < n then f i else 0) +
        (if i = (⟨n, hn⟩ : Fin N) then f i else 0) by
          by_cases hlt : i.val < n
          · have hneq : i ≠ (⟨n, hn⟩ : Fin N) := by
              intro h
              have hv : i.val = n := by simpa using congrArg Fin.val h
              omega
            simp [hlt, Nat.lt_add_one_of_lt hlt, hneq]
          · by_cases heq : i.val = n
            · have hi : i = ⟨n, hn⟩ := Fin.ext heq
              simp [hi]
            · have hnot : ¬ i.val < n + 1 := by omega
              have hneq : i ≠ (⟨n, hn⟩ : Fin N) := Fin.ne_of_val_ne heq
              simp [hlt, hnot, hneq]]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

private theorem register42_registersVal_succ
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (register : Fin 128) (n : Nat) (hnext : n + 1 < p.traceLength) :
    HonestWitness.RegistersVal (F := F) p trace register ⟨n + 1, hnext⟩ =
      HonestWitness.RegistersVal p trace register ⟨n, by omega⟩ +
      HonestWitness.RdWa p trace register ⟨n, by omega⟩ *
        (HonestWitness.RdWriteValue p trace ⟨n, by omega⟩ -
          HonestWitness.RegistersVal p trace register ⟨n, by omega⟩) := by
  unfold HonestWitness.RegistersVal
  rw [← Fin.foldl_eq_foldl_finRange, Fin.foldl_succ_last]
  simp only [Fin.val_last, Fin.val_castSucc]
  rw [Fin.foldl_eq_foldl_finRange]

private theorem register42_real_write_delta
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (register : Fin 128) (t : Fin p.traceLength)
    (hb : t.val < trace.rows.size) :
    HonestWitness.RdWa p trace register t *
      (HonestWitness.RdWriteValue p trace t -
        ((JoltISA.sourceValue (register42_srcOfAddress register)
          (trace.rows[t.val]'hb).preState).toNat : F)) =
      HonestWitness.RdWa p trace register t * HonestWitness.RdInc p trace t := by
  let row := trace.rows[t.val]'hb
  let instr := program.expandedBytecode[row.rowIndex].expandedInstruction
  have hwa := register42_RdWa_real (F := F) p trace t hb register
  change HonestWitness.RdWa (F := F) p trace register t =
    match instr.destination? with
    | some dst => if register = HonestWitness.destinationRegisterAddress dst then 1 else 0
    | none => 0 at hwa
  have hinc : HonestWitness.RdInc (F := F) p trace t =
      HonestWitness.rdValue instr row.postState -
        HonestWitness.rdValue instr row.preState := by
    unfold HonestWitness.RdInc
    simp only [dif_pos hb]
    rfl
  have hwrite : HonestWitness.RdWriteValue (F := F) p trace t =
      HonestWitness.rdValue instr row.postState := by
    unfold HonestWitness.RdWriteValue
    simp only [dif_pos hb]
    rfl
  have hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true :=
    program.expandedBytecode[row.rowIndex].registerOperandsCanonical
  cases hd : instr.destination? with
  | none =>
      rw [hwa, hd]
      simp
  | some dst =>
      by_cases hselected : register = HonestWitness.destinationRegisterAddress dst
      · have hcanondst := register42_instruction_destination_canonical instr dst hcanon hd
        have hsrcdst := register42_srcOfDestinationAddress dst hcanondst
        simp only [hselected, hinc, hwrite]
        rw [register42_rdValue_eq_destination,
          register42_rdValue_eq_destination]
        simp only [hd]
        rw [hsrcdst]
      · simp [hwa, hd, hselected]

private theorem register42_trace_register_link
    {program : JoltProgram} (trace : JoltTrace program)
    (src : JoltISA.Src) (n : Nat)
    (hn : n < trace.rows.size) (hnext : n + 1 < trace.rows.size) :
    JoltISA.sourceValue src (trace.rows[n + 1]'hnext).preState =
      JoltISA.sourceValue src (trace.rows[n]'hn).postState := by
  have hlink := trace.linked n hn hnext
  change (trace.rows[n + 1]'hnext).preState =
    if program.expandedBytecode[(trace.rows[n]'hn).rowIndex].continues then
      (trace.rows[n]'hn).postState
    else program.prepareSource trace.sequenceLayout
      (trace.rows[n + 1]'hnext).rowIndex (trace.rows[n]'hn).postState at hlink
  rw [hlink]
  by_cases hc : program.expandedBytecode[(trace.rows[n]'hn).rowIndex].continues = true
  · change JoltISA.sourceValue src
      (if program.expandedBytecode[(trace.rows[n]'hn).rowIndex].continues = true then
        (trace.rows[n]'hn).postState else
        program.prepareSource trace.sequenceLayout
          (trace.rows[n + 1]'hnext).rowIndex (trace.rows[n]'hn).postState) = _
    simp only [hc, ↓reduceIte]
  · simp only [if_neg hc]
    exact register42_prepareSource_preserves_sourceValue program
      trace.sequenceLayout _ _ src

private theorem register42_registersVal_real_step
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (register : Fin 128) (n : Nat) (hb : n < trace.rows.size)
    (hnext : n + 1 < p.traceLength)
    (hpre : HonestWitness.RegistersVal (F := F) p trace register ⟨n, by omega⟩ =
      ((JoltISA.sourceValue (register42_srcOfAddress register)
        (trace.rows[n]'hb).preState).toNat : F)) :
    HonestWitness.RegistersVal p trace register ⟨n + 1, hnext⟩ =
      ((JoltISA.sourceValue (register42_srcOfAddress register)
        (trace.rows[n]'hb).postState).toNat : F) := by
  have hstep := register42_registersVal_succ (F := F) p trace register n hnext
  have hdelta := register42_real_write_delta (F := F) p trace register ⟨n, by omega⟩ hb
  have hrow := register42_row_step (F := F) p trace register ⟨n, by omega⟩ hb
  rw [hstep, hpre, hdelta]
  exact hrow.symm

theorem register42_registersVal_preState
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (traceFits : p.ProverPaddedFor trace.rows.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0)
    (register : Fin 128) (n : Nat) (hn : n < trace.rows.size) :
    HonestWitness.RegistersVal (F := F) p trace register
      ⟨n, Nat.lt_of_lt_of_le hn traceFits.traceFits⟩ =
    ((JoltISA.sourceValue (register42_srcOfAddress register)
      (trace.rows[n]'hn).preState).toNat : F) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hstart := trace.startsAtInitial hn
          change (trace.rows[0]'hn).preState =
            program.prepareSource trace.sequenceLayout
              (trace.rows[0]'hn).rowIndex program.initialState at hstart
          rw [hstart, register42_prepareSource_preserves_sourceValue,
            initialRegistersZero]
          simp [HonestWitness.RegistersVal]
      | succ m =>
          have hm : m < trace.rows.size := by omega
          have hmp := ih m (by omega) hm
          have hnext : m + 1 < p.traceLength :=
            Nat.lt_of_lt_of_le hn traceFits.traceFits
          have hstep := register42_registersVal_real_step (F := F)
            p trace register m hm hnext hmp
          have hlink := register42_trace_register_link trace
            (register42_srcOfAddress register) m hm hn
          calc
            HonestWitness.RegistersVal p trace register
                ⟨m + 1, Nat.lt_of_lt_of_le hn traceFits.traceFits⟩ =
                ((JoltISA.sourceValue (register42_srcOfAddress register)
                  (trace.rows[m]'hm).postState).toNat : F) := hstep
            _ = ((JoltISA.sourceValue (register42_srcOfAddress register)
                  (trace.rows[m + 1]'hn).preState).toNat : F) := by rw [hlink]

private theorem register42_registersVal_step
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (traceFits : p.ProverPaddedFor trace.rows.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0)
    (register : Fin 128) (n : Nat) (hnext : n + 1 < p.traceLength) :
    HonestWitness.RegistersVal (F := F) p trace register ⟨n + 1, hnext⟩ =
      HonestWitness.RegistersVal p trace register ⟨n, by omega⟩ +
        HonestWitness.RdWa p trace register ⟨n, by omega⟩ *
          HonestWitness.RdInc p trace ⟨n, by omega⟩ := by
  have hstep := register42_registersVal_succ (F := F) p trace register n hnext
  by_cases hb : n < trace.rows.size
  · have hpre := register42_registersVal_preState (F := F) p trace traceFits
      initialRegistersZero register n hb
    have hdelta := register42_real_write_delta (F := F) p trace register
      ⟨n, by omega⟩ hb
    rw [hstep, hpre, hdelta]
  · rw [hstep]
    have hwa : HonestWitness.RdWa (F := F) p trace register ⟨n, by omega⟩ = 0 := by
      unfold HonestWitness.RdWa
      simp [hb]
    rw [hwa]
    simp

theorem honestRegistersVal_eq_prefixRdInc
    {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (traceFits : p.ProverPaddedFor trace.rows.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0)
    (register : Fin 128) (t : Fin p.traceLength) :
    HonestWitness.RegistersVal (F := F) p trace register t =
      ∑ cycle : Fin p.traceLength,
        if cycle.val < t.val then
          HonestWitness.RdWa p trace register cycle * HonestWitness.RdInc p trace cycle
        else 0 := by
  have hmain : ∀ n : Nat, (hn : n < p.traceLength) →
      HonestWitness.RegistersVal (F := F) p trace register ⟨n, hn⟩ =
        ∑ cycle : Fin p.traceLength,
          if cycle.val < n then
            HonestWitness.RdWa p trace register cycle * HonestWitness.RdInc p trace cycle
          else 0 := by
    intro n
    induction n with
    | zero =>
        intro hn
        simp [HonestWitness.RegistersVal]
    | succ m ih =>
        intro hn
        have hm : m < p.traceLength := by omega
        have hstep := register42_registersVal_step (F := F) p trace traceFits
          initialRegistersZero register m hn
        have hsum := register42_prefix_sum_succ
          (fun cycle : Fin p.traceLength =>
            HonestWitness.RdWa (F := F) p trace register cycle *
              HonestWitness.RdInc p trace cycle) m hm
        rw [hstep, ih hm, hsum]
  exact hmain t.val t.isLt

end JoltConstraints
