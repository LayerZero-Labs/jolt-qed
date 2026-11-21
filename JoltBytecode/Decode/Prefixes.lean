import JoltBytecode.Step.Instructions

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions

namespace Decode

private theorem decodeReg (r : BitVec 5) :
    encdec_reg_backwards r = pure (.Regidx r) := by
  simp [encdec_reg_backwards, Functions.base_E_enabled, Functions.not,
    Sail.BitVec.extractLsb, Functions.regidx_bit_width, BitVec.extractLsb]

private theorem prefetchChecked (r : BitVec 5)
    (h : encdec_cbop_zicbop_backwards_matches r = true) :
    ∃ v, encdec_cbop_zicbop_backwards r = pure v := by
  unfold encdec_cbop_zicbop_backwards_matches at h
  split at h <;> simp_all [encdec_cbop_zicbop_backwards]

private theorem ntlChecked (r : BitVec 5)
    (h : encdec_ntl_backwards_matches r = true) :
    ∃ v, encdec_ntl_backwards r = pure v := by
  unfold encdec_ntl_backwards_matches at h
  split at h <;> simp_all [encdec_ntl_backwards]

private theorem disabledGuard {α β : Type} (g b : Bool) (m : SailM α)
    (hm : g = true → ∃ v, m = pure v) (k : SailM β) :
    (if g && b then m >>= fun _ => k else k) = k := by
  cases hg : g with
  | false => rfl
  | true =>
    obtain ⟨v, hv⟩ := hm hg
    rw [hv]
    cases b <;> rfl

/-- The optional prefetch candidate at the start of Sail's `encdec_backwards`.
For example, an ORI with rd=x0 can share its encoding, but Zicbop is disabled. -/
abbrev prefetchPrefix (arg_ : BitVec 32) (k : SailM instruction) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__658 := head_exp_
    if (((let mapping1_ : (BitVec 5) := (Sail.BitVec.extractLsb v__658 19 15)
         let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__658 24 20)
         ((encdec_cbop_zicbop_backwards_matches mapping0_) && (encdec_reg_backwards_matches
             mapping1_))) && ((Sail.BitVec.extractLsb v__658 14 0) == (0b110000000010011#15 : (BitVec 15)))) : Bool)
    then
      (do
        let offset11_5 : (BitVec 7) := (Sail.BitVec.extractLsb v__658 31 25)
        let offset11_5 : (BitVec 7) := (Sail.BitVec.extractLsb v__658 31 25)
        let mapping1_ : (BitVec 5) := (Sail.BitVec.extractLsb v__658 19 15)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__658 24 20)
        match ((← (encdec_cbop_zicbop_backwards mapping0_)), (← (encdec_reg_backwards mapping1_))) with
        | (cbop, rs1) =>
          (do
            if ((← (currentlyEnabled .Ext_Zicbop)) : Bool)
            then (pure (some (.ZICBOP (cbop, rs1, ((offset11_5 : (BitVec 7)) +++ 0b00000#5)))))
            else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none => k

/-- The disabled prefetch candidate always falls through, including on ORI hints. -/
theorem prefetchPrefix_none (w : BitVec 32) (k : SailM instruction) : prefetchPrefix w k = k := by
  have he : currentlyEnabled .Ext_Zicbop = pure false := by
    unfold currentlyEnabled
    simp only [hartSupports, pure]
  simp only [prefetchPrefix, decodeReg, he, encdec_reg_backwards_matches,
    Functions.base_E_enabled, Functions.not, Bool.not_false, Bool.true_or,
    Bool.and_true, ↓reduceIte, bind_assoc, pure_bind]
  change (if encdec_cbop_zicbop_backwards_matches (Sail.BitVec.extractLsb w 24 20) &&
      (Sail.BitVec.extractLsb w 14 0 == 0b110000000010011#15) then
      encdec_cbop_zicbop_backwards (Sail.BitVec.extractLsb w 24 20) >>=
        fun _ => k else k) = k
  exact disabledGuard _ _ _ (prefetchChecked _) k

/-- The optional non-temporal hint candidate at the start of Sail's decoder.
For example, ADD x0,x0,x2 is also an NTL encoding when Zihintntl is enabled. -/
abbrev ntlPrefix (arg_ : BitVec 32) (k : SailM instruction) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__652 := head_exp_
    if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__652 24 20)
         (encdec_ntl_backwards_matches mapping2_)) && (((Sail.BitVec.extractLsb v__652 31 25) == (0b0000000#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
               v__652 19 0) == (0x00033#20 : (BitVec 20))))) : Bool)
    then
      (do
        let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__652 24 20)
        let op ← do (encdec_ntl_backwards mapping2_)
        if ((← (currentlyEnabled .Ext_Zihintntl)) : Bool)
        then (pure (some (.NTL op)))
        else (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | none => k

/-- The disabled non-temporal hint candidate always falls through to the base decoder. -/
theorem ntlPrefix_none (w : BitVec 32) (k : SailM instruction) : ntlPrefix w k = k := by
  have he : currentlyEnabled .Ext_Zihintntl = pure false := by
    unfold currentlyEnabled
    simp only [hartSupports, pure]
  simp only [ntlPrefix, he, bind_assoc, pure_bind]
  change (if encdec_ntl_backwards_matches (Sail.BitVec.extractLsb w 24 20) &&
      ((Sail.BitVec.extractLsb w 31 25 == 0#7) && (Sail.BitVec.extractLsb w 19 0 == 0x33#20)) then
      encdec_ntl_backwards (Sail.BitVec.extractLsb w 24 20) >>= fun _ => k
      else k) = k
  exact disabledGuard _ _ _ (ntlChecked _) k

/-- Sail's first compressed candidate is a disabled non-temporal hint; e.g. C.ADD x0,x2. -/
abbrev compressedNtlPrefix (arg_ : BitVec 16) (k : SailM instruction) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__1536 := head_exp_
    if (((let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__1536 6 2)
         (encdec_ntl_backwards_matches mapping0_)) && (((Sail.BitVec.extractLsb v__1536 15 7) == (0b100100000#9 : (BitVec 9))) && ((Sail.BitVec.extractLsb
               v__1536 1 0) == (0b10#2 : (BitVec 2))))) : Bool)
    then
      (do
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__1536 6 2)
        let op ← do (encdec_ntl_backwards mapping0_)
        if ((←((currentlyEnabled .Ext_Zihintntl) <&&> (do
             (currentlyEnabled .Ext_Zca)))) : Bool)
        then (pure (some (.C_NTL op)))
        else (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | none => k

/-- Disabled C.NTL candidates fall through, including C.ADD hints with rd=x0. -/
theorem compressedNtlPrefix_none (h : BitVec 16) (k : SailM instruction) :
    compressedNtlPrefix h k = k := by
  have he : currentlyEnabled .Ext_Zihintntl = pure false := by
    unfold currentlyEnabled
    simp only [hartSupports, pure]
  simp only [compressedNtlPrefix, he, andM, pure_bind, Bool.false_eq_true,
    ↓reduceIte, bind_assoc]
  change (if encdec_ntl_backwards_matches (Sail.BitVec.extractLsb h 6 2) &&
      ((Sail.BitVec.extractLsb h 15 7 == 0b100100000#9) && (Sail.BitVec.extractLsb h 1 0 == 2#2))
      then encdec_ntl_backwards (Sail.BitVec.extractLsb h 6 2) >>= fun _ => k else k) = k
  exact disabledGuard _ _ _ (ntlChecked _) k

end Decode
