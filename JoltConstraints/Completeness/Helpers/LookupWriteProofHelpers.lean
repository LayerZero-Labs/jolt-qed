import JoltConstraints.Completeness.Helpers.JumpReturnProofHelpers

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open Sail PreSail LeanRV64D.Functions

private theorem readReg_get (reg : Register) (s : SailState)
    (v : RegisterType reg) (s' : SailState)
    (h : (Sail.readReg reg : SailM (RegisterType reg)) s = .ok v s') :
    s.regs.get? reg = some v := by
  unfold Sail.readReg PreSail.readReg at h
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get,
    pure, EStateM.pure] at h
  cases hg : s.regs.get? reg with
  | none => simp only [hg] at h; change EStateM.Result.error Error.Unreachable s = .ok v s' at h; cases h
  | some value => simp [hg] at h; cases h; rfl

theorem lookup_readSrc_value (src : JoltISA.Src) (state state' : SailJoltState)
    (value : BitVec 64)
    (hread : JoltISA.readSrc src state = .ok value state') :
    state' = state ∧ value = JoltISA.sourceValue src state := by
  cases src with
  | vreg vr =>
      simp only [JoltISA.readSrc_vreg, readVReg_run] at hread
      cases hread
      exact ⟨rfl, rfl⟩
  | xreg rd =>
      change liftSail (rX_bits rd) state = .ok value state' at hread
      unfold liftSail at hread
      cases h : rX_bits rd state.sail with
      | error e s =>
          rw [h] at hread
          cases hread
      | ok v s =>
          rw [h] at hread
          have hs : s = state.sail := rX_bits_pure rd state.sail v s h
          subst s
          cases hread
          constructor
          · rfl
          · reg_cases rd
            all_goals
              simp_all only [JoltISA.sourceValue, rX_bits, rX,
                regval_from_reg, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast,
                Int.toNat_natCast, zero_reg, zeros]
              first
              | simp only [bind, EStateM.bind, pure, EStateM.pure] at h
                cases h
                rfl
              | simp only [bind, EStateM.bind, pure, EStateM.pure] at h
                generalize hread : Sail.readReg _ state.sail = result at h
                cases result with
                | error e s => cases h
                | ok v s =>
                    have hg := readReg_get _ _ _ _ hread
                    simp only [hg, Option.getD_some]
                    cases h
                    rfl

/-- Successful operand reads can be replaced by the pure witness calculation. -/
theorem lookup_read_bind {α : Type} (src : JoltISA.Src)
    (f : BitVec 64 → JoltMonad α) (pre post : SailJoltState) (result : α)
    (hexec : (JoltISA.readSrc src >>= f) pre = .ok result post) :
    f (JoltISA.sourceValue src pre) pre = .ok result post := by
  cases hr : JoltISA.readSrc src pre with
  | error e s => simp only [bind, EStateM.bind, hr] at hexec; cases hexec
  | ok v s =>
    obtain ⟨rfl, rfl⟩ := lookup_readSrc_value src pre s v hr
    simpa only [bind, EStateM.bind, hr] using hexec

/-- A destination write followed by retirement captures the value written. -/
theorem lookup_write_retire (dst : JoltISA.Dst)
    (value : BitVec 64) (pre post : SailJoltState) (hw : dst.NotX0)
    (hexec : (do JoltISA.writeDst dst value; pure RETIRE_SUCCESS) pre =
      .ok (.Retire_Success ()) post) :
    TraceWitness.capturedDestinationValue dst post = value := by
  cases hr : JoltISA.writeDst dst value pre with
  | error e s => simp only [bind, EStateM.bind, hr] at hexec; cases hexec
  | ok u s =>
    cases u
    simp only [bind, EStateM.bind, hr, pure, EStateM.pure,
      EStateM.Result.ok.injEq, true_and] at hexec
    cases hexec.2
    exact jump_write_capture dst value pre post hw hr

/-- Valid rows either have a writable destination or are the canonical no-op. -/
theorem lookup_destination_writable (bc : JoltInstructionRow) (valid : bc.Valid)
    (hnoop : bc.instruction ≠ JoltISA.Instr.canonicalNoOp)
    (dst : JoltISA.Dst) (hdst : bc.instruction.destination? = some dst) :
    dst.NotX0 := by
  cases dst with
  | vreg vr => exact True.intro
  | xreg rd =>
    cases hz : JoltISA.isX0 rd with
    | false => exact hz
    | true => exact False.elim (hnoop (valid.x0DestinationIsNoOp rd hdst hz))

/-- The instruction-level connection between execution and lookup capture.
The PC hypothesis is supplied by the trace boundary invariant. -/
theorem lookup_row_write {F : Type} [Field F] {bytecode : Array JoltInstructionRow}
    (row : HonestTraceRow bytecode) (valid : bytecode[row.rowIndex].Valid)
    (hpc : row.preState.sail.regs.get? Register.PC =
      some bytecode[row.rowIndex].address)
    (hflag : JoltMetadata.circuitFlag bytecode[row.rowIndex]
      .WriteLookupOutputToRD = true) :
    TraceWitness.rdValue (F := F)
      bytecode[row.rowIndex].instruction row.postState =
      ((TraceWitness.rowLookupOutput row.toTraceRow).toNat : F) := by
  let bc := bytecode[row.rowIndex]
  change JoltMetadata.circuitFlag bc .WriteLookupOutputToRD = true at hflag
  change TraceWitness.rdValue (F := F) bc.instruction row.postState = _
  by_cases hnoop : bc.instruction = JoltISA.Instr.canonicalNoOp
  · change TraceWitness.rdValue (F := F) bc.instruction row.postState = _
    simp only [TraceWitness.rowLookupOutput, show
      bytecode[row.rowIndex.val].instruction =
        JoltISA.Instr.canonicalNoOp from hnoop, hnoop,
      JoltISA.Instr.canonicalNoOp, TraceWitness.rdValue,
      TraceWitness.capturedDestinationValue, TraceWitness.capturedDestination,
      JoltISA.sourceValue, BitVec.toNat_ofNat, Nat.zero_mod, JoltISA.addWide,
      Nat.zero_add, BitVec.toNat_zero]
    rfl
  · have hw := lookup_destination_writable bc valid hnoop
    have hexec : ∃ advice : bc.instruction.RuntimeAdvice,
        JoltISA.execInstr (bc.instruction.withRuntimeAdvice advice)
          row.preState = .ok (.Retire_Success ()) row.postState :=
      ⟨row.runtimeAdvice, row.executes⟩
    have hreadpc : liftSail (get_arch_pc ()) row.preState =
        .ok bc.address row.preState := by
      change liftSail (Sail.readReg Register.PC) row.preState = _
      unfold liftSail
      rw [readReg_eq_of_get? Register.PC row.preState.sail bc.address hpc]
    cases hi : bc.instruction with
    | ADDI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | ADDIW dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | ANDI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | ORI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | XORI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | SLTI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | SLTIU dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | LUI dst imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hexec)
    | AUIPC dst imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      simp only [bind, EStateM.bind, hreadpc] at hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hexec)
    | ADDW dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | ADD dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | SUB dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | SUBW dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | MUL dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | MULW dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | MULHU dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | ANDN dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualMULI dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualMULIW dst src imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualPow2 dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualPow2W dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualPow2I dst imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hexec)
    | VirtualPow2IW dst imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hexec)
    | VirtualShiftRightBitmask dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualShiftRightBitmaskI dst imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hexec)
    | VirtualShiftRightBitmaskW dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualSRLI dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualSRAI dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualSRLIW dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualSRAIW dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualSRL dst value bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind bitmask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualSRA dst value bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind bitmask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualSRLW dst value bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind bitmask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualSRAW dst value bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind bitmask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualROTRI dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualROTRIW dst src bitmask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualRev8W dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualXORROT32 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROT24 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROT16 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROT63 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTL1 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW16 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW12 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW8 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW7 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW22 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW19 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualXORROTW6 dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | OR dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | XOR dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | AND dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | SLT dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | SLTU dst lhs rhs =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind lhs _ _ _ _ hexec
      have hread2 := lookup_read_bind rhs _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualAlignAddr dst base imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind base _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualWindowMaskB dst base imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind base _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualWindowMaskH dst base imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind base _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualWindowMaskW dst base imm =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind base _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualPext dst value mask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind mask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualPextSigned dst value mask =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind mask _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualShiftDataB dst value address =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind address _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualShiftDataH dst value address =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind address _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualShiftDataW dst value address =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind value _ _ _ _ hexec
      have hread2 := lookup_read_bind address _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | VirtualSignExtendWord dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualZeroExtendWord dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualMovsign dst src unused =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind src _ _ _ _ hexec
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread)
    | VirtualAdvice =>
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
    | VirtualAdviceLoad =>
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
    | VirtualAdviceLen =>
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
    | VirtualNegateIf dst signSource value =>
      simp only [hi, JoltISA.Instr.destination?, Option.some.injEq] at hw
      rw [hi] at hexec
      simp only [JoltISA.Instr.withRuntimeAdvice, JoltISA.execInstr] at hexec
      simp only [TraceWitness.rowLookupOutput, show
        bytecode[row.rowIndex.val].instruction = _ from hi,
        hi, TraceWitness.rdValue]
      obtain ⟨advice, hexec⟩ := hexec
      have hread := lookup_read_bind signSource _ _ _ _ hexec
      have hread2 := lookup_read_bind value _ _ _ _ hread
      exact congrArg (fun v : BitVec 64 => (v.toNat : F))
        (lookup_write_retire dst _ _ _ (hw dst rfl) hread2)
    | _ =>
      simp only [JoltMetadata.circuitFlag, JoltMetadata.opcodeFlag, hi,
        Bool.false_eq_true] at hflag
