import JoltConstraints.witness_helpers.ram_state

set_option autoImplicit false

namespace JoltConstraints

/-- Data used by the constraint equations, bound to one instance and its private
inputs. This contains no execution rows or honesty certificate.

`io` is the verifier's public I/O. `initialRam` also includes private advice; it
is not claimed to be public. Its encoding must come from `initial_state` for the
explicit private inputs, rather than an arbitrary prover-supplied memory image. -/
structure ConstraintContext (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (params : WitnessParams) where
  bytecode : Array JoltInstructionRow
  initialRam : Nat → BitVec 64
  io : JoltDevice
  entry : Fin (2 ^ params.logBytecodeK)
  expands : expand_program joltInstance.program = some bytecode
  initialized : ∃ state, joltInstance.initial_state privateInputs = some state ∧
    initialRam = TraceWitness.initialRamWordFromState state
  publicIo : joltInstance.public_io = some io
  entryIsRust : ∃ slots, preprocess bytecode = some slots ∧
    get_first_pc slots joltInstance.program.entry_address = some entry.val

namespace ConstraintContext

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (a b : ConstraintContext joltInstance privateInputs params)

-- Choosing a different context cannot change the program or its initial memory.
theorem bytecode_unique : a.bytecode = b.bytecode :=
  Option.some.inj (a.expands.symm.trans b.expands)

theorem initialRam_unique : a.initialRam = b.initialRam := by
  obtain ⟨sa, ha, ra⟩ := a.initialized
  obtain ⟨sb, hb, rb⟩ := b.initialized
  have same := Option.some.inj (ha.symm.trans hb)
  rw [ra, rb, same]

theorem publicIo_unique : a.io = b.io :=
  Option.some.inj (a.publicIo.symm.trans b.publicIo)

theorem entry_unique : a.entry = b.entry := by
  obtain ⟨sa, ha, ea⟩ := a.entryIsRust
  obtain ⟨sb, hb, eb⟩ := b.entryIsRust
  rw [bytecode_unique a b] at ha
  have same := Option.some.inj (ha.symm.trans hb)
  rw [same] at ea
  exact Fin.ext (Option.some.inj (ea.symm.trans eb))

end ConstraintContext
end JoltConstraints
