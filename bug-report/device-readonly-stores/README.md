+++
status = "unknown"
reproduced_at = "unknown"
fixed_by = ""
upstream = "a16z/jolt#2041"
registry = []
note = "Never reproduced; see issue.md. At ff6fc6568 the model has no such gap: JoltInstance.soundness is proved with only JoltField. Whether the candidate was a real gap at 43cc04333 is not known."
+++

# Input and advice stores: a candidate soundness gap

`issue.md` is the text of a16z/jolt#2041, filed from a reading of Jolt at `43cc04333` (with links to `00508a09`).
It asks which constraint excludes, from a prover's witness, a store to an input or advice word that Jolt's tracer rejects.
Nobody built a witness or a proof for it.

At `ff6fc6568` Jolt's tracer admits a store to an input or advice word only when it keeps every byte's value (Jolt at ff6fc6568: `tracer/src/emulator/mmu.rs` (`device_fault`), from a16z/jolt#2418), and the constraints include the protected-word mask.
`JoltInstance.soundness` is proved for the model at that pin with no premise beyond `JoltField`, so the model has no such gap.
a16z/jolt#2041 is still open.
