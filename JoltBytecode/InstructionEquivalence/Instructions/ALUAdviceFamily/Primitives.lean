import JoltBytecode.JoltISA.Values
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

/-!
# ALU advice-family shared imports

The instruction behavior for the advice-verified DIV/REM family now lives in
`JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas`.  The pure adjusted-divisor
values live in `JoltBytecode.JoltISA.Values`.

This file remains as a narrow compatibility import for the `ALUAdviceFamily`
directory while the proofs are being moved over to direct `JoltISA.execInstr`
statements.  It must not define a parallel `vreg_*` instruction API.
-/
