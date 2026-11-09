/-
What the completeness theorem assumes about the instance. Nothing is assumed
about the trace: what Jolt says it proves is part of `JoltInstance.InLanguage`.
-/
import JoltConstraints.honest_trace

set_option autoImplicit false

-- What the completeness theorem assumes about the instance. a16z has confirmed it.
structure JoltInstance.CompletenessAssumptions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- The program's memory image loads at least one byte.
  -- Confirmed by a16z by phone on 2026-10-08: Jolt can assume a program is never
  -- empty. Jolt's prover does not reject an empty ELF; only Jolt's verifier does
  -- (bug-report/verifier-ram-minimum).
  imageNonempty : joltInstance.program.ImageNonempty
