/-!
# Fixture for `JoltConstraints/Audit/Test/Fingerprints.lean`: a private name

This module and `PrivateB.lean` each declare a private `JoltConstraints.Audit.Test.allowed`.
The two declarations have the same name without their private prefix, so a table keyed by that
name would keep only one of them.
-/

namespace JoltConstraints.Audit.Test

/-- The private `allowed` of this module; `PrivateB.lean` has another one. -/
private def allowed : Nat := 1

/-- A value that depends on this module's private `allowed`. -/
def usesA : Nat := allowed

/-- A root whose statement depends on `usesA`, and through it on this module's `allowed`. -/
theorem rootA : usesA = usesA := rfl

end JoltConstraints.Audit.Test
