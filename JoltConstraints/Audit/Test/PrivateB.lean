/-!
# Fixture for `JoltConstraints/Audit/Test/Fingerprints.lean`: a second private name

See `PrivateA.lean`.
-/

namespace JoltConstraints.Audit.Test

/-- The private `allowed` of this module; `PrivateA.lean` has another one. -/
private def allowed : Nat := 2

/-- A value that depends on this module's private `allowed`. -/
def usesB : Nat := allowed

/-- A root whose statement depends on `usesB`, and through it on this module's `allowed`. -/
theorem rootB : usesB = usesB := rfl

end JoltConstraints.Audit.Test
