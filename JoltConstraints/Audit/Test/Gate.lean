/-!
# Fixture for `JoltConstraints/Audit/Test/Fingerprints.lean`: an owner with several members

The structure `Gate` owns the declarations Lean generates for it: the constructor `Gate.mk`
and the projections `Gate.open_` and `Gate.width`. The statement of `rootFull` reaches the
projection `Gate.width`; the statement of `rootPartial` reaches only the structure and its
constructor. A fingerprint of `Gate` computed from `rootPartial` alone misses `Gate.width`.
-/

namespace JoltConstraints.Audit.Test

/-- A structure with two fields, for example `{ open_ := true, width := 4 }`. -/
structure Gate where
  /-- Whether the gate is open. -/
  open_ : Bool
  /-- The width of the gate. -/
  width : Nat

/-- A root whose statement uses the projection `Gate.width`. -/
theorem rootFull (g : Gate) : g.width = g.width := rfl

/-- A root whose statement uses the structure `Gate` but none of its projections. -/
theorem rootPartial (g : Gate) : g = g := rfl

end JoltConstraints.Audit.Test
