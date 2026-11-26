import Lean
open Lean in
def fails : CoreM Unit := throwError "{"\""}"
theorem bad : False := by admit
-- "
