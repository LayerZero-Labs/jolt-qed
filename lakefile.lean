import Lake
open Lake DSL

package «JoltBytecode» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]
  moreLeanArgs := #["--tstack=400000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "9d092b118b6f9f777ba67c7a2d2c2bcdd1b52395"

require Sail from git
  "https://github.com/rems-project/lean-sail" @ "v3"

@[default_target]
lean_lib «JoltBytecode» where
  srcDir := "."
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib «LeanRV64D» where
  srcDir := "."
  weakLeanOptions := #[
    ⟨`linter.style.nameCheck, false⟩
  ]
  moreLeancArgs := #["-fbracket-depth=500"]
