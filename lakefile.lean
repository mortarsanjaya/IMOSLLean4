import Lake
open Lake DSL

package «IMOSLLean4» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @"v4.28.0"

@[default_target]
lean_lib «IMOSLLean4» where
  -- add any library configuration options here
