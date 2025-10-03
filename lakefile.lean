import Lake
open Lake DSL

abbrev mathlibLeanOptions : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩
  ]

package «my_project» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0-rc1"

@[default_target]
lean_lib StacksProject where
  leanOptions := mathlibLeanOptions
