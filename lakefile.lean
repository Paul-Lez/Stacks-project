import Lake
open Lake DSL

package «my_project» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0-rc1"

@[default_target]
lean_lib «StacksProject» {
  -- add any library configuration options here
}
