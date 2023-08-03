import Lake
open Lake DSL

package «sol-2-9» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «Sol29» {
  -- add library configuration options here
}
