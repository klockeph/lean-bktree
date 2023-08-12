import Lake
open Lake DSL

package «BkTree» {
  -- add package configuration options here
}

@[default_target]
lean_lib «BkTree» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"