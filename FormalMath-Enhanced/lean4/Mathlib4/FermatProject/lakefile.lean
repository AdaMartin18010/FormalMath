import Lake
open Lake DSL

package «FermatProject» {
  -- add package configuration options here
}

lean_lib «CompletenessTheorem» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fermatproject» {
  root := `CompletenessTheorem
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
