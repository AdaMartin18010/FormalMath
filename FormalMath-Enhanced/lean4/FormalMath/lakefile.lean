import Lake
open Lake DSL

package FormalMath where
  -- Mathlib4 v4.19.0
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib FormalMath where
  -- Library configuration
  roots := #[`FormalMath]
  globs := #[.submodules `FormalMath]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
