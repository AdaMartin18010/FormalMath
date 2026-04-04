import Lake
open Lake DSL

package FormalMath where
  -- Mathlib4 v4.20.0 (Aligned with Mathlib4 latest version)
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

@[default_target]
lean_lib FormalMath where
  -- Library configuration
  roots := #[`FormalMath]
  globs := #[.submodules `FormalMath]
  -- Build settings for Mathlib4 compatibility
  moreLeanArgs := #["-Dpp.proofs.withType=false"]

-- Optional: Declaration checking tool
require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

-- Documentation generation (dev mode only)
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
