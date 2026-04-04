import Lake
open Lake DSL

package FormalMath where
  description := "FormalMath - Lean4形式化数学库"
  license := "MIT"

@[default_target]
lean_lib FormalMath where
  roots := #[`FormalMath]
  globs := #[.submodules `FormalMath]
  moreLeanArgs := #[]
