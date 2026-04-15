import Lake
open Lake DSL

package FormalMath where
  description := "FormalMath - Lean4形式化数学库"
  license := "MIT"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib FormalMath where
  roots := #[`FormalMath]
  globs := #[.submodules `FormalMath]
  moreLeanArgs := #[]

lean_lib RamseyTheorem where
  roots := #[`RamseyTheorem]
  moreLeanArgs := #[]

@[default_target]
lean_lib FormalMathVerified where
  roots := #[`FormalMath]
  globs := #[.one `FormalMath.ChineseRemainderTheorem,
              .one `FormalMath.InfinitudeOfPrimes,
              .one `FormalMath.PigeonholePrinciple]
  moreLeanArgs := #[]
