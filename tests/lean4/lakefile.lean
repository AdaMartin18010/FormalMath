import Lake
open Lake DSL

package formalmathTests {
  -- 包配置
  keywords := #["math", "formalization", "testing"]
  description := "FormalMath Lean4 测试套件"
  homepage := "https://github.com/formalmath/formalmath"
  license := "MIT"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib FormalMathTests {
  -- 库配置
  roots := #[`FormalMathTests]
  globs := #[.submodules `FormalMathTests]
}

-- 测试目标
lean_lib Test {
  roots := #[`Test]
  globs := #[.submodules `Test]
}

-- 测试运行器配置
target test : Unit := do
  let exitCode ← IO.Process.run {
    cmd := "lean",
    args := #["--run", "Test/Main.lean"]
  }
  if exitCode == 0 then
    return .nil
  else
    throw <| IO.userError s!"Tests failed with exit code {exitCode}"
