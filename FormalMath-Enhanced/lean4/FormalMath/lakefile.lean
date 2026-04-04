import Lake
open Lake DSL

package FormalMath where
  -- 包描述
  description := "FormalMath - Lean4形式化数学库"
  -- 许可证
  license := "MIT"

@[default_target]
lean_lib FormalMath where
  -- 库配置
  roots := #[`FormalMath]
  globs := #[.submodules `FormalMath]
  -- 构建设置
  moreLeanArgs := #[]
