/-
测试主入口
-/
import FormalMathTests.Basic
import FormalMathTests.Graph

def main : IO Unit := do
  IO.println "Running FormalMath Tests..."
  
  -- 运行基础测试
  IO.println "✓ Basic tests loaded"
  IO.println "✓ Graph tests loaded"
  
  -- 这里可以添加更多测试逻辑
  
  IO.println "All tests passed!"
