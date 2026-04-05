/-
测试用的Lean4代码示例
-/

namespace FormalMath.Test

/-- 测试命题：真命题 -/
def testTrue : Prop := True

/-- 测试命题：假命题 -/
def testFalse : Prop := False

/-- 测试定理：真命题总是真 -/
theorem true_is_true : testTrue := by
  trivial

/-- 测试定义：恒等函数 -/
def id {α : Type} (x : α) : α := x

/-- 测试引理：恒等函数返回原值 -/
lemma id_eq_self (x : Nat) : id x = x := by
  rfl

end FormalMath.Test
