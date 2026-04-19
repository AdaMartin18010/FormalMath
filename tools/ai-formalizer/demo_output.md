# 示例文档

这是一个测试文件。

```lean4
import Mathlib

theorem f_thm {f : ℝ → ℝ} (hf : Continuous f) : ∀ x, f x = 0 → x > 0 := by
  sorry
```


一些正文内容。

```lean4
import Mathlib

theorem G_thm {G : Type*} [Group G] [Fintype G] {H : Subgroup G} : Nat.card H ∣ Nat.card G := by
  sorry
```


结束。
