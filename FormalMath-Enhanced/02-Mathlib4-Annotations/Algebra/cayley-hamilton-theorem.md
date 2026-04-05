---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Cayley-Hamilton定理 (Cayley-Hamilton Theorem)
---
# Cayley-Hamilton定理 (Cayley-Hamilton Theorem)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace CayleyHamilton

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n R}

/-- Cayley-Hamilton定理 -/
theorem cayley_hamilton :
    A.charpoly.eval A = 0 := by
  -- 利用伴随矩阵
  sorry

/-- 矩阵满足其特征多项式 -/
theorem matrix_annihilates_charpoly :
    aeval A A.charpoly = 0 := by
  -- 多项式求值的零化
  sorry

end CayleyHamilton
```

## 数学背景

Cayley-Hamilton定理由Arthur Cayley（1858年）和William Rowan Hamilton（此前对四元数）证明，是线性代数的基本结果。它表明每个方阵满足其自身的特征多项式。

## 应用

- 矩阵幂的计算
- 矩阵指数
- 控制理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
