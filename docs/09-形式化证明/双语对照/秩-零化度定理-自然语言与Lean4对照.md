---
title: "秩-零化度定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
---

## 定理陈述

**自然语言**：设 \(T: V \to W\) 是域 \(\mathbb{K}\) 上有限维向量空间之间的线性映射，则
\[
\dim(\operatorname{im}(T)) + \dim(\ker(T)) = \dim(V).
\]
其中 \(\dim(\operatorname{im}(T))\) 称为 \(T\) 的**秩**（rank），\(\dim(\ker(T))\) 称为 \(T\) 的**零化度**（nullity）。

**Lean4**：

```lean
import Mathlib.Algebra.Module.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional

universe u v w
namespace RankNullityTheorem
open FiniteDimensional LinearMap

variable {𝕜 : Type u} [Field 𝕜] {V : Type v} {W : Type w}
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
  [FiniteDimensional 𝕜 V]

-- 秩-零化度定理
theorem rank_nullity (T : V →ₗ[𝕜] W) :
    finrank 𝕜 (range T) + finrank 𝕜 (ker T) = finrank 𝕜 V := by
  exact finrank_range_add_finrank_ker T
end RankNullityTheorem
```

## 证明思路

**自然语言**：秩-零化度定理是线性代数中最基本的维数公式之一，其核心证明思路如下。

1. 取 \(\ker(T)\) 的一组基 \(\{v_1, \dots, v_k\}\)，并将其扩充为 \(V\) 的一组基 \(\{v_1, \dots, v_k, u_1, \dots, u_r\}\)。
2. 证明 \(\{T(u_1), \dots, T(u_r)\}\) 构成 \(\operatorname{im}(T)\) 的一组基：
   - **生成性**：对任意 \(w \in \operatorname{im}(T)\)，存在 \(v \in V\) 使得 \(w = T(v)\)。将 \(v\) 用基展开，含 \(v_i\) 的项被 \(T\) 映为 \(0\)，因此 \(w\) 是 \(T(u_j)\) 的线性组合。
   - **线性无关性**：设 \(\sum_{j=1}^r c_j T(u_j) = 0\)，则 \(T(\sum c_j u_j) = 0\)，即 \(\sum c_j u_j \in \ker(T)\)。因此它可以由 \(\ker(T)\) 的基 \(\{v_i\}\) 表示。但 \(\{v_1, \dots, v_k, u_1, \dots, u_r\}\) 是线性无关的，故所有系数 \(c_j\) 必须为 \(0\)。
3. 于是 \(\dim(\operatorname{im}(T)) = r\)，\(\dim(\ker(T)) = k\)，而 \(\dim(V) = k + r\)，即得定理。

**Lean4**：Mathlib4 的 `LinearMap.finrank_range_add_finrank_ker` 直接给出了秩-零化度定理。在 Lean 中，`range T` 和 `ker T` 都是子模（`Submodule`），`finrank` 计算子模作为向量空间的维数。

```lean
-- 核与像的定义
example (T : V →ₗ[𝕜] W) : Submodule 𝕜 V := ker T
example (T : V →ₗ[𝕜] W) : Submodule 𝕜 W := range T
```

## 关键 tactic/概念 教学

- `V →ₗ[𝕜] W`：域 \(\mathbb{K}\) 上从 \(V\) 到 \(W\) 的线性映射类型。
- `ker T` / `range T`：线性映射的核与像，它们都是子模。
- `finrank 𝕜 V`：有限维向量空间 \(V\) 在域 \(\mathbb{K}\) 上的维数。
- `finrank_range_add_finrank_ker`：秩-零化度定理在 Mathlib4 中的标准形式。

## 练习

1. 设 \(A\) 是 \(m \times n\) 矩阵，证明 \(\operatorname{rank}(A) + \operatorname{nullity}(A) = n\)。
2. 利用秩-零化度定理证明：若 \(T: V \to W\) 是单射且 \(\dim(V) = \dim(W)\)，则 \(T\) 也是满射（从而是同构）。
3. 在 Lean4 中，对一个具体的 \(3 \times 5\) 实矩阵计算其秩和零化度。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确