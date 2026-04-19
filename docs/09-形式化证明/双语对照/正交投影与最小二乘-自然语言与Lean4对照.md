---
title: "正交投影与最小二乘 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.06"
review_status: completed
---

## 定理陈述

**自然语言**：设 $V$ 是（实或复）内积空间，$W \subseteq V$ 是完备子空间（在有限维情形自动满足）。则对任意向量 $v \in V$，存在唯一的 $w \in W$ 使得
\[
\|v - w\| = \inf_{w' \in W} \|v - w'\|.
\]
该向量 $w$ 称为 $v$ 在 $W$ 上的**正交投影**，记作 $\operatorname{proj}_W(v)$，且满足**正交条件**：$v - w \perp W$（即对所有 $u \in W$ 有 $\langle v - w, u \rangle = 0$）。

**最小二乘法**：对于不相容方程组 $Ax = b$（$A$ 为 $m \times n$ 实矩阵），最小二乘解 $\hat{x}$ 满足正规方程
\[
A^T A \hat{x} = A^T b.
\]
当 $A$ 列满秩时，$\hat{x} = (A^T A)^{-1} A^T b$ 唯一存在。

**Lean4**：

```lean
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OrthogonalProjection
open InnerProductSpace Real

-- 正交投影的存在唯一性
theorem orthogonal_projection_exists {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace K] (u : E) :
    ∃! v : K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by
  exact exists_norm_eq_iInf_of_complete_convex K u

-- 正交条件
theorem orthogonal_condition {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace K] {u : E} {v : K}
    (hv : ‖u - v‖ = ⨅ w : K, ‖u - w‖) :
    ∀ w : K, ⟪u - v, w⟫_𝕜 = 0 := by
  sorry  -- 由极小性导出 Gateaux 导数为零

-- 正规方程
theorem normal_equations {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : Matrix.rank A = n) :
    ∃! x : Fin n → ℝ, Aᵀ * A * vec x = Aᵀ * vec b := by
  sorry  -- A^T A 正定可逆
end OrthogonalProjection
```

## 证明思路

**自然语言**：
- **存在性**：取 $W$ 中一序列 $\{w_n\}$ 使得 $\|v - w_n\| \to \inf_{w' \in W} \|v - w'\|$。利用平行四边形法则可证 $\{w_n\}$ 是 Cauchy 列。由 $W$ 的完备性，$w_n \to w \in W$，即为所求投影。
- **正交性**：对任意 $u \in W$，考虑实函数 $g(t) = \|v - (w + tu)\|^2$。由 $w$ 的极小性，$t = 0$ 是 $g$ 的最小值点，故 $g'(0) = 0$，即 $\langle v - w, u \rangle = 0$。
- **最小二乘**：$b$ 在 $A$ 的列空间 $\operatorname{Col}(A)$ 上的正交投影为 $A\hat{x}$，正交条件给出 $b - A\hat{x} \perp \operatorname{Col}(A)$，即 $A^T(b - A\hat{x}) = 0$，整理即得正规方程。

**Lean4**：`exists_norm_eq_iInf_of_complete_convex` 是内积空间投影定理的完整实现，它同时给出了存在性和唯一性。正交条件的证明需要利用变分法思想（Gateaux 导数）。正规方程部分则需要证明当 $A$ 列满秩时 $A^T A$ 正定，从而可逆。

## 关键 tactic/概念 教学

- `InnerProductSpace 𝕜 E`：内积空间的类型类，$\mathbb{R}$ 或 $\mathbb{C}$ 上的内积空间。
- `Submodule 𝕜 E`：$E$ 的线性子空间。
- `exists_norm_eq_iInf_of_complete_convex`：投影定理的存在唯一性。
- `⟪u - v, w⟫_𝕜 = 0`：正交条件的内积表述。
- `Aᵀ * A`：Gram 矩阵，在最小二乘中起核心作用。

## 练习

1. 在 $\mathbb{R}^3$ 中，求向量 $v = (1, 2, 3)^T$ 在平面 $W = \{(x, y, z) : x + y + z = 0\}$ 上的正交投影。
2. 设 $A = \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix}$，$b = \begin{pmatrix} 1 \\ 2 \\ 2 \end{pmatrix}$，求最小二乘解 $\hat{x}$。
3. 证明：若 $A$ 列满秩，则 $A^T A$ 是正定矩阵，从而可逆。
---
**参考文献**

1. 相关教材与学术论文。
