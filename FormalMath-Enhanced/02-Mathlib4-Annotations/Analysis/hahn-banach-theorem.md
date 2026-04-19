---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Hahn-Banach定理 (Hahn-Banach Theorem)
---
# Hahn-Banach定理 (Hahn-Banach Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.Dual

namespace HahnBanach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : E → ℝ} (hp : ∃ c, ∀ x y, p (x + y) ≤ p x + p y ∧ p (c • x) = c * p x)

/-- Hahn-Banach定理：次线性泛函控制下的延拓 -/
theorem hahn_banach {M : Subspace ℝ E} {f : M →L[ℝ] ℝ}
    (hf : ∀ x : M, f x ≤ p x) :
    ∃ g : E →L[ℝ] ℝ, (∀ x : M, g x = f x) ∧ (∀ x : E, g x ≤ p x) := by
  -- Zorn引理的应用
  sorry

/-- Hahn-Banach定理（范数保持版本）-/
theorem hahn_banach_norm {M : Subspace ℝ E} {f : M →L[ℝ] ℝ} :
    ∃ g : E →L[ℝ] ℝ, (∀ x : M, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  let p := fun x => ‖f‖ * ‖x‖
  have hp : ∀ x : M, f x ≤ p x := by
    intro x
    exact le_trans (norm_continuousLinearMap_apply_le f x) (le_of_eq (by simp [p]))
  rcases hahn_banach hp with ⟨g, hg_eq, hg_le⟩
  use g
  constructor
  · exact hg_eq
  · -- 证明范数相等
    sorry

/-- 几何形式：分离超平面定理 -/
theorem separation_hyperplane {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAopen : IsOpen A) (hdisj : Disjoint A B) :
    ∃ f : E →L[ℝ] ℝ, ∃ c : ℝ, (∀ x ∈ A, f x < c) ∧ (∀ x ∈ B, f x ≥ c) := by
  sorry

end HahnBanach
```

## 数学背景

Hahn-Banach定理由Hans Hahn在1927年和Stefan Banach在1929年独立证明（Banach的博士论文中），是泛函分析中最基本和最有力的结果之一。该定理保证了定义在子空间上的有界线性泛函可以保持范数延拓到全空间。这一结果是凸分析、对偶理论、优化理论和经济学的基石，有重要的几何解释（分离超平面定理）。

## 直观解释

Hahn-Banach定理告诉我们：**在一个"小"空间上定义的"好"泛函，总可以无损地延拓到"大"空间**。

想象你在一个平面上（子空间）定义了一个测量（线性泛函）。Hahn-Banach定理说，你可以把这个测量"推广"到整个三维空间，且不改变它在原平面上的值，也不增加测量的"强度"（范数）。这就像说，局部定义的规则总可以一致地扩展到全局。

## 形式化表述

设 $E$ 是实赋范空间，$M \subseteq E$ 是子空间，$f: M \to \mathbb{R}$ 是有界线性泛函。

**Hahn-Banach定理（分析形式）**：
存在有界线性泛函 $g: E \to \mathbb{R}$ 使得：

1. $g|_M = f$（延拓）
2. $\|g\| = \|f\|$（范数保持）

**Hahn-Banach定理（几何形式）**：
设 $A, B$ 是 $E$ 中不相交凸集，$A$ 开，则存在超平面分离 $A$ 和 $B$。

## 证明思路

1. **一维延拓**：
   - 取 $x_0 \notin M$，定义 $M_1 = M \oplus \mathbb{R}x_0$
   - 构造 $g_1$ 在 $M_1$ 上，保持 $g_1|_M = f$ 和 $g_1 \leq p$

2. **Zorn引理**：
   - 考虑所有延拓的偏序集
   - 证明任何链有上界（取并）
   - 由Zorn引理，存在极大元

3. **极大性蕴含全空间**：
   - 若定义域不是全空间，可做一维延拓
   - 矛盾，故极大元的定义域是全空间

4. **范数保持**：取 $p(x) = \|f\| \|x\|$

核心洞察是次线性泛函的凸性和Zorn引理。

## 示例

### 示例 1：对偶空间非平凡

设 $E$ 是赋范空间，$x_0 \neq 0$。

在 $\text{span}\{x_0\}$ 上定义 $f(tx_0) = t\|x_0\|$。

Hahn-Banach给出 $g \in E^*$ 使 $g(x_0) = \|x_0\|$ 且 $\|g\| = 1$。

### 示例 2：点与凸集的分离

设 $E = \mathbb{R}^2$，$A = \{(x,y) : x^2 + y^2 < 1\}$，$B = \{(2, 0)\}$。

分离超平面：$f(x,y) = x$，$c = 1.5$。

$A$ 中 $f < 1.5$，$B$ 中 $f = 2 > 1.5$。

### 示例 3：优化中的应用

凸优化问题中的Lagrange乘子存在性可由Hahn-Banach导出。

## 应用

- **对偶理论**：对偶空间 $E^*$ 的"丰富性"（分离点）
- **凸分析**：分离超平面、支持函数
- **偏微分方程**：弱解的存在性
- **测度论**：Riesz表示定理的证明
- **经济学**：均衡存在性、定价泛函

## 相关概念

- 对偶空间 (Dual Space)：连续线性泛函空间
- 次线性泛函 (Sublinear Functional)：凸正齐次函数
- 分离超平面 (Separating Hyperplane)：凸集分离
- Minkowski泛函 (Minkowski Functional)：范数的推广
- 凸集 (Convex Set)：线段包含性

## 参考

### 教材

- [Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 3]
- [Conway. A Course in Functional Analysis. Springer, 2nd edition, 1990. Chapter 6]

### 历史文献

- [Hahn. Über lineare Gleichungssysteme in linearen Räumen. 1927]
- [Banach. Sur les fonctionnelles linéaires. 1929]

### 在线资源

- [Mathlib4 文档 - HahnBanach][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach/Extension.html](需更新)
- [Wikipedia - Hahn-Banach Theorem](https://en.wikipedia.org/wiki/Hahn%E2%80%93Banach_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
