---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Poincaré对偶 (Poincaré Duality)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Cohomology
import Mathlib.AlgebraicTopology.Homology

namespace PoincareDuality

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [OrientableManifold n X]

/-- Poincaré对偶：同调与上同调的同构 -/
theorem poincare_duality (k : ℕ) (hk : k ≤ n) :
    H_k X ≅ H^{n-k} X := by
  -- 利用基本类和杯积
  sorry

/-- 相交形式的非退化性 -/
theorem intersection_form_nondegenerate (hX : Even n) :
    ∀ α : H_{n/2} X, α ≠ 0 → ∃ β, intersectionForm α β ≠ 0 := by
  -- 对偶性的推论
  sorry

/-- Lefschetz对偶（带边界）-/
theorem lefschetz_duality (A : ClosedSubset X) (k : ℕ) :
    H_k (X, A) ≅ H^{n-k} (X \ A) := by
  -- 相对版本的Poincaré对偶
  sorry

end PoincareDuality
```

## 数学背景

Poincaré对偶由Henri Poincaré在1890年代证明，是代数拓扑中最深刻和优美的结果之一。该定理表明，紧致定向流形的同调群和上同调群之间存在对偶关系：$k$ 维同调与 $n-k$ 维上同调同构。这是流形拓扑对称性的体现，有许多重要推论，包括相交理论、特征类和指标定理。

## 直观解释

Poincaré对偶告诉我们：**流形的"洞"在互补维度上成对出现**。

想象一个环面（轮胎形状）。它有一个2维的"内部"洞（表面本身）和一个1维的"环向"洞（绕着轮胎）。Poincaré对偶说这些洞的信息是"对偶"的——知道一维的信息就等价于知道余维数的信息。这就像说，了解一个物体的轮廓等价于了解其内部结构。

## 形式化表述

设 $X$ 是紧致定向 $n$ 维流形。

**Poincaré对偶**：
$$H_k(X) \cong H^{n-k}(X)$$

**交积形式**：在 $H_{n/2}(X) \times H_{n/2}(X) \to \mathbb{Z}$（$n$ 偶数）

**几何解释**：$k$ 维循环与 $(n-k)$ 维循环相交给出点。

**上同调版本**：杯积配对 $H^k(X) \times H^{n-k}(X) \to H^n(X) \cong \mathbb{Z}$ 是非退化的。

## 证明思路

1. **基本类**：
   - $[X] \in H_n(X)$ 是定向给出的生成元

2. **帽积**：
   - $\frown: H^k(X) \times H_n(X) \to H_{n-k}(X)$
   - 与基本类帽积给出对偶映射

3. **Mayer-Vietoris**：
   - 局部到整体的证明
   - 对 $D^n$ 和 $S^n$ 验证

4. **万有系数**：
   - 结合万有系数定理处理挠部分

核心洞察是定向给出的基本类和帽积运算。

## 示例

### 示例 1：球面

$S^n$：$H_0 = H_n = \mathbb{Z}$，其余为0。

对偶：$H_0 \cong H^n$，$H_n \cong H^0$。

### 示例 2：环面

$T^2$：$H_0 = H_2 = \mathbb{Z}$，$H_1 = \mathbb{Z}^2$。

对偶：$H_1 \cong H^1 = \mathbb{Z}^2$。

### 示例 3：复射影平面

$\mathbb{C}P^2$：$H_0 = H_2 = H_4 = \mathbb{Z}$。

对偶：$H_2 \cong H^2 = \mathbb{Z}$。

交积形式：$(\alpha, \alpha) = 1$（正定）。

## 应用

- **指标定理**：Atiyah-Singer指标定理
- **特征类**：Euler类、Pontryagin类的关系
- **手术理论**：流形的分类
- **镜像对称**：Calabi-Yau流形的对偶
- **拓扑场论**：TQFT的代数结构

## 相关概念

- [基本类 (Fundamental Class)](./fundamental-class.md)：定向的最高维同调
- [帽积 (Cap Product)](./cap-product.md)：同调-上同调运算
- [杯积 (Cup Product)](./cup-product.md)：上同调的乘法
- [相交形式 (Intersection Form)](./intersection-form.md)：中间维度的配对
- [定向 (Orientation)](./orientation.md)：流形的一致性定向

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 3]
- [Bott & Tu. Differential Forms in Algebraic Topology. Springer, 1982. Chapter 5]

### 历史文献

- [Poincaré. Analysis situs. 1895]

### 在线资源

- [Mathlib4 文档 - Cohomology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Cohomology.html)
- [Wikipedia - Poincaré Duality](https://en.wikipedia.org/wiki/Poincar%C3%A9_duality)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
