---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Stone-Weierstrass定理 (Stone-Weierstrass Theorem)
---
# Stone-Weierstrass定理 (Stone-Weierstrass Theorem)

## Mathlib4 引用

```lean
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.Separation

namespace StoneWeierstrass

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Stone-Weierstrass定理 -/
theorem stone_weierstrass (A : Subalgebra ℝ C(X, ℝ))
    (hsep : SeparatesPoints A) (hnonvanish : ∀ x, ∃ f ∈ A, f x ≠ 0) :
    Dense (A : Set C(X, ℝ)) := by
  -- 证明子代数在连续函数空间中稠密
  sorry

/-- 复版本 -/
theorem stone_weierstrass_complex (A : Subalgebra ℂ C(X, ℂ))
    (hsep : SeparatesPoints A) (hclosed : ∀ f ∈ A, star f ∈ A) :
    Dense (A : Set C(X, ℂ)) := by
  -- 需要自伴条件
  sorry

/-- Weierstrass逼近定理作为推论 -/
theorem weierstrass_from_stone (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x, |f x - p.eval x| < ε := by
  -- 多项式构成稠密子代数
  sorry

end StoneWeierstrass
```

## 数学背景

Stone-Weierstrass定理由马歇尔·斯通（Marshall Stone）于1937年证明，是Weierstrass逼近定理的深远推广。它将多项式逼近的理论从区间推广到任意紧致Hausdorff空间，用拓扑代数的语言刻画了函数代数何时稠密。这是泛函分析和拓扑学交叉的典范结果。

## 直观解释

Stone-Weierstrass定理告诉我们：**如果一族函数能"区分"所有点且"足够丰富"，那么它们就能逼近任何连续函数**。就像一组"基向量"，如果能区分空间中每一点的不同"特征"，那么它们的线性组合就能表达任何函数。

## 形式化表述

设 $X$ 是紧致Hausdorff空间，$A \subset C(X, \mathbb{R})$ 是子代数（对加、乘、数乘封闭）。

**Stone-Weierstrass定理**：若 $A$ 满足：
1. **分离点**：对任意 $x \neq y$，存在 $f \in A$ 使 $f(x) \neq f(y)$
2. **包含常数**（或无处同时为零）

则 $A$ 在 $C(X, \mathbb{R})$ 中稠密（上确界范数）。

**复版本**：需要额外假设 $A$ 对共轭封闭（自伴）。

## 证明思路

1. **归一化**：先证 $A$ 的闭包是闭子代数
2. **绝对值逼近**：利用Weierstrass定理逼近 $|t|$
3. **格结构**：证明闭包是子格（对 $\max$、$\min$ 封闭）
4. **插值**：在有限点集上精确插值
5. **稠密性**：任意连续函数可被逼近

## 示例

### 示例 1：三角多项式

在 $S^1$ 上，三角多项式 $\sum_{k=-n}^n c_k e^{ik\theta}$ 构成稠密子代数。

由Stone-Weierstrass，Fourier级数一致逼近连续函数。

### 示例 2：多元多项式

在 $[0,1]^n$ 上，多元多项式稠密。

多项式分离点（投影坐标），包含常数。

### 示例 3：代数函数

紧致流形上的光滑函数可以分离点，故稠密。

## 应用

- **调和分析**：几乎周期函数理论
- **算子代数**：$C^*$-代数的表示
- **逼近理论**：神经网络逼近（通用逼近定理）
- **遍历理论**：不变测度存在性
- **复几何**：全纯函数逼近

## 相关概念

- [Weierstrass逼近定理](./weierstrass-approximation.md)：一维版本
- [子代数](./subalgebra.md)：函数的代数结构
- [分离点](./separates-points.md)：区分不同点的能力
- [Gelfand表示](./gelfand-representation.md)：$C^*$-代数理论

## 参考

### 教材

- [Rudin. Functional Analysis. McGraw-Hill, 2nd edition, 1991. Chapter 5]
- [Conway. A Course in Functional Analysis. Springer, 1990. Chapter 8]

### 历史文献

- [Stone. Applications of the theory of Boolean rings to general topology. 1937]

### 在线资源

- [Mathlib4 文档 - Continuous Function Algebra](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Algebra.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
