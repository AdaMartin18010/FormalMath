---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Hodge分解定理
---
# Hodge分解定理

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.HodgeTheory

namespace Geometry

/-- Hodge分解定理 -/
theorem hodge_decomposition
    {M : Type*} [CompactOrientedRiemannianManifold M]
    {k : ℕ} :
    DifferentialForm M k =
      (HarmonicForms M k) ⊕
      (ExactForms M k) ⊕
      (CoexactForms M k) := by
  -- 微分形式分解为调和、恰当和余恰当部分
  sorry

/-- Hodge定理 -/
theorem hodge_theorem
    {M : Type*} [CompactOrientedRiemannianManifold M]
    {k : ℕ} :
    DeRhamCohomology M k ≅ HarmonicForms M k := by
  -- 调和形式代表de Rham上同调类
  sorry

end Geometry
```

## 数学背景

Hodge分解定理由W.V.D. Hodge在1930年代证明，是微分几何和代数几何中的里程碑结果。定理表明，在紧定向Riemann流形上，微分形式可以唯一分解为调和形式、恰当形式和余恰当形式的直和。这给出了de Rham上同调的一个典范代表——调和形式，将分析（Laplace算子）与拓扑（上同调）联系起来。Hodge理论在Kähler流形上尤为强大，产生了著名的Hodge分解。

## 直观解释

Hodge分解如同将一个向量场分解为不同"成分"：无旋（调和）、有源（恰当）和有旋（余恰当）。调和形式是"最简"的微分形式——它们同时是闭的（$d\omega = 0$）和余闭的（$d^*\omega = 0$），类似于向量分析中的无源无旋场。每个上同调类有唯一的调和代表，这给了我们计算拓扑不变量的分析工具。

## 形式化表述

设 $M$ 是紧定向Riemann流形，$\Omega^k(M)$ 是光滑 $k$-形式空间。

**Laplace算子**：$\Delta = dd^* + d^*d$

**调和形式**：$\mathcal{H}^k(M) = \{\omega \in \Omega^k(M) : \Delta \omega = 0\}$

**Hodge分解**：
$$\Omega^k(M) = \mathcal{H}^k(M) \oplus d(\Omega^{k-1}(M)) \oplus d^*(\Omega^{k+1}(M))$$

**Hodge定理**：映射 $\mathcal{H}^k(M) \to H^k_{\text{dR}}(M)$ 是同构。

## 证明思路

1. **椭圆算子理论**：证明 $\Delta$ 是椭圆算子
2. **Fredholm理论**：紧流形上调和形式有限维
3. **Green算子**：构造伪逆
4. **正交分解**：利用内积结构
5. **同构证明**：验证调和形式代表上同调类

## 示例

### 示例 1：圆周

**问题**：描述 $S^1$ 上的Hodge分解。

**解答**：

0-形式：$\Omega^0(S^1) = C^\infty(S^1)$

调和0-形式是常数函数：$\mathcal{H}^0(S^1) = \mathbb{R}$

1-形式：$\mathcal{H}^1(S^1) = \mathbb{R} \cdot d\theta$

因此 $H^0(S^1) = H^1(S^1) = \mathbb{R}$，符合已知结果。

### 示例 2：复射影直线

**问题**：描述 $\mathbb{CP}^1$ 上的Hodge分解。

**解答**：

$\mathbb{CP}^1 \cong S^2$，Betti数：$b_0 = b_2 = 1$，$b_1 = 0$。

Hodge数：$h^{0,0} = h^{1,1} = 1$，$h^{1,0} = h^{0,1} = 0$。

调和形式：常数函数和体积形式。

## 应用

- **代数几何**：周期映射和Torelli定理
- **数论**：Shimura簇的Hodge理论
- **物理**：超引力和紧致化
- **几何分析**：热方程方法和谱几何
- **拓扑**：示性类的表示

## 相关概念

- [Kähler几何](./kahler-geometry.md)：Hodge理论的强化版本
- [de Rham上同调](./de-rham-cohomology.md)：Hodge理论的目标
- [Laplace算子](./laplace-operator.md)：Hodge理论的核心算子
- [椭圆算子](./elliptic-operator.md)：分析基础
- [周期积分](./period-integral.md)：Hodge理论的应用

## 参考

### 教材

- Warner, F.W. Foundations of Differentiable Manifolds and Lie Groups. Springer, 1983. Chapter 6
- Wells, R.O. Differential Analysis on Complex Manifolds. Springer, 2008.

### 论文

- Hodge, W.V.D. The Theory and Applications of Harmonic Integrals. Cambridge University Press, 1941.
- Kodaira, K. Harmonic fields in Riemannian manifolds. Ann. of Math., 50: 587-665, 1949.

### 在线资源

- [Hodge Theory Wikipedia](https://en.wikipedia.org/wiki/Hodge_theory)
- [nLab - Hodge Theory](https://ncatlab.org/nlab/show/Hodge+theory)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
