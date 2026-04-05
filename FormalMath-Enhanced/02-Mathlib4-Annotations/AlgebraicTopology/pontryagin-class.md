---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Pontryagin类
---
# Pontryagin类

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.PontryaginClass

namespace AlgebraicTopology

/-- Pontryagin类的定义 -/
theorem pontryagin_class
    {B : Type*} [TopologicalSpace B]
    {E : Type*} [TopologicalSpace E]
    (π : E → B) [IsRealVectorBundle E B π] :
    ∃ (p : ℕ → H^{4*}(B, ℤ)),
      p 0 = 1 ∧
      TotalPontryaginClass E = ∏ (1 + p i) := by
  -- 全Pontryagin类分解
  sorry

/-- Pontryagin类与陈类的关系 -/
theorem pontryagin_chern_relation
    {B : Type*} [TopologicalSpace B]
    {E : Type*} [TopologicalSpace E]
    (π : E → B) [IsComplexVectorBundle E B π] :
    TotalPontryaginClass (E.Realification) =
      TotalChernClass E * TotalChernClass (E.Conjugate) := by
  -- 实化丛的Pontryagin类用陈类表示
  sorry

end AlgebraicTopology
```

## 数学背景

Pontryagin类由Lev Pontryagin在1940年代引入，是实向量丛的整数系数示性类。与Stiefel-Whitney类（模2系数）不同，Pontryagin类提供了更精细的拓扑信息，但在2挠部分会丢失信息。Pontryagin类在流形的配边分类、Hirzebruch符号定理和指数定理中起核心作用。它们也与实向量丛的曲率有关，是Chern-Weil理论的重要组成部分。

## 直观解释

Pontryagin类可以看作是"复化后的Chern类"。对实向量丛 $E$，我们可以将其复化得到 $E \otimes \mathbb{C}$，然后定义 $p_k(E) = (-1)^k c_{2k}(E \otimes \mathbb{C})$。这意味着Pontryagin类度量了实丛在复化后"偶数维"的扭曲。由于复化的对称性，奇数Chern类相互抵消，只剩下偶数类。几何上，$p_k$ 与丛的曲率有关，可以通过Chern-Weil理论用曲率形式表示。

## 形式化表述

设 $\pi: E \to B$ 是秩 $n$ 的实向量丛。

**定义**：$p_k(E) = (-1)^k c_{2k}(E \otimes \mathbb{C}) \in H^{4k}(B; \mathbb{Z})$

**全Pontryagin类**：$p(E) = 1 + p_1(E) + p_2(E) + \cdots$

**公理化性质**：

1. **函子性**：$p(f^*E) = f^*p(E)$
2. **Whitney和**：$p(E \oplus F) = p(E) \cdot p(F)$（模2挠）
3. **归一化**：$p_1(\gamma^2_\mathbb{C}) = 1$（标准线丛）

**曲率表示**：若 $\nabla$ 是联络，曲率 $R$，则
$$p(E) = \det(I + \frac{1}{2\pi} R)$$

## 证明思路

1. **复化构造**：$E \mapsto E \otimes \mathbb{C}$
2. **Chern类拉回**：定义 $p_k$ 用复化的Chern类
3. **实结构**：利用共轭对称性
4. **分类空间**：$BO(n)$ 和 $BU(n)$ 的关系
5. **曲率表示**：Chern-Weil理论的应用

## 示例

### 示例 1：复射影空间的Pontryagin类

**问题**：计算 $\mathbb{CP}^n$ 的Pontryagin类。

**解答**：

切丛的复化：$T\mathbb{CP}^n \otimes \mathbb{C} \cong T^{1,0} \oplus T^{0,1}$

利用 $c(T^{0,1}) = \overline{c(T^{1,0})}$：
$$p(T\mathbb{CP}^n) = (1 + c_1^2)(1 + c_1^2 + c_2^2) \cdots$$

对 $\mathbb{CP}^2$：$p_1 = 3H^2$。

### 示例 2：符号定理

**问题**：用Pontryagin类表达4k维流形的符号差。

**解答**：

Hirzebruch符号定理：
$$\sigma(M^{4k}) = \langle L_k(p_1, \ldots, p_k), [M] \rangle$$

其中 $L_k$ 是Hirzebruch L-多项式。

对4维流形：$\sigma(M) = \frac{1}{3}\langle p_1(TM), [M] \rangle$。

## 应用

- **符号定理**：Hirzebruch符号定理
- **指数定理**：Atiyah-Singer定理的实版本
- **配边理论**： oriented配边环的计算
- **surgery理论**：障碍类的定义
- **极小子流形**：Gauss映射的Pontryagin类

## 相关概念

- [Chern类](./chern-class.md)：复丛的基础示性类
- [Stiefel-Whitney类](./stiefel-whitney-class.md)：模2系数的实丛示性类
- Hirzebruch L-类：符号定理中的多项式
- A-帽类：Dirac算子的指标
- Todd类：复几何中的相关类

## 参考

### 教材

- Milnor, J.W. & Stasheff, J.D. Characteristic Classes. Princeton, 1974.
- Hirzebruch, F. Topological Methods in Algebraic Geometry. Springer, 1966.

### 论文

- Pontryagin, L.S. Characteristic cycles on differentiable manifolds. Mat. Sb., 21: 233-284, 1947.
- Thom, R. Espaces fibrés en sphères et carrés de Steenrod. Ann. Sci. École Norm. Sup., 69: 109-182, 1952.

### 在线资源

- [Pontryagin Class Wikipedia](https://en.wikipedia.org/wiki/Pontryagin_class)
- [nLab - Pontryagin Class](https://ncatlab.org/nlab/show/Pontryagin+class)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
