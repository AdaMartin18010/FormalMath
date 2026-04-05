---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Stiefel-Whitney类
---
# Stiefel-Whitney类

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.StiefelWhitneyClass

namespace AlgebraicTopology

/-- Stiefel-Whitney类的定义 -/
theorem stiefel_whitney_class
    {B : Type*} [TopologicalSpace B]
    {E : Type*} [TopologicalSpace E]
    (π : E → B) [IsRealVectorBundle E B π] :
    ∃ (w : ℕ → H^{*}(B, ZMod 2)),
      w 0 = 1 ∧
      TotalStiefelWhitneyClass E = ∏ (1 + w i) := by
  -- 全Stiefel-Whitney类分解
  sorry

/-- Whitney积公式 -/
theorem whitney_product_formula
    {B : Type*} [TopologicalSpace B]
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (π_E : E → B) (π_F : F → B)
    [IsRealVectorBundle E B π_E]
    [IsRealVectorBundle F B π_F] :
    TotalStiefelWhitneyClass (E ⊕ F) =
      TotalStiefelWhitneyClass E *
      TotalStiefelWhitneyClass F := by
  -- 直和丛的SW类相乘
  sorry

end AlgebraicTopology
```

## 数学背景

Stiefel-Whitney类由Eduard Stiefel和Hassler Whitney在1930年代独立引入，是实向量丛的基本拓扑不变量。与Chern类不同，SW类取模2值系数，具有更基本的拓扑意义。它们可以判断流形的定向性、旋量结构和浸入/嵌入的可能性。Whitney用SW类证明了著名的嵌入定理：任何 $n$ 维流形可以嵌入 $\mathbb{R}^{2n}$。SW类也是 surgery 理论和配边理论的核心工具。

## 直观解释

Stiefel-Whitney类如同实向量丛的"扭曲度量"。想象一个实向量丛在空间 $B$ 上"编织"。$w_1$ 告诉我们这个丛是否可以定向（$w_1 = 0$ 当且仅当可定向）；$w_2$ 告诉我们是否可以定义旋量结构；更高阶的类则度量了更复杂的"打结"方式。模2系数的意义在于：我们只关心奇偶性——一个扭曲要么存在要么不存在，不考虑"多重性"。

## 形式化表述

设 $\pi: E \to B$ 是秩 $n$ 的实向量丛。

**全Stiefel-Whitney类**：$w(E) = 1 + w_1(E) + w_2(E) + \cdots + w_n(E)$，其中 $w_k(E) \in H^k(B; \mathbb{Z}/2)$。

**公理化刻画**：

1. **函子性**：$w(f^*E) = f^*w(E)$
2. **Whitney积**：$w(E \oplus F) = w(E) \cdot w(F)$
3. **归一化**：Möbius丛 $M \to S^1$ 的 $w_1(M) \neq 0$

**应用**：

- $w_1(TM) = 0$ ⟺ $M$ 可定向
- $w_2(TM) = 0$ ⟺ $M$ 有旋量结构

## 证明思路

1. **分类空间**：用 $BO(n)$ 的上同调定义SW类
2. **分裂原理**：实丛的分裂（在模2意义下）
3. **Steenrod平方**：SW类可用 $Sq^k$ 表示
4. **Thom同构**：SW类作为Thom类的拉回
5. **Wu公式**：SW类与Steenrod运算的关系

## 示例

### 示例 1：实射影空间的SW类

**问题**：计算 $\mathbb{RP}^n$ 的Stiefel-Whitney类。

**解答**：

切丛的SW类：
$$w(T\mathbb{RP}^n) = (1 + a)^{n+1}$$
其中 $a = w_1(\gamma^1) \in H^1(\mathbb{RP}^n; \mathbb{Z}/2)$ 是生成元。

例如 $w(T\mathbb{RP}^2) = 1 + a + a^2$。

### 示例 2：浸入问题

**问题**：$\mathbb{RP}^n$ 何时能浸入 $\mathbb{R}^{n+k}$？

**解答**：

Whitney-Graustein定理：若 $T\mathbb{RP}^n$ 有 $k$ 个线性无关截面，则可浸入。

用SW类：需要 $\bar{w}_k(T\mathbb{RP}^n) = 0$ 对 $k > n$。

Massey证明了 $\mathbb{RP}^n$ 浸入 $\mathbb{R}^{2n - \alpha(n)}$ 其中 $\alpha(n)$ 是二进制1的个数。

## 应用

- **浸入/嵌入**：Whitney浸入定理和嵌入定理
- **可定向性**：$w_1 = 0$ 的判别
- **旋量结构**：$w_1 = w_2 = 0$ 的条件
- **配边理论**：Thom配边环的计算
- **示性数**：Stiefel-Whitney数的配边不变性

## 相关概念

- [Chern类](./chern-class.md)：复丛的版本
- [Pontryagin类](./pontryagin-class.md)：整数系数的实丛不变量
- Wu类：Steenrod平方与SW类的关系
- Thom类：SW类的构造
- Euler类：最高SW类（定向情形）

## 参考

### 教材

- Milnor, J.W. & Stasheff, J.D. Characteristic Classes. Princeton, 1974.
- Hatcher, A. Vector Bundles and K-Theory. Available online.

### 论文

- Stiefel, E. Richtungsfelder und Fernparallelismus in n-dimensionalen Mannigfaltigkeiten. Comm. Math. Helv., 8: 305-353, 1935.
- Whitney, H. On the theory of sphere bundles. Proc. Nat. Acad. Sci. USA, 26: 148-153, 1940.

### 在线资源

- [Stiefel-Whitney Class Wikipedia](https://en.wikipedia.org/wiki/Stiefel%E2%80%93Whitney_class)
- [nLab - Stiefel-Whitney Class](https://ncatlab.org/nlab/show/Stiefel-Whitney+class)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
