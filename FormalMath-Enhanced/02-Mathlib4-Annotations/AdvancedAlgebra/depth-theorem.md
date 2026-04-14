---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 深度定理
---
# 深度定理

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Depth

namespace CommutativeAlgebra

/-- 深度的定义 -/
theorem depth_def
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    [IsNoetherianModule M] (I : Ideal R) :
    depth I M =
      sInf {n | Ext R n (R ⧸ I) M ≠ 0} := by
  -- 深度作为Ext首次非零的指标
  rfl

/-- Auslander-Buchsbaum公式 -/
theorem auslander_buchsbaum
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [IsNoetherianModule M]
    [Module.FinitePresentation R M] :
    depth (maximalIdeal R) M + projectiveDimension M =
      depth (maximalIdeal R) R := by
  -- 正则局部环上的基本公式
  apply auslander_buchsbaum_formula

end CommutativeAlgebra
```

## 数学背景

深度（depth）是交换代数中一个基本的同调不变量，度量了模"非奇异"的程度。它由Auslander和Buchsbaum在1950年代系统研究，并与正则序列、局部上同调理论密切相关。Auslander-Buchsbaum公式建立了深度、投射维数和环深度之间的深刻联系，是正则局部环理论的核心结果。深度理论在Cohen-Macaulay环、Gorenstein环的研究中有核心地位。

## 直观解释

深度度量了一个模上"正则序列"的最大长度——即一个序列，其中每个元素在被前一个元素模掉后仍不是零因子。想象一个模作为空间，正则元素如同"钻孔"操作——每次钻孔（模去一个元素）后，新的空间仍然有"厚度"。深度告诉我们能钻多少次孔而空间不坍塌。对于局部环本身，深度度量了从极大理想中能提取多少"独立信息"。

## 形式化表述

设 $(R, \mathfrak{m})$ 是诺特局部环，$M$ 是有限生成 $R$-模。

**定义**：$\text{depth}_{\mathfrak{m}}(M) = \sup\{n : \exists x_1, \ldots, x_n \in \mathfrak{m} \text{ 构成$M$-正则序列}\}$

**同调刻画**：
$$\text{depth}_{\mathfrak{m}}(M) = \inf\{i : \text{Ext}^i_R(R/\mathfrak{m}, M) \neq 0\}$$

**Auslander-Buchsbaum公式**（$R$ 正则局部环）：
$$\text{depth}(M) + \text{pd}_R(M) = \text{depth}(R)$$

## 证明思路

1. **正则序列性质**：证明正则序列可延长直到达到深度
2. **Ext刻画**：利用Koszul复形或正则序列的性质
3. **Auslander-Buchsbaum公式**：对投射维数归纳，利用长正合列
4. **维数不等式**：证明 $\text{depth}(M) \leq \dim(M)$

## 示例

### 示例 1：多项式环的深度

**问题**：计算 $R = k[x,y,z]_{(x,y,z)}$ 的深度。

**解答**：

$R$ 是正则局部环，维数为3。$x, y, z$ 构成正则序列：

- $x$ 不是零因子
- 在 $R/(x)$ 中，$y$ 不是零因子
- 在 $R/(x,y)$ 中，$z$ 不是零因子

因此 $\text{depth}(R) = 3 = \dim(R)$。

### 示例 2：非CM模的深度

**问题**：设 $R = k[x,y]_{(x,y)}$，$M = R/(x)$，计算 $\text{depth}(M)$。

**解答**：

在 $M$ 上，$y$ 不是零因子（$M \cong k[y]$）。

但 $x$ 在 $M$ 上是零：$x \cdot 1 = 0$。

因此 $\text{depth}(M) = 1 < 2 = \dim(R)$，$M$ 不是CM模。

## 应用

- **Cohen-Macaulay理论**：深度等于维数的刻画
- **正则局部环**：Auslander-Buchsbaum公式的应用
- **交截重数**：Serre交截理论
- **奇点解消**：深度的变化分析
- **同调猜想**：许多猜想的深度版本

## 相关概念

- [Cohen-Macaulay环](./cohen-macaulay-ring.md)：深度等于维数的环
- 投射维数：Auslander-Buchsbaum公式的组成部分
- 正则序列：深度的构造工具
- 局部上同调：深度的另一种刻画
- [Krull维数](./krull-dimension.md)：与深度的基本不等式

## 参考

### 教材

- Eisenbud, D. Commutative Algebra with a View Toward Algebraic Geometry. Springer, 1995. Chapter 17
- Matsumura, H. Commutative Ring Theory. Cambridge, 1986. Chapter 6

### 论文

- Auslander, M. & Buchsbaum, D.A. Homological dimension in local rings. Trans. Amer. Math. Soc., 85: 390-405, 1957.
- Auslander, M. & Buchsbaum, D.A. Codimension and multiplicity. Ann. of Math., 68: 625-657, 1958.

### 在线资源

- [Depth (Ring Theory) Wikipedia](https://en.wikipedia.org/wiki/Depth_(ring_theory))
- [Stacks Project - Depth][https://stacks.math.columbia.edu/tag/00LF](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
