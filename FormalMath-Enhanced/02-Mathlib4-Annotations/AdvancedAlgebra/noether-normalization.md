---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Noether正规化定理
---
# Noether正规化定理

## Mathlib4 引用

```lean
import Mathlib.RingTheory.NoetherNormalization

namespace CommutativeAlgebra

/-- Noether正规化定理 -/
theorem noether_normalization
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    [IsNoetherian k A] (hA : FiniteType k A) :
    ∃ (n : ℕ) (y : Fin n → A),
      Algebra.Independent k y ∧
      IsIntegral (Polynomial (Fin n k)) A := by
  -- 存在代数独立的元素使得A在其上整
  sorry

end CommutativeAlgebra
```

## 数学背景

Noether正规化定理由Emmy Noether在1926年证明，是交换代数和代数几何中最基本的结果之一。定理表明：任何有限生成的代数都可以被"参数化"为一个多项式环的整扩张。这为研究仿射代数簇的维数提供了基础，也是证明Hilbert零点定理的关键步骤。Noether正规化定理是连接代数与几何的桥梁，将抽象代数结构具体化为几何参数空间上的覆盖。

## 直观解释

Noether正规化如同为代数簇找到一个"好的坐标系"。想象一个复杂的代数簇 $X$ ——Noether正规化告诉我们：存在 $n$ 个"独立"的坐标函数，使得 $X$ 可以看作是 $n$ 维仿射空间的一个"多对一"覆盖（整扩张）。这就像将复杂的几何对象"投影"到简单空间上，虽然可能有多重点（整性），但整体结构被很好地控制。$n$ 就是代数簇的维数。

## 形式化表述

设 $k$ 是域，$A$ 是有限生成 $k$-代数。

**Noether正规化定理**：存在代数独立的元素 $y_1, \ldots, y_n \in A$，使得 $A$ 在 $k[y_1, \ldots, y_n]$ 上整。

**等价表述**：若 $A = k[x_1, \ldots, x_m]/I$，则存在线性变换 $y_i = \sum a_{ij} x_j$ 使得 $A$ 在 $k[y_1, \ldots, y_n]$ 上整。

**维数推论**：$\dim(A) = n$（超越度）。

## 证明思路

1. **归纳法**：对生成元个数归纳
2. **多项式关系**：利用代数相关性
3. **变量替换**：构造适当的线性变换
4. **整性验证**：证明新变量使扩张整
5. **维数计算**：超越度等于整扩张的维数

## 示例

### 示例 1：平面曲线

**问题**：对 $A = k[x,y]/(xy-1)$ 应用Noether正规化。

**解答**：

$xy = 1$ 表明 $x$ 和 $y$ 都超越于 $k$。

取 $t = x + y$，则 $x$ 满足 $t = x + 1/x$，即 $x^2 - tx + 1 = 0$。

因此 $A$ 在 $k[t]$ 上整，维数为1。

### 示例 2：射影簇的仿射锥

**问题**：描述射影簇的仿射锥的Noether正规化。

**解答**：

设 $X \subseteq \mathbb{P}^n$ 是射影簇，$C(X) \subseteq \mathbb{A}^{n+1}$ 是其仿射锥。

若 $X$ 的维数为 $d$，则 $C(X)$ 的维数为 $d+1$。

Noether正规化给出 $k[y_0, \ldots, y_d] \hookrightarrow \mathcal{O}(C(X))$ 是整扩张。

## 应用

- **Hilbert零点定理**：代数集与理想的对应
- **维数理论**：Krull维数的计算
- **整闭包**：代数整闭包的有限性
- **Galois理论**：扩张的分类
- **不变量理论**：Hilbert第14问题

## 相关概念

- [Krull维数](./krull-dimension.md)：Noether正规化计算的对象
- 整扩张：Noether正规化的核心
- 代数独立性：正规化元的性质
- Hilbert零点定理：Noether正规化的应用
- 超越基：正规化元的几何意义

## 参考

### 教材

- Eisenbud, D. Commutative Algebra with a View Toward Algebraic Geometry. Springer, 1995. Chapter 13
- Atiyah, M.F. & Macdonald, I.G. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 5

### 论文

- Noether, E. Der Endlichkeitssatz der Invarianten endlicher linearer Gruppen der Charakteristik p. Nachr. Ges. Wiss. Göttingen, 28-35, 1926.

### 在线资源

- [Noether Normalization Lemma Wikipedia](https://en.wikipedia.org/wiki/Noether_normalization_lemma)
- [Stacks Project - Noether Normalization](https://stacks.math.columbia.edu/tag/00OW)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
