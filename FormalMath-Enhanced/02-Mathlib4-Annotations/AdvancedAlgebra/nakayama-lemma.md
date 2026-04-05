---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Nakayama引理
---
# Nakayama引理

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Nakayama

namespace CommutativeAlgebra

/-- Nakayama引理 -/
theorem nakayama_lemma
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : I ⊆ JacobsonRadical R)
    {N : Submodule R M} [Module.Finite R M]
    (h : M = N + I • M) :
    M = N := by
  -- 若M/N = I(M/N)则M/N = 0
  sorry

/--  Nakayama引理的推论 -/
theorem nakayama_corollary
    {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    {m : MaximalIdeal R} :
    Module.span R (M ⧸ (m • M)) = M ⧸ (m • M) →
    Module.span R M = M := by
  -- 生成元提升
  sorry

end CommutativeAlgebra
```

## 数学背景

Nakayama引理由Tadashi Nakayama在1951年证明（尽管特殊情形更早被Krull和Azumaya所知），是交换代数中最基本且广泛应用的引理之一。它建立了模的生成性质与其"剩余"（模去Jacobson根）之间的关系。Nakayama引理是研究有限生成模、投射模和平坦模的不可或缺的工具，也是代数几何中研究概形局部性质的基础。

## 直观解释

Nakayama引理如同一个"局部到整体"的桥梁。想象一个模 $M$ 如同一个几何对象，Jacobson根中的元素如同"接近于零"的量。引理说：如果一个性质在"模去接近于零的量"后成立（即 $M/IM$ 由某些元素生成），那么这个性质在整体上成立（$M$ 本身由这些元素的提升生成）。这类似于隐函数定理——从近似解得到精确解。

## 形式化表述

设 $R$ 是交换环，$J(R)$ 是Jacobson根，$M$ 是有限生成 $R$-模。

**Nakayama引理**：若 $I \subseteq J(R)$ 且 $M = IM + N$，则 $M = N$。

**等价表述**：若 $M = IM$，则 $M = 0$。

**几何版本**（局部环）：设 $(R, \mathfrak{m})$ 是局部环，$M$ 有限生成。

若 $m_1, \ldots, m_n$ 在 $M/\mathfrak{m}M$ 中的像生成 $M/\mathfrak{m}M$，则 $m_1, \ldots, m_n$ 生成 $M$。

## 证明思路

1. **行列式技巧**：利用Cayley-Hamilton定理
2. **局部化**：先证明局部情形
3. **降秩论证**：对模的秩归纳
4. **Jacobson根性质**：$1 + x$ 对 $x \in I$ 可逆
5. **逆元存在性**：构造关键元素的逆

## 示例

### 示例 1：局部环上的自由模

**问题**：证明局部环上的有限生成投射模是自由的。

**解答**：

设 $(R, \mathfrak{m})$ 是局部环，$P$ 是有限生成投射模。

$P/\mathfrak{m}P$ 是 $R/\mathfrak{m}$-向量空间，有基 $\bar{p}_1, \ldots, \bar{p}_n$。

由Nakayama，$p_1, \ldots, p_n$ 生成 $P$。

投射性保证这是基，故 $P \cong R^n$。

### 示例 2：平坦性判别

**问题**：用Nakayama判别局部环上模的平坦性。

**解答**：

$(R, \mathfrak{m})$ 上有限生成模 $M$ 平坦当且仅当自由。

证明概要：

- 平坦模的Tor消失：$\text{Tor}_1^R(M, R/\mathfrak{m}) = 0$
- 由Nakayama，$M$ 自由当且仅当 $M/\mathfrak{m}M$ 自由

## 应用

- **投射模**：局部自由性的证明
- **平坦模**：平坦性的局部判别
- **Krull交集定理**：理想的交为零
- **完备化**：$\mathfrak{m}$-adic拓扑的性质
- **形变理论**：障碍理论中的生成元提升

## 相关概念

- Jacobson根：Nakayama引理中的关键理想
- 局部环：Nakayama引理最常用的场景
- 有限生成模：引理的适用范围
- 完备化：Nakayama引理的拓扑应用
- Krull定理：Nakayama引理的推论

## 参考

### 教材

- Atiyah, M.F. & Macdonald, I.G. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 2
- Matsumura, H. Commutative Ring Theory. Cambridge, 1986. Chapter 2

### 论文

- Nakayama, T. A remark on finitely generated modules. Nagoya Math. J., 3: 139-140, 1951.
- Azumaya, G. On maximally central algebras. Nagoya Math. J., 2: 119-150, 1951.

### 在线资源

- [Nakayama's Lemma Wikipedia](https://en.wikipedia.org/wiki/Nakayama%27s_lemma)
- [Stacks Project - Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
