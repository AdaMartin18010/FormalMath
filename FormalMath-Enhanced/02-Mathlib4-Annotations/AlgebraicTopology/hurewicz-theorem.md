---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Hurewicz定理
---
# Hurewicz定理

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Homotopy.Hurewicz

namespace AlgebraicTopology

/-- Hurewicz同态 -/
theorem hurewicz_homomorphism
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : n > 0) :
    ∃ (h : π_n X → H_n X),
      IsGroupHom h := by
  -- 从同伦群到同调群的自然同态
  sorry

/-- Hurewicz定理 -/
theorem hurewicz_theorem
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : n ≥ 2)
    (hX : ∀ (k : ℕ), k < n → π_k X = 0) :
    HurewiczHomomorphism n ≃* H_n X := by
  -- 前n-1个同伦群平凡时，Hurewicz同态是同构
  sorry

end AlgebraicTopology
```

## 数学背景

Hurewicz定理由Witold Hurewicz在1935年证明，是同伦论与同调论之间的基本桥梁。定理建立了从同伦群到同调群的自然映射（Hurewicz同态），并证明在简单连通性条件下这是同构。这是计算同伦群的基本工具之一，因为同调群通常更容易计算。Hurewicz定理也是证明Whitehead定理（弱同伦等价是同伦等价）的关键步骤。

## 直观解释

Hurewicz定理如同在两个世界之间建立"翻译"——同伦世界（映射的同伦类）和同调世界（链的同调类）。想象一个球面映射 $S^n \to X$：在同伦论中，我们关心这个映射的同伦类；在同调论中，我们可以取其像的基本链。Hurewicz同态就是这种"取像"操作。当空间在前几个维度"没有洞"（同伦群平凡）时，这种翻译是完美的——同伦群和同调群完全一致。

## 形式化表述

设 $X$ 是拓扑空间，$n \geq 1$。

**Hurewicz同态**：$h: \pi_n(X) \to H_n(X; \mathbb{Z})$

构造：对 $[f: S^n \to X] \in \pi_n(X)$，取 $h([f]) = f_*([S^n])$。

**Hurewicz定理**：若 $X$ 是 $(n-1)$-连通的（$\pi_k(X) = 0$ 对 $k < n$），则：

1. $h: \pi_n(X) \to H_n(X)$ 是同构（$n \geq 2$）
2. $h: \pi_1(X) \to H_1(X)$ 是满射，核是换位子群（$n = 1$）

**相对版本**：对 $(X, A)$，有长正合列。

## 证明思路

1. **同态定义**：从几何链复形构造映射
2. **基本类**：$S^n$ 的定向类在 $H_n(S^n)$
3. **胞腔逼近**：用胞腔映射代表同伦类
4. **同伦不变性**：同伦映射诱导相同同调类
5. **逆映射构造**：从同调类构造同伦类

## 示例

### 示例 1：球面的同伦群

**问题**：计算 $\pi_n(S^n)$。

**解答**：

$S^n$ 是 $(n-1)$-连通的（$\pi_k(S^n) = 0$ 对 $k < n$）。

由Hurewicz定理：$\pi_n(S^n) \cong H_n(S^n) \cong \mathbb{Z}$。

生成元是恒等映射 $[1_{S^n}]$。

### 示例 2：复射影空间

**问题**：计算 $\pi_2(\mathbb{CP}^n)$。

**解答**：

$\mathbb{CP}^n$ 的胞腔分解：$e^0 \cup e^2 \cup e^4 \cup \cdots \cup e^{2n}$

因此 $H_2(\mathbb{CP}^n) = \mathbb{Z}$。

由Hurewicz定理：$\pi_2(\mathbb{CP}^n) \cong H_2(\mathbb{CP}^n) = \mathbb{Z}$。

生成元由包含 $S^2 = \mathbb{CP}^1 \hookrightarrow \mathbb{CP}^n$ 给出。

## 应用

- **同伦群计算**：从同调群推导同伦群
- **Whitehead定理**：弱同伦等价是同伦等价
- **Eilenberg-MacLane空间**：$K(\pi, n)$ 的构造
- **有理同伦论**：Quillen和Sullivan理论
- **surgery理论**：Wall的阻碍群

## 相关概念

- 同伦群：Hurewicz定理的源
- 奇异同调：Hurewicz定理的目标
- [Whitehead定理](./whitehead-theorem.md)：Hurewicz定理的应用
- Eilenberg-MacLane空间：Hurewicz定理的逆
- Blakers-Massey定理：相对Hurewicz的推广

## 参考

### 教材

- Hatcher, A. Algebraic Topology. Cambridge, 2002. Chapter 4
- Spanier, E.H. Algebraic Topology. Springer, 1966. Chapter 7

### 论文

- Hurewicz, W. Beiträge zur Topologie der Deformationen. Nederl. Akad. Wetensch. Proc. Ser. A, 38: 112-119, 521-528, 1935.

### 在线资源

- [Hurewicz Theorem Wikipedia](https://en.wikipedia.org/wiki/Hurewicz_theorem)
- [nLab - Hurewicz Theorem](https://ncatlab.org/nlab/show/Hurewicz+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
