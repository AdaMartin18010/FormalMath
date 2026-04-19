---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Schur引理 (Schur's Lemma)
---
# Schur引理 (Schur's Lemma)

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Module.SimpleModule

namespace SchurLemma

variable {R : Type*} [Ring R] {M N : Type*}
variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Schur引理：单模之间的非零同态是同构 -/
theorem schur_lemma [IsSimpleModule R M] [IsSimpleModule R N]
    {f : M →ₗ[R] N} (hf : f ≠ 0) : Function.Bijective f := by
  constructor
  · -- 单射性
    have hker : LinearMap.ker f = ⊥ ∨ LinearMap.ker f = ⊤ :=
      (IsSimpleModule.eq_bot_or_eq_top (LinearMap.ker f))
    cases hker with
    | inl h =>
      rw [LinearMap.ker_eq_bot] at h
      exact h
    | inr h =>
      rw [LinearMap.ker_eq_top] at h
      have : f = 0 := by ext x; exact h x
      contradiction
  · -- 满射性
    have him : LinearMap.range f = ⊥ ∨ LinearMap.range f = ⊤ :=
      (IsSimpleModule.eq_bot_or_eq_top (LinearMap.range f))
    cases him with
    | inl h =>
      have : f = 0 := by
        ext x
        have : f x ∈ LinearMap.range f := by use x
        rw [h] at this
        exact this
      contradiction
    | inr h =>
      rw [LinearMap.range_eq_top]
      exact h

/-- Schur引理（自同态环是除环）-/
theorem schur_lemma_divisionRing [IsSimpleModule R M] :
    IsDivisionRing (Module.End R M) := by
  constructor
  · -- 非零元可逆
    intro f hf
    have hbij := schur_lemma (by simpa using hf)
    exact ⟨LinearEquiv.ofBijective f hbij, by simp⟩

end SchurLemma
```

## 数学背景

Schur引理由Issai Schur在1905年证明，是表示论和模论中最基本的结果之一。该引理揭示了单模（不可约表示）之间同态的刚性：它们要么为零，要么为同构。这一结果对理解群的不可约表示结构至关重要，也是证明表示完全可约性（Maschke定理）的关键工具。

## 直观解释

Schur引理告诉我们：**单模之间的映射要么为零，要么是同构**。

想象单模是不可再分解的"基本粒子"。Schur引理说，不同种类的基本粒子之间没有非平凡的"相互作用"（同态为零），而同一种粒子之间的"自相互作用"都是可逆的（同构）。这反映了单模作为"原子"的结构刚性——它们不能被非平凡地映射到其他单模。

## 形式化表述

模 $M$ 称为**单模**（或不可约），如果 $M \neq 0$ 且只有 $\{0\}$ 和 $M$ 两个子模。

**Schur引理**：

1. **基本形式**：若 $M, N$ 是单 $R$-模，$f: M \to N$ 是非零模同态，则 $f$ 是同构
2. **自同态环**：单模的自同态环 $\text{End}_R(M)$ 是除环
3. **代数闭域情形**：若 $R = k$ 是代数闭域且 $M$ 有限维，则 $\text{End}_k(M) = k$（由标量乘法）

## 证明思路

1. **核的极大性**：$\ker f$ 是 $M$ 的子模，由单性知 $\ker f = 0$ 或 $\ker f = M$
2. **非零条件**：$f \neq 0$ 意味着 $\ker f \neq M$，故 $\ker f = 0$，$f$ 单
3. **像的极小性**：$\text{im } f$ 是 $N$ 的子模，由单性知 $\text{im } f = 0$ 或 $\text{im } f = N$
4. **满射性**：$f \neq 0$ 意味着 $\text{im } f \neq 0$，故 $\text{im } f = N$，$f$ 满
5. **除环结构**：非零自同态都可逆

核心洞察是单模子模的"二值性"强制同态的单/满性质。

## 示例

### 示例 1：不可约表示

设 $G$ 是有限群，$\rho: G \to GL(V)$ 是不可约复表示。

Schur引理说：与所有 $\rho(g)$ 交换的线性映射必为标量乘法。

这是量子力学中关于可观测量的基本结果。

### 示例 2：单群模

设 $M$ 是单 $\mathbb{Z}$-模，则 $M \cong \mathbb{Z}/p\mathbb{Z}$（$p$ 素数）。

$\text{End}_\mathbb{Z}(\mathbb{Z}/p\mathbb{Z}) \cong \mathbb{Z}/p\mathbb{Z}$（域）。

### 示例 3：矩阵形式

设 $M$ 是单 $k$-向量空间，$\dim M = 1$。

$\text{End}_k(M) \cong k$，Schur引理显然成立。

对更高维数，Schur引理要求寻找与表示交换的矩阵。

## 应用

- **表示论**：不可约表示的分类
- **量子力学**：角动量算符的对易关系
- **同调代数**：Ext^1(M,N) 的计算
- **李代数**：Casimir算符的性质
- **代数几何**：凝聚层的性质

## 相关概念

- 单模 (Simple Module)：无真非零子模的模
- 半单模 (Semisimple Module)：单模的直和
- [Maschke定理 (Maschke's Theorem)](./maschke-theorem.md)：表示的完全可约性
- 除环 (Division Ring)：非零元可逆的环
- 表示论 (Representation Theory)：群作用的线性化

## 参考

### 教材

- [Serre. Linear Representations of Finite Groups. Springer, 1977. Chapter 2]
- [Fulton & Harris. Representation Theory. Springer, 1991. Chapter 1]

### 历史文献

- [Schur. Neue Begründung der Theorie der Gruppencharaktere. 1905]

### 在线资源

- [Mathlib4 文档 - SimpleModule][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/SimpleModule.html](需更新)
- [Groupprops - Schur's lemma][https://groupprops.subwiki.org/wiki/Schur%27s_lemma](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
