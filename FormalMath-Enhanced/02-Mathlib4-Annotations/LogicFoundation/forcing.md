---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 力迫法基本定理
---
# 力迫法基本定理

## Mathlib4 引用

```lean
import Mathlib.SetTheory.Forcing.Basic

namespace SetTheory

/-- 力迫关系 -/
theorem forcing_relation
    {M : Type*} [Model ZFC M]
    (ℙ : Type*) [PartialOrder ℙ] [MGeneric ℙ]
    {φ : Formula L_ZFC} {p : ℙ} {τ₁ τ₂ : ℙ.Name} :
    p ⊩ φ[τ₁, τ₂] ↔
      ∀ (G : GenericFilter ℙ),
        p ∈ G → M[G] ⊨ φ[τ₁^G, τ₂^G] := by
  -- 力迫关系定义
  sorry

/-- 力迫定理 -/
theorem forcing_theorem
    {M : Type*} [Model ZFC M]
    (ℙ : Type*) [PartialOrder ℙ] [MGeneric ℙ]
    {φ : Formula L_ZFC} {τ₁ τ₂ : ℙ.Name} :
    M[G] ⊨ φ[τ₁^G, τ₂^G] ↔
      ∃ (p ∈ G), p ⊩ φ[τ₁, τ₂] := by
  -- 泛型扩张中的真值与力迫关系
  sorry

end SetTheory
```

## 数学背景

力迫法（Forcing）由Paul Cohen在1963年发明，用于证明连续统假设（CH）和选择公理（AC）独立于ZFC公理系统。这是集合论历史上最革命性的突破之一，Cohen因此获得Fields奖。力迫法通过构造集合论模型 $M$ 的泛型扩张 $M[G]$，在其中添加新的集合 $G$（"泛型对象"），从而控制新模型的性质。力迫法已成为现代集合论的核心工具，用于研究大基数、描述集合论和内模型理论。

## 直观解释

力迫法如同"向宇宙中注入新信息"。想象一个集合论模型 $M$ 如同一个"数学宇宙"，其中某些命题既不能被证明也不能被否定（如CH）。力迫法通过添加一个"泛型"对象 $G$（类似于超越数超越代数数的方式），构造一个更大的宇宙 $M[G]$。在这个新宇宙中，我们可以控制CH的真值——通过精心设计偏序集 $\mathbb{P}$，可以使CH在新宇宙中为真或为假。"力迫"关系 $p \Vdash \varphi$ 表示"条件 $p$ 强制命题 $\varphi$ 在新宇宙中为真"。

## 形式化表述

设 $M$ 是ZFC的可数传递模型，$\mathbb{P} \in M$ 是偏序集（"力迫概念"）。

**力迫语言**：$\mathbb{P}$-名（$\mathbb{P}$-name）是 $M$ 中描述 $M[G]$ 中对象的形式记号。

**泛型滤子**：滤子 $G \subseteq \mathbb{P}$ 是**$M$-泛型**的，若它与 $M$ 中所有稠密集相交。

**泛型扩张**：$M[G] = \{\tau^G : \tau \in M^{\mathbb{P}}\}$，其中 $\tau^G$ 是 $\tau$ 的解释。

**力迫定理**：$M[G] \vDash \varphi$ 当且仅当存在 $p \in G$ 使得 $p \Vdash \varphi$。

**独立性结果**：若 $M \vDash ZFC$，则 $M[G] \vDash ZFC + \neg CH$（适当选择 $\mathbb{P}$）。

## 证明思路

1. **可数模型**：取ZFC的可数传递模型 $M$
2. **偏序构造**：设计 $\mathbb{P}$ 控制新对象的性质
3. **泛型存在性**：证明 $M$-泛型滤子存在（在 $V$ 中）
4. **力迫定义**：递归定义力迫关系
5. **真值引理**：验证力迫定理
6. **独立性**：通过不同 $\mathbb{P}$ 得到不同结论

## 示例

### 示例 1：添加Cohen实数

**问题**：用力迫法向 $M$ 添加新的实数。

**解答**：

Cohen力迫：$\mathbb{P} = \text{Fn}(\omega \times \omega, 2)$（有限部分函数）。

泛型滤子 $G$ 对应新实数 $c: \omega \to 2$，即二进制展开。

在 $M[G]$ 中，$c$ 不在 $M$ 中（"Cohen实数"）。

### 示例 2：连续统假设的否定

**问题**：构造ZFC + $\neg$CH 的模型。

**解答**：

设 $\kappa$ 是 $M$ 中的不可数基数（如 $\aleph_2^M$）。

令 $\mathbb{P} = \text{Fn}(\kappa \times \omega, 2)$。

在 $M[G]$ 中，$2^{\aleph_0} \geq \kappa$，因此CH不成立。

通过链条件，基数保持，故 $M[G] \vDash 2^{\aleph_0} = \kappa$。

## 应用

- **独立性证明**：CH、AC、Suslin假设等
- **大基数**：可测基数与力迫的关系
- **描述集合论**：射影分层的研究
- **内模型理论**：迭代力迫和核心模型
- **拓扑学**：集合论拓扑的反例构造

## 相关概念

- ZFC公理系统：力迫法的理论基础
- 模型论：力迫法的逻辑框架
- 偏序集：力迫概念的结构
- 布尔值模型：力迫的另一种表述
- 迭代力迫：复杂独立性证明

## 参考

### 教材

- Kunen, K. Set Theory. College Publications, 2011.
- Jech, T. Set Theory. Springer, 2003. Chapter 15

### 论文

- Cohen, P.J. The independence of the Continuum Hypothesis I, II. Proc. Nat. Acad. Sci. USA, 50: 1143-1148, 1963; 51: 105-110, 1964.
- Shoenfield, J.R. Unramified forcing. Axiomatic Set Theory, AMS, 1971.

### 在线资源

- [Forcing (Mathematics) Wikipedia](https://en.wikipedia.org/wiki/Forcing_(mathematics))
- [nLab - Forcing](https://ncatlab.org/nlab/show/forcing)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
