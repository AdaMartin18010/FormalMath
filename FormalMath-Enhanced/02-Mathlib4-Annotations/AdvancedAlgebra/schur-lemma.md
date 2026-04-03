---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Schur引理

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.Basic

namespace RepresentationTheory

/-- Schur引理：不可约表示之间的同态 -/
theorem schur_lemma
    {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Simple V]
    [AddCommGroup W] [Module k W] [Simple W]
    (f : V →ₗ[k] W) [f.IsModuleHom] :
    f = 0 ∨ Function.Bijective f := by
  -- 核和像都是子模，由不可约性推出结论
  have h1 : f.ker = ⊤ ∨ f.ker = ⊥ := by
    apply Simple.eq_bot_or_eq_top
  have h2 : f.range = ⊤ ∨ f.range = ⊥ := by
    apply Simple.eq_bot_or_eq_top
  cases h1 with
  | inl h_ker_top =>
    left; ext x; simp [h_ker_top]
  | inr h_ker_bot =>
    cases h2 with
    | inl h_range_top =>
      right; constructor
      · -- 单射
        rwa [LinearMap.ker_eq_bot] at h_ker_bot
      · -- 满射
        rwa [LinearMap.range_eq_top] at h_range_top
    | inr h_range_bot =>
      left; ext x; simp [h_range_bot]

end RepresentationTheory
```

## 数学背景

Schur引理由德国数学家Issai Schur在1905年证明，是表示论中最基本且强大的工具之一。该引理揭示了一个简单但深刻的数学事实：不可约表示之间的同态只能是零映射或同构。这一结果不仅在表示论中无处不在，也在代数几何、调和分析等领域有重要应用。

## 直观解释

Schur引理的核心思想是"简单对简单"：不可约表示作为"原子"式的数学对象，它们之间的映射具有极端的性质。想象两个不可约表示为两个不可分割的整体，任何连接它们的"桥梁"（同态）要么完全断开（零映射），要么建立完美的一一对应（同构）。不存在"部分连接"的可能性。

## 形式化表述

**Schur引理（代数版本）**：设 $M, N$ 是环 $R$ 上的单模，则任何 $R$-模同态 $f: M \to N$ 要么是零，要么是同构。

**Schur引理（表示论版本）**：设 $V, W$ 是群 $G$ 的不可约表示，则任何 $G$-等变线性映射 $f: V \to W$ 要么是零，要么是同构。

**推论**：若 $V$ 是不可约表示，则 $\text{End}_{k[G]}(V)$ 是除环。当 $k$ 代数闭时，这是 $k$ 本身。

## 证明思路

1. **考虑核**：$\ker(f)$ 是 $V$ 的子表示，由不可约性，$\ker(f) = 0$ 或 $V$
2. **考虑像**：$\text{im}(f)$ 是 $W$ 的子表示，由不可约性，$\text{im}(f) = 0$ 或 $W$
3. **分类讨论**：
   - 若 $\ker(f) = V$，则 $f = 0$
   - 若 $\ker(f) = 0$ 且 $\text{im}(f) = W$，则 $f$ 是双射

## 示例

### 示例 1：阿贝尔群的表示

**问题**：证明阿贝尔群 $G$ 在代数闭域上的不可约表示都是一维的。

**解答**：

设 $\rho: G \to GL(V)$ 是不可约表示。对任意 $g \in G$，$\rho(g)$ 是 $G$-等变的（因为 $G$ 阿贝尔）。

由Schur引理，$\rho(g) = \lambda_g \cdot I$。因此每个子空间都是不变的，不可约性要求 $\dim V = 1$。

### 示例 2：不可约表示的自同态

**问题**：设 $V$ 是 $S_3$ 在 $\mathbb{C}$ 上的标准表示，求 $\text{End}_{\mathbb{C}[S_3]}(V)$。

**解答**：

由于 $\mathbb{C}$ 代数闭，且 $V$ 不可约，由Schur引理推论：
$$\text{End}_{\mathbb{C}[S_3]}(V) \cong \mathbb{C}$$

这意味着任何 $S_3$-等变自同态都是标量乘法。

## 应用

- **特征标正交性**：Schur引理是其证明的核心
- **表示的分类**：确定不可约表示的重数
- **量子力学**：角动量算符的对易关系
- **代数几何**：凝聚层的性质研究
- **调和分析**：不可约酉表示的分类

## 相关概念

- [Maschke定理](./maschke-theorem.md)：表示的完全可约性
- [特征标正交性](./character-orthogonality.md)：依赖Schur引理
- [Jacobson密度定理](./jacobson-density.md)：Schur引理的推广
- [Brauer群](./brauer-group.md)：中心单代数的分类
- [Morita等价](./morita-equivalence.md)：基于Schur引理的等价理论

## 参考

### 教材

- Lang, S. Algebra. Springer, 2002. Chapter XVII
- Etingof, P. et al. Introduction to Representation Theory. AMS, 2011. Chapter 2

### 论文

- Schur, I. Neue Begründung der Theorie der Gruppencharaktere. Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften, 406-432, 1905.

### 在线资源

- [Schur's Lemma Wikipedia](https://en.wikipedia.org/wiki/Schur%27s_lemma)
- [nLab - Schur's Lemma](https://ncatlab.org/nlab/show/Schur%27s+lemma)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
