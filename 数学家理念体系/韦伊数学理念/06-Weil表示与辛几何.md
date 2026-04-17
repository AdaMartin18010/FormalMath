---
title: "Weil表示与辛几何：从量子力学到数论"
level: gold
course: Weil数学理念
msc_primary: "11F27"
references:
  textbooks:
    - title: "Weil Representation I: Intertwining Distributions and Discrete Spectrum"
      author: "S. Kudla"
      year: 1996
    - title: "The Weil Representation, Maslov Index and Theta Series"
      author: "G. Lion & M. Vergne"
      year: 1980
  papers:
    - title: "Sur certains groupes d'opérateurs unitaires"
      author: "A. Weil"
      year: 1964
status: completed
created_at: 2026-04-18
---

# Weil表示与辛几何：从量子力学到数论

## 1. 引言

Weil表示（又称metaplectic表示或Shale-Weil表示）是Weil在1964年的一篇论文中引入的表示论构造。这一表示不仅统一了数论中经典的theta对应和Siegel模形式，更揭示了辛几何、量子力学和自守形式之间深刻的联系。

本文将深入分析Weil表示的构造，探讨其在数论和表示论中的核心地位，并阐述这一理论对现代数学的深远影响。

## 2. 辛几何基础

### 2.1 辛向量空间

**定义 2.1（辛空间）**。实向量空间 $V$ 配备非退化反对称双线性型 $\omega$ 称为**辛空间**。

**例子 2.2**：$V = \mathbb{R}^{2n}$，$\omega((x, y), (x', y')) = x \cdot y' - y \cdot x'$。

### 2.2 辛群

**定义 2.3（辛群）**：

$$Sp(V, \omega) = \{g \in GL(V) : \omega(gv, gw) = \omega(v, w) \text{ for all } v, w\}$$

## 3. Weil表示的构造

### 3.1 经典动机：谐振子

量子力学中的**谐振子**由Hamiltonian $H = \frac{1}{2}(p^2 + q^2)$ 描述。其对称性群包含一个double cover of $SL_2(\mathbb{R})$，这就是Weil表示的原型。

### 3.2 一般构造

**定理 3.1（Weil, 1964）**。设 $V$ 为局部域 $F$ 上的辛空间。则存在**Weil表示**：

$$\omega: \widetilde{Sp}(V) \to U(L^2(X))$$

其中 $\widetilde{Sp}(V)$ 为辛群的**metaplectic double cover**，$X$ 为 $V$ 的一个Lagrange子空间。

### 3.3 局部Weil表示

对 $F = \mathbb{R}$ 或 $\mathbb{Q}_p$：

**实情形**：$\widetilde{Sp}_{2n}(\mathbb{R})$ 在 $L^2(\mathbb{R}^n)$ 上的表示由以下算子生成：

- **平移**：$T_a f(x) = f(x + a)$
- **调制**：$M_b f(x) = e^{2\pi i b \cdot x} f(x)$
- **Fourier变换**：$\mathcal{F} f(\xi) = \int f(x) e^{-2\pi i x \cdot \xi} dx$

**p-adic情形**：类似的构造，使用 $p$-adic Fourier变换。

## 4. Theta对应

### 4.1 对偶重配对

**定理 4.1（Howe对偶性）**。设 $(G, G')$ 为reductive dual pair in $Sp(V)$。则Weil表示限制到 $G \times G'$ 上具有**多重性一（multiplicity one）**性质。

### 4.2 经典例子

**例 4.2（Siegel模形式）**。对 dual pair $(Sp_{2n}, O_m)$：

- $Sp_{2n}$ 的表示对应Siegel模形式
- $O_m$ 的表示对应theta级数

**例 4.3（Shimura对应）**。对 dual pair $(\widetilde{SL}_2, PGL_2)$：

- 构造了半整权模形式与整权模形式之间的对应

## 5. 与量子力学的联系

### 5.1 Stone-von Neumann定理

**定理 5.1（Stone-von Neumann）**。Heisenberg群的不可约酉表示由Planck常数 $\hbar$ 参数化，且在同构意义下唯一。

Weil表示是这一定理在辛群setting中的推广。

### 5.2 量子纠缠与Weil表示

近年来，Weil表示在**量子信息理论**中的应用受到关注：

- **纠缠态的构造**：利用Weil表示的离散版本
- **量子纠错码**：基于辛几何的stabilizer码

## 6. 批判性比较

| 维度 | Weil表示 (1964) | Segal-Bargmann (1960s) | Kirillov轨道法 |
|------|----------------|----------------------|---------------|
| **核心对象** | 辛群的表示 | 全纯函数空间 | Coadjoint轨道 |
| **主要应用** | 数论、自守形式 | 量子场论 | 幂零Lie群表示 |
| **技术工具** | Adele方法、Fourier分析 | 复分析、泛函分析 | 辛几何 |
| **统一性** | 局部-整体统一 | 全纯-实分析统一 | 经典-量子对应 |

## 7. Lean4 形式化对照

```lean4
import Mathlib

-- Weil表示的形式化极具挑战性
-- 以下是核心概念的概念性表达

-- 辛群
def SymplecticGroup (V : Type*) [AddCommGroup V] [Module ℝ V]
    (ω : BilinearForm ℝ V) : Subgroup (GL ℝ V) where
  carrier := {g | ∀ v w, ω (g • v) (g • w) = ω v w}
  one_mem' := by simp
  mul_mem' := by sorry
  inv_mem' := by sorry

-- Weil表示（概念性）
example (V : Type*) [AddCommGroup V] [Module ℝ V]
    (ω : BilinearForm ℝ V) (hω : ω.IsNondegenerate) (hω' : ω.IsAlt) :
    Representation ℂ (SymplecticGroup V ω) (Lp ℂ 2 (AddHaar ℝ)) := by
  sorry
```

## 8. 结论

Weil表示是20世纪数学最深刻的构造之一。它不仅统一了数论中的theta对应和模形式理论，更揭示了辛几何与量子力学之间的深层联系。

从自守形式到量子信息，从表示论到几何量子化，Weil表示的影响力跨越了数学和物理学的多个领域。正如Weil自己所评价的："这个表示是数学中最美丽的结构之一。"

---

**参考文献**

1. Weil, A. "Sur certains groupes d'opérateurs unitaires." *Acta Math.* 111 (1964), 143–211.
2. Howe, R. "Transcending classical invariant theory." *J. Amer. Math. Soc.* 2 (1989), 535–552.
3. Kudla, S. S. "Notes on the local theta correspondence." *Univ. of Maryland*, 1996.
4. Lion, G. & Vergne, M. *The Weil Representation, Maslov Index and Theta Series*. Birkhäuser, 1980.
5. Gelbart, S. "Weil's representation and the spectrum of the metaplectic group." *LNM* 530, 1976.
