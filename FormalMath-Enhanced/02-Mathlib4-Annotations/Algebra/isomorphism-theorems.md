---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 同构定理 (Isomorphism Theorems)
---
# 同构定理 (Isomorphism Theorems)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

namespace IsomorphismTheorems

variable {G H : Type*} [Group G] [Group H]

/-- 第一同构定理 -/
theorem first_isomorphism (f : G →* H) :
    G ⧸ (ker f) ≅* (range f) := by
  exact QuotientGroup.quotientKerEquivRange f

/-- 第二同构定理（钻石同构）-/
theorem second_isomorphism {H N : Subgroup G} [N.Normal] (hH : H ≤ G) :
    H ⧸ (H ⊓ N) ≅* (H ⊔ N) ⧸ N := by
  -- 对应定理的应用
  sorry

/-- 第三同构定理 -/
theorem third_isomorphism {M N : Subgroup G} [M.Normal] [N.Normal] (hMN : N ≤ M) :
    (G ⧸ N) ⧸ (M ⧸ N) ≅* G ⧸ M := by
  -- 商群的商
  sorry

end IsomorphismTheorems
```

## 数学背景

群同构定理（第一、第二、第三同构定理）是群论的基础结构定理，其历史可以追溯到群论创立时期（Camille Jordan, Otto Hölder等19世纪末数学家）。这些定理揭示了商群构造与子群格之间的深刻关系，是理解群结构的必要工具。它们不仅适用于群论，在线性代数（向量空间商）、环论（理想商）和模论中也有直接类比，构成了整个抽象代数的通用语言。同构定理的证明虽然技巧性不高，但其思想——通过同态核来"约化"代数结构——是代数学最核心的方法论之一。

### 同态、核与像

**定义（群同态）**：设 $G, H$ 是群。映射 $f: G \to H$ 称为**同态**（homomorphism），如果对任意 $a, b \in G$：

$$f(ab) = f(a)f(b)$$

**定义（核与像）**：同态 $f: G \to H$ 的**核**（kernel）和**像**（image）定义为：

$$\ker(f) = \{g \in G : f(g) = e_H\}$$
$$\text{im}(f) = \{f(g) : g \in G\}$$

**基本性质**：$\ker(f) \trianglelefteq G$（核总是正规子群），$\text{im}(f) \leq H$（像是子群）。

### 商群

**定义（商群）**：若 $N \trianglelefteq G$，则陪集集合 $G/N = \{gN : g \in G\}$ 在运算 $(aN)(bN) = (ab)N$ 下构成群，称为 $G$ 关于 $N$ 的**商群**。

## 同构定理的陈述与证明

### 第一同构定理

**定理（第一同构定理）**：设 $f: G \to H$ 是群同态。则：

$$G/\ker(f) \cong \text{im}(f)$$

具体地，映射 $\bar{f}: G/\ker(f) \to \text{im}(f)$，$\bar{f}(g \cdot \ker(f)) = f(g)$ 是群同构。

**证明**：

**良定义性**：若 $g_1 \ker(f) = g_2 \ker(f)$，则 $g_1^{-1}g_2 \in \ker(f)$，$f(g_1^{-1}g_2) = e$，$f(g_1) = f(g_2)$。故 $\bar{f}$ 良定义。

**同态性**：$\bar{f}((g_1 \ker)(g_2 \ker)) = \bar{f}(g_1 g_2 \ker) = f(g_1 g_2) = f(g_1)f(g_2) = \bar{f}(g_1 \ker)\bar{f}(g_2 \ker)$。

**满射**：对 $h \in \text{im}(f)$，$h = f(g)$ 对某个 $g \in G$，$\bar{f}(g \ker) = h$。

**单射**：若 $\bar{f}(g \ker) = e$，则 $f(g) = e$，$g \in \ker(f)$，$g \ker = \ker$。故 $\ker(\bar{f}) = \{\ker(f)\}$ 是平凡子群，$\bar{f}$ 单射。 $\square$

### 第二同构定理（钻石同构定理）

**定理（第二同构定理）**：设 $G$ 是群，$H \leq G$ 是子群，$N \trianglelefteq G$ 是正规子群。则：

1. $HN = \{hn : h \in H, n \in N\}$ 是 $G$ 的子群；
2. $H \cap N \trianglelefteq H$；
3. $HN/N \cong H/(H \cap N)$。

**证明**：

$HN$ 是子群：$(h_1 n_1)(h_2 n_2) = h_1 h_2 (h_2^{-1} n_1 h_2) n_2 \in HN$（因为 $N$ 正规，$h_2^{-1}n_1h_2 \in N$）。

$H \cap N \trianglelefteq H$：若 $x \in H \cap N$，$h \in H$，则 $hxh^{-1} \in H$（因为 $H$ 是子群）且 $hxh^{-1} \in N$（因为 $N$ 正规），故 $hxh^{-1} \in H \cap N$。

构造同态 $f: H \to HN/N$，$f(h) = hN$。
- $f$ 是满射：$hnN = hN = f(h)$。
- $\ker(f) = \{h \in H : hN = N\} = \{h \in H : h \in N\} = H \cap N$。

由第一同构定理，$H/\ker(f) = H/(H \cap N) \cong \text{im}(f) = HN/N$。 $\square$

### 第三同构定理

**定理（第三同构定理）**：设 $G$ 是群，$M, N \trianglelefteq G$，且 $N \leq M$。则 $M/N \trianglelefteq G/N$，且：

$$(G/N)/(M/N) \cong G/M$$

**证明**：

$M/N \trianglelefteq G/N$：对 $gN \in G/N$，$mN \in M/N$，$(gN)(mN)(gN)^{-1} = gmg^{-1}N \in M/N$（因为 $M$ 正规）。

构造同态 $f: G/N \to G/M$，$f(gN) = gM$。
- **良定义性**：若 $g_1 N = g_2 N$，则 $g_1^{-1}g_2 \in N \leq M$，$g_1 M = g_2 M$。
- **同态性**：$f((g_1 N)(g_2 N)) = f(g_1 g_2 N) = g_1 g_2 M = (g_1 M)(g_2 M) = f(g_1 N)f(g_2 N)$。
- **满射**：显然。
- **核**：$\ker(f) = \{gN : gM = M\} = \{gN : g \in M\} = M/N$。

由第一同构定理，$(G/N)/\ker(f) = (G/N)/(M/N) \cong \text{im}(f) = G/M$。 $\square$

## 例子

### 例子1：整数到循环群的投影

设 $f: \mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$，$f(k) = k \bmod n$。则：
- $\ker(f) = n\mathbb{Z}$
- $\text{im}(f) = \mathbb{Z}/n\mathbb{Z}$

由第一同构定理：$\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/n\mathbb{Z}$（恒真，但验证了定理）。

### 例子2： sign 同态

设 $f: S_n \to \{\pm 1\}$ 是符号同态。则：
- $\ker(f) = A_n$（交错群）
- $\text{im}(f) = \{\pm 1\}$

第一同构定理：$S_n/A_n \cong \{\pm 1\} \cong \mathbb{Z}/2\mathbb{Z}$。

### 例子3：第二同构定理的几何例子

设 $G = \mathbb{R}^2$（加法群），$H = \{(x, 0) : x \in \mathbb{R}\} \cong \mathbb{R}$（x轴），$N = \{(0, y) : y \in \mathbb{R}\} \cong \mathbb{R}$（y轴）。

$N \trianglelefteq G$（Abel群的所有子群都正规）。

$HN = \mathbb{R}^2$（整个平面）。$H \cap N = \{(0,0)\}$。

第二同构定理：$H/(H \cap N) = H/\{0\} \cong H \cong \mathbb{R}$，而 $HN/N = \mathbb{R}^2/N \cong \mathbb{R}$。确实同构。

### 例子4：第三同构定理

设 $G = \mathbb{Z}$，$M = 6\mathbb{Z}$，$N = 12\mathbb{Z}$。$N \leq M$。

$G/N = \mathbb{Z}/12\mathbb{Z}$，$M/N = 6\mathbb{Z}/12\mathbb{Z} = \{\bar{0}, \bar{6}\} \cong \mathbb{Z}/2\mathbb{Z}$。

$(G/N)/(M/N) = (\mathbb{Z}/12\mathbb{Z})/(\{\bar{0}, \bar{6}\}) \cong \mathbb{Z}/6\mathbb{Z} = G/M$。

确实同构。

## 应用

### 1. 群的分解和合成

同构定理是理解群合成列（composition series）和可解群的基础。Jordan-Hölder定理利用同构定理证明任何有限群的两个合成列有相同的合成因子（在同构和重排意义下）。

### 2. 同调代数中的长正合列

在群同调、拓扑同调等理论中，短正合列 $1 \to N \to G \to G/N \to 1$ 诱导长正合列。同构定理帮助理解中间群的结构，以及商群与模结构之间的关系。

### 3. 格同构定理的基础

第一同构定理是更一般的对应定理的核心：对任意满同态 $f: G \to H$，$G$ 中包含 $\ker(f)$ 的子群与 $H$ 的子群之间存在一一对应。正规子群对应正规子群，且对应保持指数。

### 4. 环论与模论中的类比

同构定理在环论和模论中有直接类比：
- **环**：$R/I$ 的理想对应于 $R$ 中包含 $I$ 的理想；$(R/I)/(J/I) \cong R/J$。
- **模**：对 $R$-模同态 $f: M \to N$，$M/\ker(f) \cong \text{im}(f)$。

这些结果统一了抽象代数中"商构造"的理论框架。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
